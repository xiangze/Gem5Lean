#!/usr/bin/env python3
"""sc2lean — 制約付き SystemC/TLM-2.0 (LT) モジュールを Lean 4 のイベント駆動モデルへ変換する。

libclang で C++ を構文解析し、TOML のルール表に従って AST を Lean に写す。
ルールで扱えない記述に出会うと Unsupported 例外（ソース位置つき）を投げる。

対応する書き方（これ以外は例外）:
  * SC_MODULE / sc_module 派生クラス、SC_CTOR
  * フィールド: ルールで型が決まるスカラ、その固定長配列、sc_event、
    simple_target_socket、simple_initiator_socket
  * SC_THREAD: [前置きの文] + while(true){...}（または for(;;)）。wait(...) と
    socket->b_transport(...) は本体の最上位の文としてだけ書ける
  * SC_METHOD + sensitive << ev。next_trigger は不可
  * register_b_transport で登録したターゲット側 b_transport（内部で wait は不可）
  * 値を返し状態を書き換えないヘルパメソッド

生成物: モジュールごとの namespace に
  St（状態）, Msg（入出力メッセージ）, init, initEvents, step : St → Msg → St × List (Nat × Msg)
時間は ps 単位の Nat。step が返すリストは（遅延, メッセージ）。
"""
from __future__ import annotations

import argparse
import os
import re
import sys

try:  # Python 3.11+
    import tomllib as _toml_bin
except ModuleNotFoundError:  # 3.10 以前: pip install tomli（tomllib と同じ API）
    try:
        import tomli as _toml_bin
    except ModuleNotFoundError:
        _toml_bin = None
from dataclasses import dataclass, field
from pathlib import Path

import clang.cindex as ci
from clang.cindex import CursorKind as K

HERE = Path(__file__).resolve().parent

# --------------------------------------------------------------------------- 例外


class Unsupported(Exception):
    """想定外の記述。ソース位置と該当行を持つ。"""

    def __init__(self, msg: str, cursor: ci.Cursor | None = None):
        self.msg = msg
        self.loc = ""
        self.line = ""
        if cursor is not None and cursor.location.file is not None:
            f = cursor.location.file.name
            self.loc = f"{f}:{cursor.location.line}:{cursor.location.column}"
            try:
                self.line = Path(f).read_text(errors="replace").splitlines()[cursor.location.line - 1]
            except (OSError, IndexError):
                pass
        super().__init__(self.format())

    def format(self) -> str:
        s = f"{self.loc}: 未対応: {self.msg}" if self.loc else f"未対応: {self.msg}"
        if self.line:
            s += f"\n    | {self.line.strip()}"
        return s


class ParseError(Exception):
    pass


# --------------------------------------------------------------------------- ルール


def _merge(base: dict, extra: dict) -> dict:
    out = dict(base)
    for k, v in extra.items():
        if k in ("stmt_rules", "expr_rules"):
            out[k] = list(v) + list(out.get(k, []))  # 後から読んだルールを優先
        elif k == "lean" and isinstance(v, dict) and "extra" in v:
            merged = _merge(out.get("lean", {}), {kk: vv for kk, vv in v.items() if kk != "extra"})
            merged["extra"] = (out.get("lean", {}).get("extra", "") + "\n" + v["extra"]).strip("\n")
            out[k] = merged
        elif isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = _merge(out[k], v)
        else:
            out[k] = v
    return out


def load_toml(p: Path) -> dict:
    """tomllib / tomli はバイナリモード、toml パッケージはテキストモードで読む。"""
    if _toml_bin is not None:
        with open(p, "rb") as f:
            return _toml_bin.load(f)
    try:
        import toml
    except ModuleNotFoundError:
        raise SystemExit("sc2lean: TOML ライブラリがありません。pip install tomli（または toml）してください")
    with open(p, encoding="utf-8") as f:
        return toml.load(f)


@dataclass
class Rules:
    data: dict

    @classmethod
    def load(cls, paths: list[Path], use_default: bool = True) -> "Rules":
        data: dict = {}
        files = ([HERE / "rules" / "default.toml"] if use_default else []) + list(paths)
        for p in files:
            data = _merge(data, load_toml(Path(p)))
        r = cls(data)
        r._compile()
        return r

    def _compile(self):
        for key in ("stmt_rules", "expr_rules"):
            for rule in self.data.get(key, []):
                if "match" not in rule:
                    raise ValueError(f"{key} のルール {rule.get('name')} に match がありません")
                rule["_re"] = re.compile(rule["match"])

    def table(self, name: str) -> dict:
        cur = self.data
        for part in name.split("."):
            cur = cur.get(part, {})
        return cur

    @property
    def stmt_rules(self):
        return self.data.get("stmt_rules", [])

    @property
    def expr_rules(self):
        return self.data.get("expr_rules", [])


# --------------------------------------------------------------------------- 補助

LEAN_KEYWORDS = {
    "def", "end", "fun", "if", "then", "else", "do", "let", "mut", "match", "with",
    "return", "for", "in", "while", "break", "continue", "structure", "inductive",
    "namespace", "open", "where", "at", "from", "have", "show", "by", "deriving",
    "instance", "class", "import", "theorem", "example", "abbrev", "universe",
    "variable", "section", "macro", "syntax", "s", "out", "m", "r", "Type", "Prop",
}


def lean_id(name: str) -> str:
    return f"«{name}»" if name in LEAN_KEYWORDS else name


def qualname(c: ci.Cursor) -> str:
    parts = []
    while c is not None and c.kind != K.TRANSLATION_UNIT:
        if c.kind == K.ENUM_DECL and not c.is_scoped_enum():
            c = c.semantic_parent
            continue
        if c.spelling:
            parts.append(c.spelling)
        c = c.semantic_parent
    return "::".join(reversed(parts))


_WORDY = re.compile(r"\w")


def norm_text(c: ci.Cursor) -> str:
    """トークンを連結した正規化テキスト（識別子同士の間だけ空白 1 個）。"""
    out = ""
    prev = ""
    for t in c.get_tokens():
        s = t.spelling
        if prev and _WORDY.match(prev[-1]) and _WORDY.match(s[0]):
            out += " "
        out += s
        prev = s
    return out


def strip_wrappers(c: ci.Cursor) -> ci.Cursor:
    while c.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR):
        ch = list(c.get_children())
        if len(ch) != 1:
            break
        c = ch[0]
    return c


def ctype(t: ci.Type) -> ci.Type:
    if t.kind in (ci.TypeKind.LVALUEREFERENCE, ci.TypeKind.RVALUEREFERENCE):
        t = t.get_pointee()
    return t.get_canonical()


def type_key(t: ci.Type) -> str:
    s = ctype(t).spelling
    s = re.sub(r"\b(const|volatile)\b\s*", "", s).strip()
    return s


def op_spelling(c: ci.Cursor) -> str:
    """BINARY_OPERATOR / COMPOUND_ASSIGNMENT_OPERATOR の演算子トークン。"""
    ch = list(c.get_children())
    end = ch[0].extent.end.offset
    for t in c.get_tokens():
        if t.extent.start.offset >= end:
            return t.spelling
    raise Unsupported("演算子を特定できません", c)


def unary_op(c: ci.Cursor) -> tuple[str, bool]:
    toks = list(c.get_tokens())
    ch = list(c.get_children())[0]
    if toks and toks[0].extent.start.offset < ch.extent.start.offset:
        return toks[0].spelling, True
    return toks[-1].spelling, False


def int_literal(c: ci.Cursor) -> str:
    tok = next(c.get_tokens()).spelling
    tok = re.sub(r"[uUlL]+$", "", tok).replace("'", "")
    if re.fullmatch(r"0[0-7]+", tok):
        return str(int(tok, 8))
    return tok


def is_literal(c: ci.Cursor) -> bool:
    c = strip_wrappers(c)
    if c.kind in (K.INTEGER_LITERAL, K.CXX_BOOL_LITERAL_EXPR):
        return True
    if c.kind == K.UNARY_OPERATOR and unary_op(c)[0] == "-":
        return is_literal(list(c.get_children())[0])
    return False


def source_text(c: ci.Cursor) -> str:
    """コメント用のソース表記。マクロ展開されたものはトークンが取れないので行を使う。"""
    t = norm_text(c)
    if t:
        return t
    try:
        return Path(c.location.file.name).read_text(errors="replace").splitlines()[c.location.line - 1].strip()
    except (OSError, IndexError, AttributeError):
        return ""


def definition_of(decl: ci.Cursor) -> ci.Cursor:
    """メソッド宣言から本体つきの定義を探す（クラス外定義に対応）。同じ翻訳単位にないと例外。"""
    d = decl.get_definition()
    if d is None:
        raise Unsupported(f"{decl.spelling} の本体が見つかりません（実装の .cpp を入力に渡してください）", decl)
    return d


def indent(lines: list[str], n: int = 2) -> list[str]:
    return [" " * n + l for l in lines]


def call_receiver_and_args(c: ci.Cursor) -> tuple[ci.Cursor | None, list[ci.Cursor]]:
    """CALL_EXPR からレシーバと引数を取り出す。演算子オーバーロードは第 1 引数がレシーバ。"""
    ref = c.referenced
    args = list(c.get_arguments())
    if ref is not None and ref.spelling.startswith("operator") and ref.kind == K.CXX_METHOD:
        ch = list(c.get_children())
        if ch and (not args or ch[0] != args[0]):
            # libclang は CXXOperatorCallExpr の第 1 被演算子を get_arguments に含める場合と含めない場合がある
            if args and norm_text(ch[0]) == norm_text(args[0]):
                return args[0], args[1:]
            return ch[0], args
        return args[0], args[1:]
    ch = list(c.get_children())
    if ch:
        callee = ch[0]
        if callee.kind == K.MEMBER_REF_EXPR:
            base = list(callee.get_children())
            return (base[0] if base else None), args
    return None, args


# --------------------------------------------------------------------------- モジュールの情報


@dataclass
class Var:
    lean: str        # Lean 側での参照式（ローカル名、または s.フィールド）
    ty: str          # Lean の型
    field: str | None = None  # 状態フィールドならフィールド名


@dataclass
class Process:
    kind: str                     # "thread" | "method"
    name: str
    cursor: ci.Cursor | None = None
    sensitivity: list[str] = field(default_factory=list)
    dont_init: bool = False


@dataclass
class Module:
    name: str
    cursor: ci.Cursor
    fields: dict[str, tuple[str, str]] = field(default_factory=dict)  # name -> (type, default)
    arrays: dict[str, tuple[str, int]] = field(default_factory=dict)
    events: list[str] = field(default_factory=list)
    tsockets: dict[str, str | None] = field(default_factory=dict)  # socket -> b_transport method
    isockets: list[str] = field(default_factory=list)
    methods: dict[str, ci.Cursor] = field(default_factory=dict)
    processes: list[Process] = field(default_factory=list)
    ctor: ci.Cursor | None = None
    field_inits: list[tuple[str, ci.Cursor]] = field(default_factory=list)


@dataclass
class Ctx:
    kind: str                       # init | method | bt | thread | helper
    module: Module
    locals: dict[str, Var] = field(default_factory=dict)  # USR -> Var
    finish: str = "(s, out)"        # return のときの値
    aliases: dict[str, Var] = field(default_factory=dict)  # payload の正規化テキスト -> 結びついた変数
    proc: str = ""


# --------------------------------------------------------------------------- 変換器


class Translator:
    def __init__(self, rules: Rules, keep_going: bool = False):
        self.rules = rules
        self.keep_going = keep_going
        self.errors: list[Unsupported] = []
        self.helpers_needed: dict[str, ci.Cursor] = {}

    # ---- エラー -------------------------------------------------------------
    def guard(self, fn, *a, placeholder=None):
        try:
            return fn(*a)
        except Unsupported as e:
            if not self.keep_going:
                raise
            self.errors.append(e)
            return placeholder

    # ---- 型 -----------------------------------------------------------------
    def lean_type(self, t: ci.Type, where: ci.Cursor) -> str:
        key = type_key(t)
        types = self.rules.table("types")
        if key in types:
            return types[key]
        ct = ctype(t)
        if ct.kind == ci.TypeKind.ENUM:
            # ルールのない列挙型は C++ と同じく基底の整数型として扱う
            return self.lean_type(ct.get_declaration().enum_type, where)
        raise Unsupported(f"型 '{key}' の対応ルールがありません（[types] に追加してください）", where)

    def default_of(self, ty: str, where: ci.Cursor) -> str:
        d = self.rules.table("defaults")
        if ty in d:
            return d[ty]
        raise Unsupported(f"型 {ty} の既定値ルールがありません（[defaults]）", where)

    def convert(self, code: str, src: str, dst: str, c: ci.Cursor) -> str:
        if src == dst:
            return code
        numeric = ("Int", "Nat", "UInt8", "UInt16", "UInt32", "UInt64")
        if re.fullmatch(r"\(?\d+\)?", code) and src in numeric and dst in numeric:
            return code  # 整数リテラル（列挙子や定数を展開したもの）は型を問わない
        if is_literal(c) and dst not in ("Bool",) and src in ("Int", "Nat", "UInt8", "UInt16", "UInt32", "UInt64"):
            return code
        conv = self.rules.table("conversions")
        key = f"{src}->{dst}"
        if key in conv:
            return conv[key].replace("{e}", code)
        raise Unsupported(f"型変換 {key} のルールがありません（[conversions] に追加してください）", c)

    # ---- 正規表現ルール -----------------------------------------------------
    def find_sub(self, root: ci.Cursor, text: str) -> ci.Cursor | None:
        def walk(c):
            if c.kind != K.UNEXPOSED_EXPR and norm_text(c) == text:
                return c
            for ch in c.get_children():
                r = walk(ch)
                if r is not None:
                    return r
            return None
        for ch in root.get_children():
            r = walk(ch)
            if r is not None:
                return r
        return None

    def fill(self, tmpl: str, m: re.Match, root: ci.Cursor, ctx: Ctx) -> str:
        def rep(mm: re.Match) -> str:
            kind, idx = mm.group(1), int(mm.group(2))
            g = m.group(idx)
            if g is None:
                raise Unsupported(f"ルールのキャプチャ {idx} が空です", root)
            if kind == "raw":
                return g
            sub = self.find_sub(root, g)
            if sub is None:
                raise Unsupported(f"ルールのキャプチャ '{g}' に対応する部分式が見つかりません", root)
            code, ty = self.expr(sub, ctx)
            if kind == "n":
                return self.convert(code, ty, "Nat", sub)
            return code
        return re.sub(r"\{(raw|e|n)(\d+)\}", rep, tmpl)

    def try_expr_rules(self, c: ci.Cursor, ctx: Ctx):
        if not self.rules.expr_rules:
            return None
        text = norm_text(c)
        for rule in self.rules.expr_rules:
            m = rule["_re"].fullmatch(text)
            if m:
                return self.fill(rule["lean"], m, c, ctx), rule.get("type", self.lean_type(c.type, c))
        return None

    # ---- 式 -----------------------------------------------------------------
    def expr(self, c: ci.Cursor, ctx: Ctx, want: str | None = None) -> tuple[str, str]:
        r = self.try_expr_rules(c, ctx) if c.kind != K.UNEXPOSED_EXPR else None
        if r is None:
            r = self._expr(c, ctx)
        code, ty = r
        if want is not None and ty != want:
            code = self.convert(code, ty, want, c)
            ty = want
        return code, ty

    def _expr(self, c: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        k = c.kind
        if k == K.UNEXPOSED_EXPR:
            ch = list(c.get_children())
            if len(ch) != 1:
                raise Unsupported("解釈できない暗黙の式です", c)
            code, ty = self.expr(ch[0], ctx)
            if c.type.kind in (ci.TypeKind.POINTER,) or ch[0].type.kind == ci.TypeKind.CONSTANTARRAY:
                raise Unsupported("ポインタ／配列の減衰は扱えません", c)
            dst = self.lean_type(c.type, c)
            return self.convert(code, ty, dst, ch[0]), dst
        if k == K.INTEGER_LITERAL:
            return int_literal(c), self.lean_type(c.type, c)
        if k == K.CXX_BOOL_LITERAL_EXPR:
            return next(c.get_tokens()).spelling, "Bool"
        if k == K.PAREN_EXPR:
            code, ty = self.expr(list(c.get_children())[0], ctx)
            return f"({code})", ty
        if k == K.DECL_REF_EXPR:
            return self.ref(c, ctx)
        if k == K.MEMBER_REF_EXPR:
            return self.member(c, ctx)
        if k == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = list(c.get_children())
            name = self.state_array(base)
            if name is None:
                raise Unsupported("状態フィールドの配列以外の添字アクセスは扱えません", c)
            i, _ = self.expr(idx, ctx, "Nat")
            return f"s.{lean_id(name)}[{i}]!", self.module_array_type(name)
        if k == K.BINARY_OPERATOR:
            return self.binop(c, ctx)
        if k == K.UNARY_OPERATOR:
            op, prefix = unary_op(c)
            (a,) = list(c.get_children())
            if op in ("++", "--"):
                raise Unsupported("インクリメント／デクリメントは文としてだけ書けます", c)
            if op in ("&", "*"):
                raise Unsupported("ポインタ演算（& / *）は扱えません。定型句なら [[expr_rules]] を追加してください", c)
            code, ty = self.expr(a, ctx)
            if op == "+":
                return code, ty
            name = {"-": "neg"}.get(op, op)
            return self.op_template(ty, name, c).replace("{a}", self.paren(code)), self.lean_type(c.type, c)
        if k == K.CONDITIONAL_OPERATOR:
            cond, a, b = list(c.get_children())
            ty = self.lean_type(c.type, c)
            cc, _ = self.expr(cond, ctx, "Bool")
            ac, _ = self.expr(a, ctx, ty)
            bc, _ = self.expr(b, ctx, ty)
            return f"(if {cc} then {ac} else {bc})", ty
        if k in (K.CSTYLE_CAST_EXPR, K.CXX_STATIC_CAST_EXPR, K.CXX_FUNCTIONAL_CAST_EXPR):
            inner = [ch for ch in c.get_children() if ch.kind not in (K.TYPE_REF, K.NAMESPACE_REF)]
            if len(inner) != 1:
                raise Unsupported("キャストの形が想定外です", c)
            dst = self.lean_type(c.type, c)
            return self.expr(inner[0], ctx, dst)[0], dst
        if k == K.CALL_EXPR:
            return self.call_expr(c, ctx)
        if k == K.CXX_THIS_EXPR:
            raise Unsupported("this を値として使うことはできません", c)
        raise Unsupported(f"式の種類 {k.name} は扱えません", c)

    @staticmethod
    def paren(code: str) -> str:
        return code if re.fullmatch(r"[\w.\[\]!«»]+", code) else f"({code})"

    def op_template(self, ty: str, op: str, c: ci.Cursor) -> str:
        t = self.rules.table(f"ops.{ty}").get(op) or self.rules.table("ops.default").get(op)
        if t is None:
            raise Unsupported(f"演算子 {op}（型 {ty}）のルールがありません", c)
        return t

    def binop(self, c: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        op = op_spelling(c)
        if op in ("=", ","):
            raise Unsupported(f"式の中の '{op}' は扱えません（代入は文として書いてください）", c)
        a, b = list(c.get_children())
        if op in ("==", "!="):
            # 列挙型どうしの比較は C++ では int に昇格されるが、Lean では列挙のまま比べる
            ia, ib = strip_wrappers(a), strip_wrappers(b)
            ka, kb = ctype(ia.type).kind, ctype(ib.type).kind
            if ka == kb == ci.TypeKind.ENUM and type_key(ia.type) == type_key(ib.type):
                a, b = ia, ib
        ac, aty = self.expr(a, ctx)
        if op in ("<<", ">>"):
            bc, _ = self.expr(b, ctx, aty if aty != "Int" else None)
        elif op in ("&&", "||"):
            ac, aty = self.expr(a, ctx, "Bool")
            bc, _ = self.expr(b, ctx, "Bool")
        else:
            bc, bty = self.expr(b, ctx)
            if bty != aty:
                bc = self.convert(bc, bty, aty, b)
        code = self.op_template(aty, op, c).replace("{a}", self.paren(ac)).replace("{b}", self.paren(bc))
        return code, self.lean_type(c.type, c)

    def lookup_local(self, ref: ci.Cursor, ctx: Ctx) -> Var | None:
        return ctx.locals.get(ref.get_usr() or f"{ref.spelling}@{ref.location.offset}")

    def ref(self, c: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        ref = c.referenced
        if ref is None:
            raise Unsupported("参照先が解決できません", c)
        v = self.lookup_local(ref, ctx)
        if v is not None:
            return v.lean, v.ty
        if ref.kind in (K.ENUM_CONSTANT_DECL, K.VAR_DECL):
            q = qualname(ref)
            consts = self.rules.table("constants")
            if q in consts:
                return consts[q], self.lean_type(c.type, c)
            if ref.kind == K.ENUM_CONSTANT_DECL:
                return str(ref.enum_value), self.lean_type(ref.type, c)
            init = [ch for ch in ref.get_children() if ch.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
            if ctype(ref.type).is_const_qualified() and init and ref.semantic_parent.kind in (
                    K.TRANSLATION_UNIT, K.NAMESPACE, K.STRUCT_DECL, K.CLASS_DECL):
                ty = self.lean_type(ref.type, c)
                code, _ = self.expr(init[0], Ctx("helper", ctx.module), ty)
                return self.paren(code), ty
            raise Unsupported(f"定数 '{q}' のルールがありません（const で初期化式のある定数は自動展開します。"
                              f"それ以外は [constants] に追加してください）", c)
        raise Unsupported(f"'{c.spelling}'（{ref.kind.name}）への参照は扱えません", c)

    def is_this_member(self, c: ci.Cursor) -> bool:
        c = strip_wrappers(c)
        if c.kind != K.MEMBER_REF_EXPR:
            return False
        ch = list(c.get_children())
        return not ch or (len(ch) == 1 and strip_wrappers(ch[0]).kind == K.CXX_THIS_EXPR)

    def state_field(self, c: ci.Cursor, mod: Module) -> str | None:
        c = strip_wrappers(c)
        if self.is_this_member(c) and c.spelling in mod.fields:
            return c.spelling
        return None

    def state_array(self, c: ci.Cursor) -> str | None:
        c = strip_wrappers(c)
        if self.is_this_member(c) and c.spelling in self.cur.arrays:
            return c.spelling
        return None

    def module_array_type(self, name: str) -> str:
        return self.cur.arrays[name][0]

    def member(self, c: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        mod = ctx.module
        if self.is_this_member(c):
            if c.spelling in mod.fields:
                return f"s.{lean_id(c.spelling)}", mod.fields[c.spelling][0]
            if c.spelling in mod.arrays:
                raise Unsupported("配列全体を値として使うことはできません", c)
            raise Unsupported(f"メンバ '{c.spelling}' を値として使うことはできません", c)
        raise Unsupported(f"他のオブジェクトのメンバ '{c.spelling}' へのアクセスは扱えません（ルールで getter を定義してください）", c)

    def call_expr(self, c: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        ref = c.referenced
        if ref is None:
            raise Unsupported("呼び出し先が解決できません", c)
        recv, args = call_receiver_and_args(c)
        if ref.kind == K.CONSTRUCTOR:
            ty = self.lean_type(c.type, c)
            if not args:
                return self.default_of(ty, c), ty
            q = qualname(ref)
            if len(args) == 1 and type_key(args[0].type) == type_key(c.type):
                return self.expr(args[0], ctx)  # コピーコンストラクタ
        q = qualname(ref)
        tmpl = self.rules.table("calls.expr").get(q)
        if tmpl is not None:
            code = tmpl
            if "{this}" in code:
                if recv is None:
                    raise Unsupported(f"{q} のレシーバがありません", c)
                code = code.replace("{this}", self.paren(self.expr(recv, ctx)[0]))
            for i, a in enumerate(args):
                code = code.replace(f"{{{i}}}", self.paren(self.expr(a, ctx)[0]))
            return code, self.lean_type(c.type, c)
        if ref.kind == K.CXX_METHOD and ref.semantic_parent == ctx.module.cursor and (recv is None or self.is_this_member_base(recv)):
            if ref.result_type.kind == ci.TypeKind.VOID:
                raise Unsupported(f"void のヘルパメソッド {ref.spelling} は扱えません（呼び出し元に展開してください）", c)
            self.helpers_needed[ref.spelling] = definition_of(ref)
            ps = []
            for a, p in zip(args, ref.get_arguments()):
                ps.append(self.paren(self.expr(a, ctx, self.lean_type(p.type, p))[0]))
            return f"({lean_id(ref.spelling)} s{''.join(' ' + p for p in ps)})", self.lean_type(c.type, c)
        raise Unsupported(f"関数 '{q}' の呼び出しルールがありません（[calls.expr] に追加してください）", c)

    @staticmethod
    def is_this_member_base(c: ci.Cursor) -> bool:
        return strip_wrappers(c).kind == K.CXX_THIS_EXPR

    # ---- 代入 ---------------------------------------------------------------
    def assign(self, lhs: ci.Cursor, value: str, vty: str | None, vcur: ci.Cursor | None, ctx: Ctx) -> list[str]:
        lhs = strip_wrappers(lhs)
        mod = ctx.module
        if lhs.kind == K.DECL_REF_EXPR and lhs.referenced is not None:
            v = self.lookup_local(lhs.referenced, ctx)
            if v is None:
                raise Unsupported(f"'{lhs.spelling}' には代入できません", lhs)
            if vty is not None:
                value = self.convert(value, vty, v.ty, vcur)
            if v.field:
                return [f"s := {{ s with {lean_id(v.field)} := {value} }}"]
            return [f"{v.lean} := {value}"]
        if ctx.kind == "helper":
            raise Unsupported("ヘルパメソッドの中で状態を書き換えることはできません", lhs)
        name = self.state_field(lhs, mod)
        if name is not None:
            if vty is not None:
                value = self.convert(value, vty, mod.fields[name][0], vcur)
            return [f"s := {{ s with {lean_id(name)} := {value} }}"]
        if lhs.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = list(lhs.get_children())
            arr = self.state_array(base)
            if arr is not None:
                i, _ = self.expr(idx, ctx, "Nat")
                if vty is not None:
                    value = self.convert(value, vty, mod.arrays[arr][0], vcur)
                return [f"s := {{ s with {lean_id(arr)} := s.{lean_id(arr)}.set! {self.paren(i)} {self.paren(value)} }}"]
        raise Unsupported("この左辺への代入は扱えません", lhs)

    def rvalue_of(self, lhs: ci.Cursor, ctx: Ctx) -> tuple[str, str]:
        return self.expr(lhs, ctx)

    # ---- 文 -----------------------------------------------------------------
    def stmts(self, cs: list[ci.Cursor], ctx: Ctx) -> list[str]:
        out = []
        for c in cs:
            r = self.guard(self.stmt, c, ctx, placeholder=[f"-- sc2lean: 変換失敗 ({c.location.line} 行)"])
            out += r
        return out

    def try_stmt_rules(self, c: ci.Cursor, ctx: Ctx) -> list[str] | None:
        if not self.rules.stmt_rules:
            return None
        text = norm_text(c)
        for rule in self.rules.stmt_rules:
            m = rule["_re"].fullmatch(text)
            if not m:
                continue
            action = rule.get("action", "assign")
            if action == "bind_data_ptr":
                if ctx.kind != "thread":
                    raise Unsupported("set_data_ptr による変数の結びつけは SC_THREAD の中でだけ扱えます", c)
                return []  # 事前走査で処理済み
            if action == "skip":
                return []
            if action == "assign":
                if "lhs" not in rule:
                    raise Unsupported(f"ルール '{rule.get('name')}' に lhs がありません", c)
                lhs_t = re.sub(r"\{raw(\d+)\}", lambda mm: m.group(int(mm.group(1))) or "", rule["lhs"])
                target = self.find_sub(c, lhs_t)
                if target is None:
                    raise Unsupported(f"ルール '{rule.get('name')}' の左辺 '{lhs_t}' が見つかりません", c)
                value = self.fill(rule["lean"], m, c, ctx)
                return self.assign(target, value, None, None, ctx)
            if action == "lean":
                return [self.fill(rule["lean"], m, c, ctx)]
            raise Unsupported(f"ルール '{rule.get('name')}' の action '{action}' は不明です", c)
        return None

    def stmt(self, c: ci.Cursor, ctx: Ctx) -> list[str]:
        r = self.try_stmt_rules(c, ctx)
        if r is not None:
            return r
        k = c.kind
        if k == K.UNEXPOSED_EXPR:
            ch = list(c.get_children())
            if len(ch) == 1:
                return self.stmt(ch[0], ctx)
            raise Unsupported("解釈できない文です", c)
        if k == K.COMPOUND_STMT:
            return self.stmts(list(c.get_children()), ctx)
        if k == K.NULL_STMT:
            return []
        if k == K.DECL_STMT:
            out = []
            for d in c.get_children():
                out += self.decl(d, ctx)
            return out
        if k == K.BINARY_OPERATOR:
            op = op_spelling(c)
            if op != "=":
                raise Unsupported(f"値を使わない式 '{op}' は文として扱えません", c)
            lhs, rhs = list(c.get_children())
            v, vty = self.expr(rhs, ctx)
            return self.assign(lhs, v, vty, rhs, ctx)
        if k == K.COMPOUND_ASSIGNMENT_OPERATOR:
            op = op_spelling(c)[:-1]
            lhs, rhs = list(c.get_children())
            lc, lty = self.expr(lhs, ctx)
            rc, rty = self.expr(rhs, ctx)
            if rty != lty and op not in ("<<", ">>"):
                rc = self.convert(rc, rty, lty, rhs)
            v = self.op_template(lty, op, c).replace("{a}", self.paren(lc)).replace("{b}", self.paren(rc))
            return self.assign(lhs, v, None, None, ctx)
        if k == K.UNARY_OPERATOR:
            op, _ = unary_op(c)
            if op not in ("++", "--"):
                raise Unsupported(f"値を使わない式 '{op}' は文として扱えません", c)
            (a,) = list(c.get_children())
            ac, aty = self.expr(a, ctx)
            v = self.op_template(aty, op[0], c).replace("{a}", self.paren(ac)).replace("{b}", "1")
            return self.assign(a, v, None, None, ctx)
        if k == K.CALL_EXPR:
            return self.call_stmt(c, ctx)
        if k == K.IF_STMT:
            ch = list(c.get_children())
            if len(ch) not in (2, 3) or ch[0].kind in (K.DECL_STMT, K.VAR_DECL):
                raise Unsupported("初期化文つきの if は扱えません", c)
            cond, _ = self.expr(ch[0], ctx, "Bool")
            then_l = self.stmt(ch[1], ctx) or ["pure ()"]
            out = [f"if {cond} then"] + indent(then_l)
            if len(ch) == 3:
                else_l = self.stmt(ch[2], ctx) or ["pure ()"]
                out += ["else"] + indent(else_l)
            return out
        if k == K.WHILE_STMT:
            cond_c, body = list(c.get_children())
            if ctx.kind == "thread" and self.contains_wait(body):
                raise Unsupported("ループの中の wait は扱えません（SC_THREAD の最上位の while(true) だけ）", c)
            cond, _ = self.expr(cond_c, ctx, "Bool")
            return [f"while {cond} do"] + indent(self.stmt(body, ctx) or ["pure ()"])
        if k == K.FOR_STMT:
            ch = list(c.get_children())
            if len(ch) != 4:
                raise Unsupported("for は 初期化; 条件; 更新 をすべて書いた形だけ扱えます", c)
            init, cond_c, inc, body = ch
            if self.contains_kind(body, K.CONTINUE_STMT):
                raise Unsupported("for の中の continue は扱えません", c)
            if ctx.kind == "thread" and self.contains_wait(body):
                raise Unsupported("ループの中の wait は扱えません", c)
            out = self.stmt(init, ctx)
            cond, _ = self.expr(cond_c, ctx, "Bool")
            out += [f"while {cond} do"] + indent((self.stmt(body, ctx) or []) + self.stmt(inc, ctx))
            return out
        if k == K.BREAK_STMT:
            return ["break"]
        if k == K.CONTINUE_STMT:
            return ["continue"]
        if k == K.RETURN_STMT:
            ch = list(c.get_children())
            if ctx.kind == "thread":
                raise Unsupported("SC_THREAD の中の return は扱えません", c)
            if ctx.kind == "helper":
                if not ch:
                    raise Unsupported("値のない return", c)
                v, _ = self.expr(ch[0], ctx, ctx.finish)
                return [f"return {v}"]
            if ch:
                raise Unsupported("値つきの return は扱えません", c)
            return [f"return {ctx.finish}"]
        raise Unsupported(f"文の種類 {k.name} は扱えません", c)

    def contains_kind(self, c: ci.Cursor, kind) -> bool:
        if c.kind == kind:
            return True
        return any(self.contains_kind(ch, kind) for ch in c.get_children())

    def contains_wait(self, c: ci.Cursor) -> bool:
        if c.kind == K.CALL_EXPR and self.wait_kind(c) is not None:
            return True
        return any(self.contains_wait(ch) for ch in c.get_children())

    def decl(self, d: ci.Cursor, ctx: Ctx) -> list[str]:
        if d.kind != K.VAR_DECL:
            raise Unsupported(f"宣言 {d.kind.name} は扱えません", d)
        if d.storage_class == ci.StorageClass.STATIC:
            raise Unsupported("static ローカル変数は扱えません", d)
        if ctype(d.type).kind == ci.TypeKind.CONSTANTARRAY:
            raise Unsupported("ローカル配列は扱えません", d)
        ty = self.lean_type(d.type, d)
        init = [ch for ch in d.get_children() if ch.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
        key = d.get_usr() or f"{d.spelling}@{d.location.offset}"
        existing = ctx.locals.get(key)
        if init:
            v, _ = self.expr(init[0], ctx, ty)
        else:
            v = self.default_of(ty, d)
        if existing is not None and existing.field:
            return [f"s := {{ s with {lean_id(existing.field)} := {v} }}"]
        ctx.locals[key] = Var(lean_id(d.spelling), ty)
        return [f"let mut {lean_id(d.spelling)} : {ty} := {v}"]

    # ---- 呼び出し文 ---------------------------------------------------------
    def wait_kind(self, c: ci.Cursor) -> str | None:
        c = strip_wrappers(c)
        if c.kind != K.CALL_EXPR or c.referenced is None:
            return None
        q = qualname(c.referenced)
        if q == "sc_core::sc_module::wait":
            return "wait"
        if q == "tlm_utils::__sc2lean_fw_if::b_transport":
            return "b_transport"
        return None

    def event_of(self, c: ci.Cursor, mod: Module) -> str:
        c = strip_wrappers(c)
        if self.is_this_member(c) and c.spelling in mod.events:
            return c.spelling
        raise Unsupported("sc_event 型のメンバ以外のイベントは扱えません", c)

    def time_expr(self, args: list[ci.Cursor], ctx: Ctx, where: ci.Cursor) -> str:
        if len(args) == 1:
            return self.expr(args[0], ctx, "Nat")[0]
        if len(args) == 2:
            tmpl = self.rules.table("calls.expr").get("sc_core::sc_time::sc_time")
            if tmpl is None:
                raise Unsupported("sc_time コンストラクタのルールがありません", where)
            for i, a in enumerate(args):
                tmpl = tmpl.replace(f"{{{i}}}", self.paren(self.expr(a, ctx)[0]))
            return tmpl
        raise Unsupported("時間の指定の形が想定外です", where)

    def call_stmt(self, c: ci.Cursor, ctx: Ctx) -> list[str]:
        ref = c.referenced
        if ref is None:
            raise Unsupported("呼び出し先が解決できません", c)
        q = qualname(ref)
        recv, args = call_receiver_and_args(c)
        mod = ctx.module
        if self.wait_kind(c) is not None:
            where = {"bt": "ターゲット側 b_transport の中", "method": "SC_METHOD の中",
                     "init": "コンストラクタの中", "helper": "ヘルパメソッドの中"}.get(ctx.kind)
            if where:
                raise Unsupported(f"{where}では {ref.spelling} を呼べません", c)
            raise Unsupported(f"{ref.spelling} は SC_THREAD 本体の最上位の文としてだけ書けます", c)
        if q == "sc_core::sc_event::notify":
            if ctx.kind == "helper":
                raise Unsupported("ヘルパの中の notify は扱えません", c)
            ev = self.event_of(recv, mod)
            t = self.time_expr(args, ctx, c) if args else "0"
            return [f"out := out ++ [({t}, .ev_{ev})]"]
        if q in ("sc_core::sc_module::next_trigger",):
            raise Unsupported("next_trigger（動的感度）は扱えません", c)
        if q == "sc_core::sc_stop":
            return ["out := out ++ [(0, .stop)]"]
        if ref.spelling == "operator=" and recv is not None and len(args) == 1:
            v, vty = self.expr(args[0], ctx)
            return self.assign(recv, v, vty, args[0], ctx)
        tmpl = self.rules.table("calls.stmt").get(q)
        if tmpl is not None:
            if tmpl == "skip":
                return []
            if tmpl == "comment":
                return [f"pure ()  -- {source_text(c)}"]
            if tmpl == "stop":
                return ["out := out ++ [(0, .stop)]"]
            if recv is None:
                raise Unsupported(f"{q} のレシーバがありません", c)
            code = tmpl.replace("{this}", self.paren(self.expr(recv, ctx)[0]))
            for i, a in enumerate(args):
                code = code.replace(f"{{{i}}}", self.paren(self.expr(a, ctx)[0]))
            return self.assign(recv, code, None, None, ctx)
        raise Unsupported(f"関数 '{q}' を文として呼ぶルールがありません（[calls.stmt] に追加してください）", c)

    # ---- モジュール解析 -----------------------------------------------------
    def analyze(self, cls: ci.Cursor) -> Module:
        mod = Module(cls.spelling, cls)
        for ch in cls.get_children():
            k = ch.kind
            if k in (K.CXX_BASE_SPECIFIER, K.CXX_ACCESS_SPEC_DECL):
                continue
            if k == K.FIELD_DECL:
                self.guard(self.analyze_field, ch, mod)
            elif k == K.CONSTRUCTOR:
                if mod.ctor is not None:
                    raise Unsupported("コンストラクタは 1 つだけにしてください", ch)
                mod.ctor = definition_of(ch)
            elif k == K.CXX_METHOD:
                if ch.spelling in mod.methods:
                    raise Unsupported(f"メソッド {ch.spelling} のオーバーロードは扱えません", ch)
                mod.methods[ch.spelling] = definition_of(ch)
            elif k == K.DESTRUCTOR:
                continue
            else:
                raise Unsupported(f"クラス内の {k.name} は扱えません", ch)
        if mod.ctor is None:
            raise Unsupported("SC_CTOR がありません", cls)
        self.analyze_ctor(mod)
        return mod

    def analyze_field(self, f: ci.Cursor, mod: Module):
        key = type_key(f.type)
        t = ctype(f.type)
        if key == "sc_core::sc_event":
            mod.events.append(f.spelling)
            return
        if key.startswith("tlm_utils::simple_target_socket<"):
            mod.tsockets[f.spelling] = None
            return
        if key.startswith("tlm_utils::simple_initiator_socket<"):
            mod.isockets.append(f.spelling)
            return
        if t.kind == ci.TypeKind.CONSTANTARRAY:
            ety = self.lean_type(t.element_type, f)
            mod.arrays[f.spelling] = (ety, t.element_count)
            mod.fields_order = getattr(mod, "fields_order", []) + [f.spelling]
            return
        if t.kind in (ci.TypeKind.POINTER,):
            raise Unsupported(f"ポインタ型のフィールド '{f.spelling}' は扱えません", f)
        ty = self.lean_type(f.type, f)
        mod.fields[f.spelling] = (ty, self.default_of(ty, f))
        init = [ch for ch in f.get_children() if ch.kind not in (K.TYPE_REF, K.NAMESPACE_REF, K.TEMPLATE_REF)]
        if init:
            mod.field_inits.append((f.spelling, init[0]))

    def analyze_ctor(self, mod: Module):
        ctor = mod.ctor
        body = None
        pending_member = None
        for ch in ctor.get_children():
            if ch.kind in (K.PARM_DECL, K.TYPE_REF, K.NAMESPACE_REF):
                continue
            if ch.kind == K.MEMBER_REF:
                pending_member = ch.spelling
                continue
            if ch.kind == K.COMPOUND_STMT:
                body = ch
                continue
            if pending_member is not None:
                if pending_member in mod.fields:
                    mod.field_inits.append((pending_member, ch))
                pending_member = None
                continue
            raise Unsupported(f"コンストラクタの {ch.kind.name} は扱えません", ch)
        mod.init_stmts = []
        if body is None:
            return
        for st in body.get_children():
            s = strip_wrappers(st)
            if s.kind == K.CALL_EXPR and s.referenced is not None:
                q = qualname(s.referenced)
                if q in ("sc_core::__sc2lean_thread", "sc_core::__sc2lean_method"):
                    lit = list(s.get_arguments())[0]
                    name = strip_wrappers(lit).spelling.strip('"')
                    if name not in mod.methods:
                        raise Unsupported(f"プロセス関数 {name} が見つかりません", s)
                    kind = "thread" if q.endswith("thread") else "method"
                    mod.processes.append(Process(kind, name, mod.methods[name]))
                    continue
                if q == "sc_core::__sc2lean_dont_initialize":
                    if not mod.processes:
                        raise Unsupported("dont_initialize の前にプロセスがありません", s)
                    mod.processes[-1].dont_init = True
                    continue
                if q == "sc_core::sc_sensitive::operator<<":
                    if not mod.processes:
                        raise Unsupported("sensitive の前にプロセスがありません", s)
                    mod.processes[-1].sensitivity += self.sensitivity_chain(s, mod)
                    continue
                if s.referenced.spelling == "register_b_transport":
                    recv, args = call_receiver_and_args(s)
                    sock = strip_wrappers(recv).spelling
                    fn = norm_text(args[1]).split("::")[-1]
                    if sock not in mod.tsockets or fn not in mod.methods:
                        raise Unsupported("register_b_transport の対象が想定外です", s)
                    mod.tsockets[sock] = fn
                    continue
            mod.init_stmts.append(st)

    def sensitivity_chain(self, c: ci.Cursor, mod: Module) -> list[str]:
        c = strip_wrappers(c)
        if c.kind == K.CALL_EXPR and c.referenced is not None and qualname(c.referenced) == "sc_core::sc_sensitive::operator<<":
            recv, args = call_receiver_and_args(c)
            return self.sensitivity_chain(recv, mod) + [self.event_of(args[0], mod)]
        if self.is_this_member(c) and c.spelling == "sensitive":
            return []
        raise Unsupported("sensitive << の右辺は sc_event のメンバだけ扱えます", c)

    # ---- 生成 ---------------------------------------------------------------
    def gen_module(self, mod: Module) -> str:
        self.cur = mod
        self.helpers_needed = {}
        L: list[str] = []
        body: list[str] = []   # 関数定義（St/Msg の後に置く）
        extra_fields: list[tuple[str, str, str]] = []  # (name, type, default)
        pc_types: list[str] = []
        msgs: list[str] = ["stop"]
        dispatch: dict[str, list[tuple[str, list[str]]]] = {}  # msg ctor -> [(pattern, lines)]
        init_events: list[str] = []

        def add_msg(m: str):
            if m not in msgs:
                msgs.append(m)

        def on(ctor: str, pattern: str, lines: list[str], group: str | None = None, cond: str | None = None):
            """ctor のメッセージで lines を実行する。同じ group（スレッド）の分岐は else if で排他にする。"""
            dispatch.setdefault(ctor, []).append((pattern, group, cond, lines))

        for ev in mod.events:
            add_msg(f"ev_{ev}")

        # ---- ターゲットソケット
        for sock, fn in mod.tsockets.items():
            if fn is None:
                raise Unsupported(f"ソケット {sock} に register_b_transport がありません", mod.ctor)
            add_msg(f"{sock}_req (p : Payload)")
            add_msg(f"{sock}_resp (p : Payload) (d : Nat)")
            m = mod.methods[fn]
            params = list(m.get_arguments())
            if len(params) != 2 or not params[0].spelling or not params[1].spelling:
                raise Unsupported("b_transport は (payload&, sc_time&) の名前つき引数 2 つにしてください", m)
            ctx = Ctx("bt", mod)
            tn, dn = lean_id(params[0].spelling), lean_id(params[1].spelling)
            ctx.locals[params[0].get_usr()] = Var(tn, "Payload")
            ctx.locals[params[1].get_usr()] = Var(dn, "Nat")
            ctx.finish = f"(s, out ++ [(0, .{sock}_resp {tn} {dn})])"
            lines = self.stmts(list(self.body_of(m).get_children()), ctx)
            fname = f"{sock}_{fn}"
            body += [f"/-- {mod.name}::{fn}（{sock} の b_transport） -/",
                     f"def {fname} (s : St) ({tn} : Payload) : St × List (Nat × Msg) := Id.run do",
                     "  let mut s := s", "  let mut out : List (Nat × Msg) := []",
                     f"  let mut {tn} := {tn}", f"  let mut {dn} : Nat := 0"]
            body += indent(lines) + [f"  return {ctx.finish}", ""]
            on(f"{sock}_req", f".{sock}_req p", [f"let r := {fname} s p", "s := r.1", "out := out ++ r.2"])

        for sock in mod.isockets:
            add_msg(f"{sock}_req (p : Payload)")
            add_msg(f"{sock}_resp (p : Payload) (d : Nat)")

        # ---- プロセス
        for proc in mod.processes:
            if proc.kind == "method":
                self.gen_method(mod, proc, body, add_msg, on, init_events)
            else:
                self.gen_thread(mod, proc, body, add_msg, on, init_events, extra_fields, pc_types)

        # ---- ヘルパ（呼ばれたものだけ。ヘルパ内から別ヘルパを呼ぶ場合に備えて繰り返す）
        helper_defs: list[str] = []
        done: set[str] = set()
        while set(self.helpers_needed) - done:
            for name in list(set(self.helpers_needed) - done):
                helper_defs = self.gen_helper(mod, self.helpers_needed[name]) + helper_defs
                done.add(name)

        # ---- 初期状態
        ictx = Ctx("init", mod)
        ilines = []
        for name, e in mod.field_inits:
            v, _ = self.guard(self.expr, e, ictx, mod.fields[name][0], placeholder=("0", ""))
            ilines.append(f"s := {{ s with {lean_id(name)} := {v} }}")
        ilines += self.stmts(mod.init_stmts, ictx)

        # ---- 組み立て
        L.append(f"namespace {mod.name}")
        L.append("")
        L += pc_types
        L.append("structure St where")
        for n, (ty, d) in mod.fields.items():
            L.append(f"  {lean_id(n)} : {ty} := {d}")
        for n, (ety, size) in mod.arrays.items():
            L.append(f"  {lean_id(n)} : Array {ety} := Array.replicate {size} {self.default_of(ety, mod.cursor)}")
        for n, ty, d in extra_fields:
            L.append(f"  {lean_id(n)} : {ty} := {d}")
        if not (mod.fields or mod.arrays or extra_fields):
            L.append("  dummy : Unit := ()")
        L.append("  deriving Repr")
        L.append("")
        L.append("inductive Msg")
        for m in msgs:
            L.append(f"  | {m}")
        L.append("  deriving Repr")
        L.append("")
        L += helper_defs
        L += body
        L.append("/-- コンストラクタ本体を実行した初期状態 -/")
        L.append("def init : St := Id.run do")
        L.append("  let mut s : St := {}")
        L += indent(ilines)
        L.append("  return s")
        L.append("")
        L.append("/-- 時刻 0 に投入するメッセージ（プロセスの起動） -/")
        L.append(f"def initEvents : List (Nat × Msg) := [{', '.join(init_events)}]")
        L.append("")
        L.append("/-- 1 メッセージを配送する。同じメッセージで起きるプロセスは宣言順に実行する。 -/")
        L.append("def step (s : St) (m : Msg) : St × List (Nat × Msg) := Id.run do")
        L.append("  let mut s := s")
        L.append("  let mut out : List (Nat × Msg) := []")
        if dispatch:
            L.append("  match m with")
            for ctor, handlers in dispatch.items():
                L.append(f"  | {handlers[0][0]} =>")
                prev_group = None
                for _, group, cond, lines in handlers:
                    if cond is None:
                        L += indent(lines, 4)
                        prev_group = None
                        continue
                    kw = "else if" if group is not None and group == prev_group else "if"
                    L.append(f"    {kw} {cond} then")
                    L += indent(lines, 6)
                    prev_group = group
            L.append("  | _ => pure ()")
        L.append("  return (s, out)")
        L.append("")
        L.append(f"end {mod.name}")
        return "\n".join(L)

    def body_of(self, m: ci.Cursor) -> ci.Cursor:
        for ch in m.get_children():
            if ch.kind == K.COMPOUND_STMT:
                return ch
        raise Unsupported("関数本体がありません", m)

    def gen_helper(self, mod: Module, m: ci.Cursor) -> list[str]:
        ctx = Ctx("helper", mod)
        ret = self.lean_type(m.result_type, m)
        ctx.finish = ret
        ps = []
        for p in m.get_arguments():
            ty = self.lean_type(p.type, p)
            ctx.locals[p.get_usr()] = Var(lean_id(p.spelling), ty)
            ps.append(f"({lean_id(p.spelling)} : {ty})")
        lines = self.stmts(list(self.body_of(m).get_children()), ctx)
        out = [f"def {lean_id(m.spelling)} (s : St){''.join(' ' + p for p in ps)} : {ret} := Id.run do"]
        for p in m.get_arguments():
            out.append(f"  let mut {lean_id(p.spelling)} := {lean_id(p.spelling)}")
        out += indent(lines)
        if not lines or not lines[-1].startswith("return "):
            out.append(f"  return {self.default_of(ret, m)}  -- C++ で return せずに抜けた場合（未定義動作）")
        return out + [""]

    def gen_method(self, mod, proc, body, add_msg, on, init_events):
        ctx = Ctx("method", mod, proc=proc.name)
        lines = self.stmts(list(self.body_of(proc.cursor).get_children()), ctx)
        fname = f"{proc.name}_run"
        body += [f"/-- SC_METHOD {proc.name} -/",
                 f"def {fname} (s : St) : St × List (Nat × Msg) := Id.run do",
                 "  let mut s := s", "  let mut out : List (Nat × Msg) := []"]
        body += indent(lines) + ["  return (s, out)", ""]
        call = [f"let r := {fname} s", "s := r.1", "out := out ++ r.2"]
        if not proc.dont_init:
            add_msg(f"start_{proc.name}")
            init_events.append(f"(0, .start_{proc.name})")
            on(f"start_{proc.name}", f".start_{proc.name}", call)
        for ev in proc.sensitivity:
            on(f"ev_{ev}", f".ev_{ev}", call)

    def gen_thread(self, mod, proc, body, add_msg, on, init_events, extra_fields, pc_types):
        th = proc.name
        top = list(self.body_of(proc.cursor).get_children())
        # 最後の文が無限ループなら本体として分ける
        loop_body: list[ci.Cursor] | None = None
        if top and self.is_forever(top[-1]):
            loop_body = list(self.loop_body(top[-1]).get_children())
            prefix = top[:-1]
        else:
            prefix = top
        for st in prefix[:-1] if loop_body is None else prefix:
            if self.is_forever(st):
                raise Unsupported("無限ループの後ろの文には到達しません", st)
        items = prefix + (loop_body or [])
        loop_start = len(prefix)
        if loop_body is not None and not any(self.wait_kind(x) for x in loop_body):
            nested = next((x for x in loop_body if self.contains_wait(x)), None)
            if nested is not None:
                raise Unsupported("wait / b_transport は while(true) 本体の最上位の文としてだけ書けます（if やループの中は不可）", nested)
            raise Unsupported("wait を含まない無限ループです", top[-1])

        # スレッドのローカル変数（最上位で宣言されたもの）は状態フィールドに昇格する
        ctx = Ctx("thread", mod, proc=th)
        for st in items:
            if st.kind == K.DECL_STMT:
                for d in st.get_children():
                    if d.kind != K.VAR_DECL:
                        continue
                    if ctype(d.type).kind == ci.TypeKind.CONSTANTARRAY:
                        raise Unsupported("スレッドのローカル配列は扱えません", d)
                    ty = self.lean_type(d.type, d)
                    fname = f"{th}_{d.spelling}"
                    if fname in mod.fields:
                        raise Unsupported(f"フィールド名 {fname} が衝突します", d)
                    extra_fields.append((fname, ty, self.default_of(ty, d)))
                    ctx.locals[d.get_usr()] = Var(f"s.{lean_id(fname)}", ty, fname)
        # set_data_ptr(&v) の結びつけを事前に集める
        for st in items:
            text = norm_text(st)
            for rule in self.rules.stmt_rules:
                if rule.get("action") != "bind_data_ptr":
                    continue
                mm = rule["_re"].fullmatch(text)
                if mm:
                    g = [x for x in mm.groups() if x is not None]
                    payload, var = g[0], g[1]
                    vc = self.find_sub(st, var)
                    if vc is None or vc.referenced is None or self.lookup_local(vc.referenced, ctx) is None:
                        raise Unsupported(f"set_data_ptr の結びつけ先 '{var}' はスレッドのローカル変数にしてください", st)
                    ctx.aliases[payload] = vc
                    break

        waits = [i for i, x in enumerate(items) if self.wait_kind(x)]
        labels = ["start"] + [f"w{j}" for j in range(len(waits))]
        label_of_wait = {i: f"w{j}" for j, i in enumerate(waits)}
        pc_ty = f"{th.capitalize()}Pc"
        ctors = labels + ["done"]
        pc_types += [f"inductive {pc_ty} | " + " | ".join(ctors), "  deriving Repr, BEq, DecidableEq", ""]
        extra_fields.insert(0, (f"{th}_pc", pc_ty, ".start"))
        pcf = f"{th}_pc"

        def segment_after(pos: int) -> tuple[list[ci.Cursor], int | None]:
            """pos の次から次の wait まで（ループの末尾から先頭へ回り込む）。"""
            seg = []
            i = pos + 1
            wrapped = False
            while True:
                if i >= len(items):
                    if loop_body is None:
                        return seg, None
                    if wrapped:
                        raise Unsupported("内部エラー: wait のないループ", proc.cursor)
                    i, wrapped = loop_start, True
                    continue
                if i in label_of_wait:
                    return seg, i
                seg.append(items[i])
                i += 1

        for label in labels:
            pos = -1 if label == "start" else waits[int(label[1:])]
            seg, nxt = segment_after(pos)
            fname = f"{th}_{label}"
            params, resume = "", []
            trigger = []
            if label == "start":
                if proc.dont_init:
                    if not proc.sensitivity:
                        raise Unsupported("dont_initialize のスレッドに感度リストがありません", proc.cursor)
                    trigger = [(f"ev_{e}", f".ev_{e}") for e in proc.sensitivity]
                else:
                    add_msg(f"start_{th}")
                    init_events.append(f"(0, .start_{th})")
                    trigger = [(f"start_{th}", f".start_{th}")]
            else:
                w = strip_wrappers(items[pos])
                trigger, params, resume = self.wait_trigger(w, ctx, proc, add_msg)
            lines = self.stmts(seg, ctx)
            if nxt is None:
                tail = [f"s := {{ s with {pcf} := .done }}"]
            else:
                tail = self.wait_suspend(strip_wrappers(items[nxt]), ctx, mod) + [f"s := {{ s with {pcf} := .{label_of_wait[nxt]} }}"]
            body += [f"/-- SC_THREAD {th}: {'起動' if label == 'start' else label + ' の再開'}から次の待ちまで -/",
                     f"def {fname} (s : St){params} : St × List (Nat × Msg) := Id.run do",
                     "  let mut s := s", "  let mut out : List (Nat × Msg) := []"]
            body += indent(resume + lines + tail) + ["  return (s, out)", ""]
            args = " ".join(a.split(":")[0].strip(" (") for a in params.split(") (") if a.strip()) if params else ""
            call = [f"let r := {fname} s{(' ' + args) if args else ''}", "s := r.1", "out := out ++ r.2"]
            for ctor, pat in trigger:
                on(ctor, pat, call, group=th, cond=f"s.{pcf} == .{label}")

    def is_forever(self, c: ci.Cursor) -> bool:
        if c.kind == K.WHILE_STMT:
            cond = strip_wrappers(list(c.get_children())[0])
            return cond.kind == K.CXX_BOOL_LITERAL_EXPR and norm_text(cond) == "true" or (
                cond.kind == K.INTEGER_LITERAL and int_literal(cond) != "0")
        if c.kind == K.FOR_STMT:
            return len(list(c.get_children())) == 1
        return False

    def loop_body(self, c: ci.Cursor) -> ci.Cursor:
        b = list(c.get_children())[-1]
        if b.kind != K.COMPOUND_STMT:
            raise Unsupported("無限ループの本体は { } で書いてください", c)
        return b

    def wait_trigger(self, w: ci.Cursor, ctx: Ctx, proc: Process, add_msg):
        """wait の後で再開するきっかけ: (trigger list, 追加引数, 再開時の前処理)"""
        th = proc.name
        kind = self.wait_kind(w)
        recv, args = call_receiver_and_args(w)
        if kind == "b_transport":
            sock = self.isocket_of(recv, ctx.module)
            tr, dl = args
            resume = self.assign(tr, "p", "Payload", None, ctx)
            dc, _ = self.expr(dl, ctx)
            resume += self.assign(dl, f"{self.paren(dc)} + d", None, None, ctx)
            alias = ctx.aliases.get(norm_text(strip_wrappers(tr)))
            if alias is not None:
                trc, _ = self.expr(tr, ctx)
                resume += self.assign(alias, f"{self.paren(trc)}.data", None, None, ctx)
            return [(f"{sock}_resp", f".{sock}_resp p d")], " (p : Payload) (d : Nat)", resume
        if not args:
            if not proc.sensitivity:
                raise Unsupported("引数なしの wait() には静的感度が必要です", w)
            return [(f"ev_{e}", f".ev_{e}") for e in proc.sensitivity], "", []
        if len(args) == 1 and type_key(args[0].type) == "sc_core::sc_event":
            ev = self.event_of(args[0], ctx.module)
            return [(f"ev_{ev}", f".ev_{ev}")], "", []
        add_msg(f"wake_{th}")
        return [(f"wake_{th}", f".wake_{th}")], "", []

    def wait_suspend(self, w: ci.Cursor, ctx: Ctx, mod: Module) -> list[str]:
        """wait に入るときに出すメッセージ"""
        kind = self.wait_kind(w)
        recv, args = call_receiver_and_args(w)
        if kind == "b_transport":
            sock = self.isocket_of(recv, mod)
            if len(args) != 2:
                raise Unsupported("b_transport の引数が想定外です", w)
            tr = args[0]
            out = []
            alias = ctx.aliases.get(norm_text(strip_wrappers(tr)))
            if alias is not None:
                trc, _ = self.expr(tr, ctx)
                ac, _ = self.expr(alias, ctx)
                out += self.assign(tr, f"{{ {trc} with data := {ac} }}", None, None, ctx)
            trc, _ = self.expr(tr, ctx, "Payload")
            for a in args:
                if strip_wrappers(a).kind != K.DECL_REF_EXPR:
                    raise Unsupported("b_transport の引数は変数にしてください", a)
            return out + [f"out := out ++ [(0, .{sock}_req {self.paren(trc)})]"]
        if not args or (len(args) == 1 and type_key(args[0].type) == "sc_core::sc_event"):
            return []
        t = self.time_expr(args, ctx, w)
        return [f"out := out ++ [({t}, .wake_{ctx.proc})]"]

    def isocket_of(self, recv: ci.Cursor, mod: Module) -> str:
        r = strip_wrappers(recv)
        if r.kind == K.CALL_EXPR and r.spelling == "operator->":
            inner = list(r.get_children())[0]
            if self.is_this_member(inner) and inner.spelling in mod.isockets:
                return inner.spelling
        raise Unsupported("b_transport は initiator socket のメンバに対して呼んでください", recv)


# --------------------------------------------------------------------------- 入口


def parse(path: Path, extra_args: list[str]) -> ci.TranslationUnit:
    args = ["-x", "c++", "-std=c++17", "-nostdinc", "-nostdinc++", f"-I{HERE / 'stubs'}"] + extra_args
    tu = ci.Index.create().parse(str(path), args=args)
    errs = [d for d in tu.diagnostics if d.severity >= ci.Diagnostic.Error]
    if errs:
        msg = "\n".join(f"{d.location.file}:{d.location.line}:{d.location.column}: {d.spelling}" for d in errs)
        hint = ""
        if any("file not found" in d.spelling for d in errs):
            hint = ("\n  標準ライブラリと SystemC は本物のヘッダではなく stubs/ の最小ヘッダで解析します。"
                    "\n  自分のヘッダなら -I でディレクトリを指定し、標準ヘッダなら stubs/ に最小の宣言を足してください。")
        raise ParseError("C++ の構文解析に失敗しました（スタブにない API を使っていませんか）:\n" + msg + hint)
    return tu


def is_stub(f) -> bool:
    return f is not None and os.path.realpath(f.name).startswith(str(HERE / "stubs") + os.sep)


def is_module_class(c: ci.Cursor) -> bool:
    for b in c.get_children():
        if b.kind == K.CXX_BASE_SPECIFIER and b.referenced is not None and qualname(b.referenced) == "sc_core::sc_module":
            return True
    return False


def module_complete(cls: ci.Cursor) -> bool:
    """コンストラクタとメソッドの本体がすべてこの翻訳単位にあるか"""
    return all(ch.get_definition() is not None for ch in cls.get_children()
               if ch.kind in (K.CONSTRUCTOR, K.CXX_METHOD))


def find_modules(tu: ci.TranslationUnit, path: Path, notes: list) -> list[ci.Cursor]:
    """入力ファイルと、そこから読まれる自分のヘッダ（stubs/ 以外）にある sc_module を集める。
    ヘッダにあって本体がこの入力にないモジュールは変換せず notes に記録する。
    モジュール以外の宣言（定数、enum、関数宣言、普通のクラスなど）は、使われたときに処理する。"""
    mods = []
    main = os.path.realpath(str(path))

    def walk(c):
        for ch in c.get_children():
            f = ch.location.file
            if f is None or is_stub(f):
                continue
            in_main = os.path.realpath(f.name) == main
            if ch.kind in (K.NAMESPACE, K.LINKAGE_SPEC):
                walk(ch)
            elif ch.kind in (K.STRUCT_DECL, K.CLASS_DECL) and ch.is_definition() and is_module_class(ch):
                if in_main or module_complete(ch):
                    mods.append(ch)
                else:
                    notes.append((ch.get_usr(), f"{f.name}: モジュール {ch.spelling} は本体が入力にないので変換しません"
                                                " （実装の .cpp も入力に渡してください）"))
            elif ch.kind == K.CLASS_TEMPLATE and is_module_class(ch):
                raise Unsupported(f"テンプレートのモジュール {ch.spelling} は扱えません", ch)
    walk(tu.cursor)
    return mods


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="制約付き SystemC/TLM を Lean 4 に変換する")
    ap.add_argument("inputs", nargs="+", type=Path)
    ap.add_argument("-o", "--output", type=Path, help="出力 .lean（省略時は標準出力）")
    ap.add_argument("-r", "--rules", type=Path, action="append", default=[], help="追加ルール（TOML、複数可）")
    ap.add_argument("--no-default-rules", action="store_true", help="既定ルールを読まない")
    ap.add_argument("-k", "--keep-going", action="store_true", help="未対応箇所をすべて集めてから失敗する")
    ap.add_argument("-I", dest="incdirs", action="append", default=[], help="追加のインクルードパス")
    ap.add_argument("-D", dest="defines", action="append", default=[], help="マクロ定義")
    a = ap.parse_args(argv)

    rules = Rules.load(a.rules, use_default=not a.no_default_rules)
    tr = Translator(rules, keep_going=a.keep_going)
    extra = [f"-I{d}" for d in a.incdirs] + [f"-D{d}" for d in a.defines]
    out = ["-- sc2lean で自動生成。手で編集する場合は生成元とルールも合わせて更新すること。",
           "set_option linter.unusedVariables false", ""]
    out.append(rules.table("lean").get("prelude", "").strip())
    out.append("")
    extra_prelude = rules.table("lean").get("extra", "").strip()
    if extra_prelude:
        out += [extra_prelude, ""]
    notes: list[tuple[str, str]] = []
    seen: set[str] = set()
    try:
        for p in a.inputs:
            tu = parse(p, extra)
            for cls in find_modules(tu, p, notes):
                if cls.get_usr() in seen:
                    continue  # 複数の .cpp から読まれたヘッダのモジュール
                seen.add(cls.get_usr())
                mod = tr.analyze(cls)
                text = tr.guard(tr.gen_module, mod, placeholder="")
                out.append(text)
                out.append("")
    except (Unsupported, ParseError) as e:
        print(f"sc2lean: {e}", file=sys.stderr)
        return 1
    reported = set()
    for usr, n in notes:
        if usr not in seen and usr not in reported:  # 別の入力で変換できたものは除く
            reported.add(usr)
            print(f"sc2lean: 注意: {n}", file=sys.stderr)
    if tr.errors:
        for e in tr.errors:
            print(e.format(), file=sys.stderr)
        print(f"sc2lean: 未対応箇所が {len(tr.errors)} 件あります", file=sys.stderr)
        return 1
    text = "\n".join(out)
    if a.output:
        a.output.write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
