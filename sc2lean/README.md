# sc2lean — 制約付き SystemC/TLM を Lean 4 に変換する

libclang で C++ を解析し、TOML のルールに従って Lean 4 のイベント駆動モデルを生成します。
ルールにない記述に出会うと、ソース位置つきの例外 `Unsupported` を出して止まります。

```
pip install libclang            # Python 3.11 以上（tomllib を使用）
python3 sc2lean.py examples/memory.cpp examples/initiator.cpp -o Out.lean
python3 sc2lean.py foo.cpp -r my_rules.toml -r more.toml   # ルールの追加
python3 sc2lean.py -k foo.cpp   # 未対応箇所を全部集めてから失敗する
LEAN=/path/to/lean ./run_tests.sh
```

SystemC 本体は不要です。`stubs/` の最小ヘッダ（`-nostdinc` で解析）を使うため、
スタブにない API を使うと構文解析の段階でエラーになります。これも「想定外の記述」の検出として働きます。
スタブを足すか、`-I` で別のスタブを先に読ませれば拡張できます。

## 生成物

モジュールごとに `namespace <Module>` を作り、その中に次のものを置きます。

| 名前 | 内容 |
|---|---|
| `St` | 状態。メンバ変数、配列（`Array`）、スレッドの PC、スレッドのローカル変数（`<thread>_<var>`） |
| `Msg` | 入出力メッセージ。`ev_<event>`、`<socket>_req p`、`<socket>_resp p d`、`start_<proc>`、`wake_<thread>`、`stop` |
| `init` | コンストラクタを実行した後の状態 |
| `initEvents` | 時刻 0 に投入するメッセージ |
| `step : St → Msg → St × List (Nat × Msg)` | 1 メッセージの配送。返すのは（遅延 ps, メッセージ）の列 |

時間は ps 単位の `Nat` です。ソケット間の配線は生成しません（`test/Harness.lean` が配線とイベントキューの例）。

## 変換規則（対応する書き方）

- **SC_THREAD**: `[前置きの文] + while(true){...}`。`wait(...)` と `socket->b_transport(...)` は本体の最上位の文としてだけ書けます。待ちの位置ごとに PC の値を作り、「再開から次の待ちまで」を 1 つの Lean 関数にします。ループの末尾は先頭に回り込みます。
  - `wait(t)` / `wait(v, unit)`: `wake_<thread>` を遅延 t で自分に送り、それを受けて再開
  - `wait(ev)`: `ev_<ev>` を受けて再開
  - `wait()`: 静的感度のイベントのどれかで再開
  - `sock->b_transport(trans, delay)`: `<sock>_req trans` を送り、`<sock>_resp p d` を受けて `trans := p; delay := delay + d` で再開（LT のブロッキング呼び出しを要求と応答の 2 メッセージに分解）
- **SC_METHOD**: 本体を 1 関数にします。`sensitive <<` のイベントと（`dont_initialize` がなければ）`start_<m>` で起動します。
- **ターゲット側 b_transport**: `<sock>_req p` を受けて本体を実行し、`<sock>_resp trans delay` を返します。`return;` も使えます。
- **ヘルパメソッド**: 値を返し、状態を書き換えないものは `def f (s : St) ...` になります。
- **ev.notify(t)** は `(t, .ev_x)` を送ります。`notify()`（即時通知）も遅延 0 のメッセージになるので、デルタサイクルとの違いに注意してください。
- 同じメッセージで起きるプロセスは宣言順に実行します（SystemC が許す実行順の 1 つ）。誰も待っていないイベントは捨てられます。これは SystemC と同じ挙動です。

## ルールファイル（`rules/default.toml`）

`-r` で渡したファイルは既定ルールの上に重ねられます。テーブルはキー単位で上書きし、`[[stmt_rules]]` / `[[expr_rules]]` は先頭に追加されて優先されます。

| テーブル | 役割 |
|---|---|
| `[types]` | C++ の canonical な型 → Lean の型 |
| `[defaults]` | Lean の型の既定値 |
| `[conversions]` | `"UInt64->UInt32" = "({e}).toUInt32"` のような型変換（暗黙・明示のキャスト） |
| `[ops.default]`, `[ops.<型>]` | 演算子の対応（`[ops.Int]` で `/`, `%` を `Int.tdiv` / `Int.tmod` にしているのは C++ の 0 方向丸めに合わせるため） |
| `[constants]` | 列挙子・定数の修飾名 → Lean の式（時間単位もここ） |
| `[calls.expr]` | 値を返す関数・メソッドの修飾名 → テンプレート（`{this}`, `{0}`, `{1}`…） |
| `[calls.stmt]` | 状態を変えるメソッド → レシーバに代入する新しい値（`"skip"` なら無視） |
| `[[stmt_rules]]` / `[[expr_rules]]` | 正規化テキストへの正規表現による定型句の変換（`memcpy` やデータポインタの扱い） |
| `[lean] prelude` / `[lean] extra` | 出力の先頭に置く Lean コード（`extra` は複数ファイルで連結） |

正規表現は、トークンを詰めて並べた「正規化テキスト」に完全一致させます（識別子どうしの間にだけ空白が入る。例: `memcpy(trans.get_data_ptr(),&mem[addr/4],4)`）。テンプレートでは `{rawN}`（キャプチャそのまま）、`{eN}`（キャプチャと同じテキストの部分式を Lean に訳したもの）、`{nN}`（それを Nat にしたもの）が使えます。

利用者ルールの例は `examples/extra_rules.toml` です。プロジェクト独自の関数 `parity` を Lean 関数に対応させ、その定義を `[lean] extra` で出力に足しています。

## 例外になる主な記述

ポインタ（フィールド、`&` / `*`、配列の減衰）、`switch`、`if`・ループの中の `wait`、ターゲット側 `b_transport` や SC_METHOD の中の `wait`、`next_trigger`、`continue` を含む `for`、初期化文つきの `if`、ローカル配列、`static` ローカル、ルールのない型・関数・定数・型変換、sc_module 以外のクラス、自由関数の定義、`sc_signal` / `sc_in` / `sc_out`、nb_transport、DMI。
メッセージには、どのテーブルにルールを足せばよいかが出ます。

## 割り切り

- generic payload はワード単位（`data : UInt32`）にしています。データポインタは `set_data_ptr(&v)` と `memcpy` の定型句だけをルールで扱います。`set_data_ptr(&v)` は「b_transport の直前に `trans.data := v`、応答後に `v := trans.data`」に変換します。
- ループは Lean の `while` になります。実行はできますが、証明で扱うには `for i in [a:b]` などへの書き換えが必要です。
- 変換の正しさは証明していません。`test/Harness.lean` のように、SystemC と同じ刺激を与えてトレースを比べる差分テストで確認してください。
