#!/usr/bin/env bash
# 変換 → Lean でコンパイル → シミュレーション結果の #guard、未対応記述の検出を確認する。
# LEAN 環境変数で lean のパスを指定できる（既定は PATH 上の lean）。
set -euo pipefail
cd "$(dirname "$0")"
LEAN=${LEAN:-lean}

python3 sc2lean.py examples/memory.cpp examples/initiator.cpp -o test/Generated.lean
python3 sc2lean.py examples/counter.cpp -r examples/extra_rules.toml -o test/Counter.gen.lean
(cd test && "$LEAN" -o Generated.olean Generated.lean && LEAN_PATH=. "$LEAN" Harness.lean)
cat test/Counter.gen.lean test/CounterTest.lean.in > test/Counter.lean
(cd test && "$LEAN" Counter.lean)
echo "ok: 生成コードのコンパイルとシミュレーション"

expect_fail() {  # $1 = 入力, 残り = 期待するメッセージ（部分一致）
  local f=$1; shift
  if out=$(python3 sc2lean.py -k "$f" 2>&1); then echo "NG: $f が通ってしまった"; exit 1; fi
  for m in "$@"; do
    grep -qF -- "$m" <<<"$out" || { echo "NG: $f に '$m' がない"; echo "$out"; exit 1; }
  done
}
expect_fail examples/bad.cpp "ポインタ型のフィールド" "最上位の文としてだけ"
expect_fail examples/bad2.cpp "SWITCH_STMT" "b_transport の中では wait"
if python3 sc2lean.py examples/counter.cpp >/dev/null 2>&1; then echo "NG: ルールなしで parity が通った"; exit 1; fi
echo "ok: 未対応記述の検出"
