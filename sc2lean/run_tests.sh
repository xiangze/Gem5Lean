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
python3 sc2lean.py examples/split/top.cpp examples/split/mem.cpp -o test/Split.gen.lean
cat test/Split.gen.lean test/SplitTest.lean.in > test/Split.lean
(cd test && "$LEAN" Split.lean)
echo "ok: 生成コードのコンパイルとシミュレーション（ヘッダ分割を含む）"

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
printf '#include <systemc>\nSC_MODULE(E){ SC_CTOR(E){ SC_REPORT_ERROR("E","x"); } };\n' > test/report_error.cpp
expect_fail test/report_error.cpp "sc_core::sc_report_error"
python3 sc2lean.py test/report_error.cpp -r examples/split/report_rules.toml >/dev/null
rm -f test/report_error.cpp
echo "ok: 未対応記述の検出とルールによる解除"
