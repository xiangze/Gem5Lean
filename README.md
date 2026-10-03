# Gem5Lean — gem5 の TLM 抽象を Lean 4 で再定義し、形式検証する

依存は Lean 4 core のみ (v4.22.0, Mathlib なし)。`sorry` / `native_decide` なし。
主定理が使う公理は標準の `propext`, `Quot.sound`, `Classical.choice` だけです (`Axioms.lean` で確認できます)。

```
lake build            # 全証明のチェック + #eval / #guard によるシミュレーションテスト
lake env lean Axioms.lean
```

## 構成

| ファイル | gem5 で対応するもの | 内容 |
|---|---|---|
| `Kernel.lean` | `SimObject`, ports, `EventQueue`, `simulate()` | Module / 並列合成 / 配線 / イベントキュー / 実行可能 `step` と関係的仕様 `Step` |
| `Port.lean` | timing モード (`sendTimingReq`, `sendRetryReq`, `sendTimingResp`) | プロトコルモニタ、lost-retry デッドロックが起きないことの証明、buggy responder の反例 |
| `RV32.lean` | ISA 定義 (`arch/riscv`) | RV32I (ワードの LW/SW のみ) のビット列デコーダ、ISA 仕様 `isaStep` |
| `SoC.lean` | `TimingSimpleCPU` + `NoncoherentXBar` + 2×`SimpleMemory` + Python config | TLM SoC と ISA への refinement 証明 |
| `SoCTest.lean` | `se.py` での実行 | Σ1..10 プログラムをレイテンシの異なる 3 構成で実行し、ISA 仕様と比較 |
| `NoC.lean` | Garnet mesh + `XY` routing | CDG 非巡回、デッドロック自由、ライブロック自由、最短経路、適応ルーティングの反例 |

## 主な定理

### Step 1: カーネル
- `step_wf` / `run_wf`: キューは時刻順で、すべて現在時刻以降 (不変条件) / シミュレーション時刻は単調
- `step_sound`: 実行可能な `step` は、非決定的な仕様 `Step` (「最小時刻のイベントを 1 つ配送」、キューは multiset として扱う) を実装する
- `step_progress`: 仕様でステップできるとき、実装も止まらない
- `Module.par_frame_left/right`: 合成した片方へのメッセージはもう片方の状態を変えない
- `Port.no_lost_retry`: 容量 `cap > 0` の responder と標準的な requestor では、**任意のスケジュール**でトレースがプロトコル合法。さらに requestor が blocked なら必ず retry 義務が立っていて、`serve` も実行可能
- `Port.buggy_stuck_forever`: retry 義務を記録しない responder では、以後どのスケジュールでも requestor が永久に blocked のまま (gem5 でよくあるハングの再現)

### Step 2: 最小 SoC
- `txnRead` / `txnWrite`: CPU→XBar→RAMᵢ→XBar のトランザクションを経ると、読み出し値はフラットメモリの値と一致し、書き込みはフラットメモリへの 1 ワード書き込みと一致する (アドレスマップによらない)
- `instr_refines`: 静止状態から 1 命令。ISA が停止しなければ、TLM SoC は有限ステップ (4 または 8 イベント) で次の静止状態に達し、アーキテクチャ状態とメモリが一致する。ISA が停止するなら SoC も停止状態に達する
- **`soc_refines_isa`**: k 命令についての refinement。**レイテンシ (`xbarLat`, `lat0`, `lat1`) とアドレスマップ `inR0` は任意**

### Step 3: NoC (W×H メッシュ、XY ルーティング)
- `next_rank` / `cdg_acyclic`: チャネルにランク関数を与え、依存辺に沿ってランクが狭義増加することを示す。これにより CDG が非巡回であることが言える (Dally–Seitz)
- **`progress`**: 合法で空でない網状態では、必ずどれかのフリットが前進または排出できる (デッドロック自由)
- `move_valid` / `inject_valid`: 合法性 (1 バッファ 1 フリットを含む) は保存される
- `drain`: 注入を止めると、空の網へ到達できる
- `moves_bounded`: どんな Move 列も長さは初期の距離和以下。つまりライブロックしない
- `stuck_is_empty`: 到達可能で、もう動けない状態は空だけ
- `route_minimal`: 1 ホップごとにマンハッタン距離が 1 減る
- `stepNet_sound` / `stepNet_none`: 実行可能なアービタは仕様の健全な実装で、合法状態では空のときにだけ止まる
- `adaptive_deadlock` / `cycle4_not_xy`: ターン制限のない最小適応ルーティングでは、2×2 で 4 フリットの循環待ちが合法に作れる。XY ルーティングでは同じ状態が不正になる

## モデル化の範囲と割り切り
- ISA 意味論 (`exec`, `decode`) は ISA 仕様と CPU モデルで共有しています。refinement が示しているのは、「ポート、イベントキュー、XBar のアドレス振り分け、分割メモリによる分散メモリ系がフラットメモリと等価であること」です。デコーダ自体の正しさ (RISC-V 仕様書との一致) は対象外で、Sail などとの突き合わせが別途必要です。
- CPU は outstanding が 1 の TimingSimpleCPU 相当です。XBar はリクエスタが 1 つなので、応答の経路表を持ちません。
- LB/LH/SB/SH、例外、CSR、キャッシュ、コヒーレンスは未対応です。
- NoC は store-and-forward で、チャネルごとに 1 フリットのバッファを持ちます。VC、クレジット、wormhole のフリット分割はありません。NoC は `Kernel` の Module としてはまだ包んでいません。

## 次の拡張候補
1. NoC を `Kernel.Module` (ルータ = SimObject) として実装し、`stepNet` との対応を証明する
2. TileRiscV (4×4 RV32IM) の TILE_SEND/TILE_RECV を、このメッシュ NoC の上に載せる
3. 複数リクエスタの XBar (応答ルーティングと公平性)
4. Sparkle の RTL 状態から TLM 状態への抽象化関数を定義し、RTL ⊑ TLM の refinement を示す
