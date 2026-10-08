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
| `RV32.lean` | ISA 定義 (`arch/riscv`) | RV32IM (ロード/ストアはワード単位のみ) のビット列デコーダ、ISA 仕様 `isaStep`、RISC-V の除算表のテスト |
| `SoC.lean` | `TimingSimpleCPU` + `NoncoherentXBar` + 2×`SimpleMemory` + Python config | TLM SoC と ISA への refinement 証明 |
| `SoCTest.lean` | `se.py` での実行 | Σ1..10 プログラムをレイテンシの異なる 3 構成で実行し、ISA 仕様と比較 |
| `NoC.lean` | Garnet mesh + `XY` routing | CDG 非巡回、デッドロック自由、ライブロック自由、最短経路、適応ルーティングの反例 |
| `Tile.lean` | TileRiscV (4×4 RV32IM + TILE_SEND/RECV) を SimObject 配列として | レジスタ方式の同期メッシュ仕様と、イベント駆動 TLM 実装の refinement |
| `Fast.lean` | — | 配列ベースの高速メッシュ (BitVec 版)、実装方式に依存しないメッシュ層 `TileImpl`、仕様・TLM との一致 |
| `Fast32.lean` | gem5 の decode cache 相当 | UInt32 + 事前デコードの高速版と、その正しさ |
| `FastTest.lean` | — | 高速版 (BitVec / UInt32 / 専用版 / 破壊的更新版) と仕様の毎サイクル比較 |
| `bench/` | — | ベンチマーク (Lean の exe と C の参照実装) |
| `TileTest.lean` | `se.py` 相当 | 1×4 リレー、1×2 ハザード、4×4 波面計算で、仕様と TLM を毎サイクル比較 |

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

### Step 4: TileRiscV のメッシュ (レジスタ方式)
仕様は RTL `TileRiscV.lean` と同じサイクル意味論です。
- `TILE_SEND dir, rs1` は `out[dir]` を上書きする
- `TILE_RECV rd, dir` は隣接コアの `out[opp dir]` を待たずに読む（端は 0）
- 全コアが同期して進む。SEND したサイクルの RECV は古い値を読み、次のサイクルから新しい値が見える

TLM 実装は、各タイルが隣の出力レジスタの**ローカルなミラー**を持ちます。SEND はリンク経由でミラー更新のメッセージを送り、他タイルの状態を直接は読みません。1 サイクルは 2 tick で、クロックを偶数 tick、リンク到着を奇数 tick にしています。これは gem5 のイベント priority と同じ役割です。

- `Module.array`: 同種モジュールの配列（gem5 の `VectorParam` 相当）
- `enqueue_mid` / `schedule_clk`: 同じ時刻帯のイベントがキューのどこに入るかの補題
- `phase1` / `phase2`: 1 サイクル分のクロックイベント処理と、リンク更新処理
- `mirror_after`: リンク処理後、全ミラーが次状態の隣接出力レジスタと一致する
- **`mesh_refines`**: 対称な隣接関係（`Topology`）なら何でも、k サイクル後の TLM 状態が仕様 `meshRun` と一致する（アーキ状態、dmem、出力レジスタ、停止フラグ、ミラーのすべて）
- `mesh4x4_refines`: 4×4 メッシュ（`meshTopo 4 4`、RTL と同じ N/S/E/W の向き）への具体化
- テスト: 1×4 のプレフィックス和リレー `[1,3,6,10]`、1×2 で同サイクルの RECV が 0 を読むハザード `(0, 7)`、4×4 の波面計算（二項係数）。いずれも仕様と TLM を毎サイクル比較して一致

**RTL について見つけた点**: `TileRiscV.lean` / `TileRiscV_Equiv.lean` の `mExtResult` は `rs1.toInt / rs2.toInt` と `%` を使っています。Lean の `Int` の `/` と `%` は Euclid 除算なので、`DIV -7, 2 = -4`、`REM -7, 2 = 1` となり、RISC-V 仕様（-3 と -1）と食い違います。`Int.tdiv` / `Int.tmod` に置き換えれば一致します（`TileTest.lean` で確認済み）。

### Step 5: 高速実行版 (証明つき)
仕様 `meshStep` は状態を関数で持つので、実行すると閉包が積み重なって遅くなります。同じ意味論を配列で実装し、抽象化関数を通して一致を証明しました。
- `TileImpl`: タイルの実装方式に依存しないインタフェース。条件は「抽象化すると `tileStep` と一致する」ことだけで、これを満たせばメッシュ層の証明（`fmeshStep_abs`、`fmeshRun_abs`）がそのまま通ります。
- **`fast_correct`**: 高速版を k サイクル回した結果は、(1) 仕様 `meshRun` と一致し、(2) `mesh_refines` と合わせるとイベント駆動 TLM とも一致する。
- BitVec 版 `bvImpl`（`fstep_abs`）: レジスタは `Array`、dmem は `HashMap`。
- UInt32 版 `u32Impl`（`step32_abs`）: 値は `UInt32` で、符号付き比較は `Int32`。命令は事前デコードしてキャッシュし（`fetch_eq`）、まれな演算（mulh 系、div/rem 系、sra）は仕様の関数にフォールバックします。
- `mesh32Step`: UInt32 版専用のステップ。一般版と `rfl` で等しいので、`TileImpl` 経由の間接呼び出しがありません。
- `fmeshStepFast`（破壊的更新版）: 一般版と等しいことは証明済みですが、実測では遅くなったので既定では使いません。

速度は 4×4 メッシュの波面プログラム、409 万命令で測りました（このクラウド VM、ネイティブ実行）。

| 実装 | MIPS（16 コア合計） |
|---|---|
| TLM（閉包のまま） | 約 0.01、O(n²) |
| TLM（状態を配列に詰め直す） | 約 0.2 |
| 高速版 BitVec | 0.2 |
| 高速版 UInt32（`TileImpl` 経由） | 8.7 |
| **高速版 UInt32 専用（`mesh32Step`）** | **9.3** |
| C の参照実装（`bench/mesh.c`） | 約 190 |
| 参考: gem5 AtomicSimpleCPU（公表値、別ホスト） | 約 1.3 |

## モデル化の範囲と割り切り
- ISA 意味論 (`exec`, `decode`) は ISA 仕様と CPU モデルで共有しています。refinement が示しているのは、「ポート、イベントキュー、XBar のアドレス振り分け、分割メモリによる分散メモリ系がフラットメモリと等価であること」です。デコーダ自体の正しさ (RISC-V 仕様書との一致) は対象外で、Sail などとの突き合わせが別途必要です。
- Tile のメッシュはレジスタ方式（RTL と同じ）です。RECV が送信を待たないので、プログラムの正しさは SEND と RECV のタイミング次第です。`TileTiming.lean` は `blockingRecv` で送信を待つモデルになっており、RTL とは意味が異なります。
- Tile の dmem/imem はアドレスで直接引く関数で、RTL の `% dMemSize` による折り返しはモデル化していません。
- CPU は outstanding が 1 の TimingSimpleCPU 相当です。XBar はリクエスタが 1 つなので、応答の経路表を持ちません。
- LB/LH/SB/SH、例外、CSR、キャッシュ、コヒーレンスは未対応です。
- NoC は store-and-forward で、チャネルごとに 1 フリットのバッファを持ちます。VC、クレジット、wormhole のフリット分割はありません。NoC は `Kernel` の Module としてはまだ包んでいません。

## 次の拡張候補
1. FIFO 方式の TILE_SEND/RECV（受信を待つ + クレジット制御）を NoC 上に載せ、Kahn の決定性を証明する
2. リンク遅延を一般の L にし、仕様側で「L サイクル前の値を読む」形に一般化する
3. 複数リクエスタの XBar (応答ルーティングと公平性)
4. Sparkle の RTL 状態から TLM 状態への抽象化関数を定義し、RTL ⊑ TLM の refinement を示す
