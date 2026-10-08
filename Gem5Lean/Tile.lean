import Gem5Lean.Kernel
import Gem5Lean.RV32
import Gem5Lean.NoC

/-!
# Gem5Lean.Tile — TileRiscV (TILE_SEND / TILE_RECV, レジスタ方式) を TLM メッシュに載せる

## 仕様 (RTL `TileRiscV.lean` のサイクル意味論)

* 各コアは方向ごとの出力レジスタ `out : Dir → Word` を持つ
* `TILE_SEND dir, rs1` : `out[dir] ← rs1` (上書き)
* `TILE_RECV rd, dir`  : `rd ← neighbor[dir].out[opp dir]` (待たない。端は 0)
* 全コアが同期して 1 サイクル進む。RECV が見るのは **前サイクル末** のレジスタ値
  (SEND in cycle T は RECV in cycle T+1 から見える)

これを `meshStep` として定義する (`Topology` は対称な隣接関係なら何でもよい)。

## 実装 (gem5 風 TLM)

* タイル = `Module`。状態は自コアの状態 + 隣接出力レジスタの **ローカルなミラー** `mirror`
* クロック: 自分で 2 tick ごとに `clk` イベントを再スケジュール (1 サイクル = 2 tick)
* SEND は、リンク経由で隣のタイルへ「レジスタ更新メッセージ」を送る (遅延 1 tick)
* RECV は自分のミラーを読むだけ。他タイルの状態は **一切直接読まない**
* 全タイルは `Module.array` で合成し、`System.wire` で隣接リンクを配線する

半 tick ずらす (クロック = 偶数 tick、リンク到着 = 奇数 tick) のは、
gem5 でクロックエッジのイベントとリンク到着イベントに priority を付けるのと同じ役割。

## 主定理

`mesh_refines`: k サイクル後の TLM 状態は、すべてのタイルについて
仕様の状態 + 「ミラー = 隣接タイルの実際の出力レジスタ」と一致する。
-/

namespace Gem5
open Gem5.RV32
open Gem5.NoC (Dir)

/-! ## 同種モジュールの配列 (gem5 の `VectorParam` / `cpu = [TimingSimpleCPU() for …]`) -/

@[reducible] def Module.array (ι : Type) [DecidableEq ι] {M I O S : Type} (init : ι → S)
    (h : I → M → S → S × List (Nat × O × M)) : Module M where
  I := ι × I
  O := ι × O
  State := ι → S
  init := init
  handle p m st :=
    let r := h p.2 m (st p.1)
    (fun j => if j = p.1 then r.1 else st j, mapOuts (fun o => (p.1, o)) r.2)

theorem enqueue_mid {P M : Type} (e : Event P M) :
    ∀ (A B : List (Event P M)), (∀ x ∈ A, x.time ≤ e.time) → (∀ x ∈ B, e.time < x.time) →
      enqueue e (A ++ B) = A ++ e :: B
  | [], [], _, _ => rfl
  | [], b :: bs, _, hB => by simp [enqueue, hB b (by simp)]
  | a :: as, B, hA, hB => by
    have ha := hA a (by simp)
    have : ¬ e.time < a.time := Nat.not_lt.mpr ha
    simp only [List.cons_append, enqueue, this, if_false]
    rw [enqueue_mid e as B (fun x hx => hA x (by simp [hx])) hB]

end Gem5

namespace Gem5.Tile
open Gem5 Gem5.RV32
open Gem5.NoC (Dir)

def _root_.Gem5.NoC.Dir.opp : Dir → Dir
  | .N => .S | .S => .N | .E => .W | .W => .E

@[simp] theorem _root_.Gem5.NoC.Dir.opp_opp (d : Dir) : d.opp.opp = d := by cases d <;> rfl

theorem _root_.Gem5.NoC.Dir.opp_inj {d e : Dir} (h : d.opp = e.opp) : d = e := by
  cases d <;> cases e <;> simp_all [Gem5.NoC.Dir.opp]

def upd {α : Type} (f : Dir → α) (d : Dir) (v : α) : Dir → α := fun e => if e = d then v else f e

/-! ## ISA 拡張: CUSTOM-0 (opcode 0x0B) -/

/-- RTL のエンコーディング: funct3[1:0] = 0:N 1:S 2:E 3:W -/
def dirOfBits (b : Nat) : Dir :=
  match b % 4 with
  | 0 => .N | 1 => .S | 2 => .E | _ => .W

inductive TInstr
  | base (i : Instr)
  | send (d : Dir) (rs1 : Reg)
  | recv (rd : Reg) (d : Dir)

/-- funct7[0] = 1 が SEND、0 が RECV -/
def tdecode (w : Word) : TInstr :=
  if (w.extractLsb' 0 7).toNat = 0x0B then
    let d := dirOfBits (w.extractLsb' 12 3).toNat
    if (w.extractLsb' 25 1).toNat = 1 then .send d (w.extractLsb' 15 5)
    else .recv (w.extractLsb' 7 5) d
  else .base (decode w)

/-! ## 1 コアの状態と 1 サイクル -/

structure Tile where
  arch   : Arch
  imem   : Mem
  dmem   : Mem
  out    : Dir → Word
  halted : Bool

/-- 1 サイクル実行。`inp d` は方向 d の隣接コアの (前サイクル末の) 出力レジスタ。
第 2 成分は TILE_SEND した (方向, 値)。 -/
def tileStep (t : Tile) (inp : Dir → Word) : Tile × Option (Dir × Word) :=
  if t.halted then (t, none) else
  match tdecode (t.imem t.arch.pc) with
  | .send d rs1 =>
    let v := t.arch.get rs1
    ({ t with out := upd t.out d v, arch := { t.arch with pc := t.arch.pc + 4 } }, some (d, v))
  | .recv rd d =>
    ({ t with arch := { t.arch.set rd (inp d) with pc := t.arch.pc + 4 } }, none)
  | .base i =>
    match exec i t.arch with
    | none => ({ t with halted := true }, none)
    | some (a', .none) => ({ t with arch := a' }, none)
    | some (a', .load rd addr) => ({ t with arch := a'.set rd (t.dmem addr) }, none)
    | some (a', .store addr v) => ({ t with arch := a', dmem := t.dmem.write addr v }, none)

theorem tileStep_halted {t : Tile} (h : t.halted = true) (inp) : tileStep t inp = (t, none) := by
  simp [tileStep, h]

/-- 出力レジスタは SEND した方向だけが変わる -/
theorem tileStep_out (t : Tile) (inp : Dir → Word) :
    (tileStep t inp).1.out =
      match (tileStep t inp).2 with
      | some (d, v) => upd t.out d v
      | none => t.out := by
  unfold tileStep
  split
  · rfl
  · split
    · rfl
    · rfl
    · split <;> rfl

theorem tileStep_halted_mono {t : Tile} (inp) (h : t.halted = true) : (tileStep t inp).1.halted = true := by
  rw [tileStep_halted h]; exact h

theorem tileStep_send_not_halted {t : Tile} {inp} {d v} (h : (tileStep t inp).2 = some (d, v)) :
    t.halted = false := by
  cases hh : t.halted
  · rfl
  · rw [tileStep_halted hh] at h; cases h

/-! ## 仕様: 同期メッシュ -/

/-- 対称な隣接関係 (2D メッシュ、トーラス等) -/
structure Topology (ι : Type) where
  nbr  : ι → Dir → Option ι
  symm : ∀ i d j, nbr i d = some j → nbr j d.opp = some i

variable {ι : Type} [DecidableEq ι]

/-- コア i の方向 d の入力 = 隣接コアの反対方向の出力レジスタ (端は 0) -/
def nbrOut (T : Topology ι) (s : ι → Tile) (i : ι) (d : Dir) : Word :=
  match T.nbr i d with
  | some j => (s j).out d.opp
  | none => 0

/-- **仕様**: 全コアが前サイクル末の値を見て同時に 1 サイクル進む -/
def meshStep (T : Topology ι) (s : ι → Tile) : ι → Tile :=
  fun i => (tileStep (s i) (nbrOut T s i)).1

def meshRun (T : Topology ι) : Nat → (ι → Tile) → (ι → Tile)
  | 0, s => s
  | k + 1, s => meshRun T k (meshStep T s)

/-! ## 実装: TLM タイル -/

inductive TIn | clk | link (d : Dir) | sink
  deriving DecidableEq

inductive TOut | clk | link (d : Dir)
  deriving DecidableEq

structure TileI where
  tile   : Tile
  mirror : Dir → Word

theorem TileI.ext' {a b : TileI} (h1 : a.tile = b.tile) (h2 : a.mirror = b.mirror) : a = b := by
  cases a; cases b; simp_all

def clkOuts (r : Tile × Option (Dir × Word)) : List (Nat × TOut × Word) :=
  (match r.2 with
   | some (d, v) => [(1, .link d, v)]
   | none => []) ++
  (if r.1.halted then [] else [(2, .clk, 0)])

/-- タイルのハンドラ: クロックで 1 命令、リンクでミラー更新。他タイルの状態は読まない -/
def tileHandle : TIn → Word → TileI → TileI × List (Nat × TOut × Word)
  | .clk, _, s => let r := tileStep s.tile s.mirror; (⟨r.1, s.mirror⟩, clkOuts r)
  | .link d, v, s => (⟨s.tile, upd s.mirror d v⟩, [])
  | .sink, _, s => (s, [])

def dummyTile : TileI := ⟨⟨⟨0, fun _ => 0⟩, fun _ => 0, fun _ => 0, fun _ => 0, true⟩, fun _ => 0⟩

/-- 配線: SEND 方向 d のリンク → 隣接タイルの「反対方向」ミラー。端は sink -/
def meshWire (T : Topology ι) : ι × TOut → ι × TIn
  | (i, .clk) => (i, .clk)
  | (i, .link d) =>
    match T.nbr i d with
    | some j => (j, .link d.opp)
    | none => (i, .sink)

abbrev meshSys (T : Topology ι) : System Word where
  mod := Module.array ι (fun _ => dummyTile) tileHandle
  wire := meshWire T

abbrev Ev (T : Topology ι) := Event (meshSys T).mod.I Word

def implOf (T : Topology ι) (s : ι → Tile) : ι → TileI := fun i => ⟨s i, nbrOut T s i⟩

def clkEv (T : Topology ι) (t : Nat) (i : ι) : Ev T := ⟨t, (i, .clk), 0⟩

def clkEvs (T : Topology ι) (t : Nat) (s : ι → Tile) (l : List ι) : List (Ev T) :=
  (l.filter fun i => !(s i).halted).map (clkEv T t)

/-- 対応関係: 時刻 2c の直前 (クロックイベントのみがキューにある) で、
TLM 状態 = 仕様状態 + 正しいミラー -/
def Rel (T : Topology ι) (tiles : List ι) (c : Nat) (s : ι → Tile) (σ : SimState (meshSys T)) : Prop :=
  σ.st = implOf T s ∧ σ.queue = clkEvs T (2 * c) s tiles ∧ σ.now ≤ 2 * c

def initSim (T : Topology ι) (tiles : List ι) (s0 : ι → Tile) : SimState (meshSys T) :=
  ⟨0, clkEvs T 0 s0 tiles, implOf T s0⟩

theorem init_rel (T : Topology ι) (tiles : List ι) (s0 : ι → Tile) : Rel T tiles 0 s0 (initSim T tiles s0) :=
  ⟨rfl, rfl, Nat.le_refl _⟩

/-! ## 証明 -/

section proofs
variable (T : Topology ι)

def postTile (s : ι → Tile) (i : ι) : Tile × Option (Dir × Word) := tileStep (s i) (nbrOut T s i)

/-- タイル i が今サイクルに出すリンクイベント -/
def sendEvs (c : Nat) (s : ι → Tile) (i : ι) : List (Ev T) :=
  match (postTile T s i).2 with
  | some (d, v) => [⟨2 * c + 1, meshWire T (i, .link d), v⟩]
  | none => []

/-- タイル i の次のクロックイベント (停止していなければ) -/
def clkEv2 (c : Nat) (s : ι → Tile) (i : ι) : List (Ev T) :=
  if (postTile T s i).1.halted then [] else [clkEv T (2 * c + 2) i]

theorem enqueue_end (e : Ev T) (Q : List (Ev T)) (h : ∀ x ∈ Q, x.time ≤ e.time) :
    enqueue e Q = Q ++ [e] := by
  have := enqueue_mid e Q [] h (by simp)
  simpa using this

/-- クロックハンドラの出力をキューへ入れると、リンクイベントは「リンク群の末尾」、
クロックイベントは「次サイクル群の末尾」に入る -/
theorem schedule_clk (c : Nat) (s : ι → Tile) (i : ι) (A L K : List (Ev T))
    (hA : ∀ x ∈ A, x.time ≤ 2 * c) (hL : ∀ x ∈ L, x.time = 2 * c + 1) (hK : ∀ x ∈ K, x.time = 2 * c + 2) :
    schedule (meshSys T) (2 * c) (mapOuts (fun o => (i, o)) (clkOuts (postTile T s i))) (A ++ (L ++ K)) =
      A ++ ((L ++ sendEvs T c s i) ++ (K ++ clkEv2 T c s i)) := by
  have e1 : ∀ e : Ev T, e.time = 2 * c + 1 → enqueue e (A ++ (L ++ K)) = A ++ ((L ++ [e]) ++ K) := by
    intro e he
    rw [← List.append_assoc, enqueue_mid e (A ++ L) K]
    · simp
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hA x hx; omega
      · have := hL x hx; omega
    · intro x hx; have := hK x hx; omega
  have hle : ∀ x ∈ A ++ (L ++ K), x.time ≤ 2 * c + 2 := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx | hx
    · have := hA x hx; omega
    · have := hL x hx; omega
    · have := hK x hx; omega
  have hle2 : ∀ e : Ev T, e.time = 2 * c + 1 → ∀ x ∈ A ++ ((L ++ [e]) ++ K), x.time ≤ 2 * c + 2 := by
    intro e he x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | (hx | hx) | hx
    · have := hA x hx; omega
    · have := hL x hx; omega
    · subst hx; omega
    · have := hK x hx; omega
  unfold sendEvs clkEv2 clkOuts
  rcases h2 : (postTile T s i).2 with _ | ⟨d, v⟩ <;>
    rcases h1 : (postTile T s i).1.halted with _ | _ <;>
    simp only [List.nil_append, List.append_nil, mapOuts, List.map, schedule, mkEv, meshWire,
      if_true, if_false, Bool.false_eq_true, List.cons_append]
  all_goals first
    | (rw [e1 _ rfl]; done)
    | (rw [e1 _ rfl, enqueue_end T _ _ (hle2 _ rfl)]; simp [clkEv])
    | (rw [enqueue_end T _ _ hle]; simp [clkEv])

theorem run_succ {M} {S : System M} {s s' : SimState S} (n : Nat) (h : step s = some s') :
    run (n + 1) s = run n s' := by
  simp [run, h]

/-- **Phase 1**: 時刻 2c のクロックイベントを (リスト p の順に) 全部処理する -/
theorem phase1 (c : Nat) (s : ι → Tile) :
    ∀ (p : List ι) (now : Nat) (st : ι → TileI) (L K : List (Ev T)),
      p.Nodup → (∀ i ∈ p, st i = implOf T s i) →
      now ≤ 2 * c + 1 →
      (∀ e ∈ L, e.time = 2 * c + 1) → (∀ e ∈ K, e.time = 2 * c + 2) →
      ∃ now', now' ≤ 2 * c + 1 ∧
        run p.length (⟨now, p.map (clkEv T (2 * c)) ++ (L ++ K), st⟩ : SimState (meshSys T)) =
          ⟨now', L ++ p.flatMap (sendEvs T c s) ++ (K ++ p.flatMap (clkEv2 T c s)),
            fun j => if j ∈ p then ⟨(postTile T s j).1, (st j).mirror⟩ else st j⟩
  | [], now, st, L, K, _, _, hn, _, _ =>
    ⟨now, hn, by simp [run]⟩
  | i :: rest, now, st, L, K, hnd, hst, hn, hL, hK => by
    rw [List.nodup_cons] at hnd
    have hsi := hst i (by simp)
    -- 1 ステップ: タイル i のクロック
    have hstep : step (⟨now, (i :: rest).map (clkEv T (2 * c)) ++ (L ++ K), st⟩ : SimState (meshSys T)) =
        some ⟨2 * c, rest.map (clkEv T (2 * c)) ++ ((L ++ sendEvs T c s i) ++ (K ++ clkEv2 T c s i)),
          fun j => if j = i then ⟨(postTile T s i).1, (st i).mirror⟩ else st j⟩ := by
      simp only [step, List.map_cons, List.cons_append]
      congr 2
      · rw [← schedule_clk T c s i (rest.map (clkEv T (2 * c))) L K
          (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; simp [clkEv]) hL hK]
        simp only [clkEv, Module.array, tileHandle, hsi, implOf, postTile]
      · funext j
        simp only [clkEv, Module.array, tileHandle, hsi, implOf, postTile]
    rw [List.length_cons, run_succ _ hstep]
    obtain ⟨now', hn', hrun⟩ := phase1 c s rest (2 * c)
      (fun j => if j = i then ⟨(postTile T s i).1, (st i).mirror⟩ else st j)
      (L ++ sendEvs T c s i) (K ++ clkEv2 T c s i)
      hnd.2 (by
        intro j hj
        have : j ≠ i := fun h => hnd.1 (h ▸ hj)
        simp only [this, if_false, ite_false]; exact hst j (by simp [hj]))
      (by omega)
      (by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hL e he
        · unfold sendEvs at he; split at he <;> simp_all)
      (by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hK e he
        · unfold clkEv2 at he; split at he <;> simp_all [clkEv])
    refine ⟨now', hn', ?_⟩
    rw [hrun]
    congr 1
    · simp [List.flatMap_cons, List.append_assoc]
    · funext j
      by_cases hj : j ∈ rest
      · have : j ≠ i := fun h => hnd.1 (h ▸ hj)
        simp [hj, this]
      · by_cases hji : j = i
        · subst hji; simp [hj]
        · simp [hj, hji]

/-- リンク/シンクのイベントはミラーしか変えず、出力もない -/
def Silent (e : Ev T) : Prop := e.port.2 ≠ .clk

def applyEvs (L : List (Ev T)) (st : ι → TileI) : ι → TileI :=
  L.foldl (fun st e => ((meshSys T).mod.handle e.port e.msg st).1) st

theorem silent_outs {e : Ev T} (h : Silent T e) (st : ι → TileI) :
    ((meshSys T).mod.handle e.port e.msg st).2 = [] := by
  obtain ⟨_, ⟨i, p⟩, m⟩ := e
  cases p with
  | clk => exact absurd rfl h
  | link d => rfl
  | sink => rfl

/-- **Phase 2**: リンクイベントを全部処理する -/
theorem phase2 : ∀ (L Q : List (Ev T)) (now : Nat) (st : ι → TileI), (∀ e ∈ L, Silent T e) →
    (∀ e ∈ L, e.time ≤ 2 * c + 1) → now ≤ 2 * c + 1 →
    ∃ now', now' ≤ 2 * c + 1 ∧
      run L.length (⟨now, L ++ Q, st⟩ : SimState (meshSys T)) = ⟨now', Q, applyEvs T L st⟩
  | [], Q, now, st, _, _, hn => ⟨now, hn, by simp [run, applyEvs]⟩
  | e :: L, Q, now, st, hs, ht, _ => by
    have hstep : step (⟨now, (e :: L) ++ Q, st⟩ : SimState (meshSys T)) =
        some ⟨e.time, L ++ Q, ((meshSys T).mod.handle e.port e.msg st).1⟩ := by
      have h0 := silent_outs T (hs e (by simp)) st
      simp only [Module.array] at h0
      simp only [step, List.cons_append, h0, schedule]
    rw [List.length_cons, run_succ _ hstep]
    obtain ⟨now', hn', h⟩ := phase2 L Q e.time _ (fun x hx => hs x (by simp [hx]))
      (fun x hx => ht x (by simp [hx])) (ht e (by simp))
    exact ⟨now', hn', by rw [h]; rfl⟩

theorem applyEvs_cons (e : Ev T) (L : List (Ev T)) (st : ι → TileI) :
    applyEvs T (e :: L) st = applyEvs T L ((meshSys T).mod.handle e.port e.msg st).1 := rfl

theorem handle_tile {e : Ev T} (h : Silent T e) (st : ι → TileI) (j : ι) :
    (((meshSys T).mod.handle e.port e.msg st).1 j).tile = (st j).tile := by
  obtain ⟨_, ⟨i, p⟩, m⟩ := e
  cases p with
  | clk => exact absurd rfl h
  | link d => simp only [Module.array, tileHandle]; split <;> simp_all
  | sink => simp only [Module.array, tileHandle]; split <;> simp_all

theorem applyEvs_tile : ∀ (L : List (Ev T)) (st : ι → TileI) (j : ι), (∀ e ∈ L, Silent T e) →
    (applyEvs T L st j).tile = (st j).tile
  | [], _, _, _ => rfl
  | e :: L, st, j, hs => by
    rw [applyEvs_cons, applyEvs_tile L _ j (fun x hx => hs x (by simp [hx])),
      handle_tile T (hs e (by simp))]

theorem handle_mirror_other {e : Ev T} (st : ι → TileI) (j : ι) (d : Dir)
    (h : e.port ≠ (j, .link d)) (hs : Silent T e) :
    (((meshSys T).mod.handle e.port e.msg st).1 j).mirror d = (st j).mirror d := by
  obtain ⟨_, ⟨i, p⟩, m⟩ := e
  cases p with
  | clk => exact absurd rfl hs
  | sink => simp only [Module.array, tileHandle]; split <;> simp_all
  | link d' =>
    simp only [Module.array, tileHandle]
    split
    · rename_i hji
      subst hji
      have : d ≠ d' := fun hd => h (by subst hd; rfl)
      simp [upd, this]
    · rfl

theorem handle_mirror_hit {e : Ev T} (st : ι → TileI) (j : ι) (d : Dir) (h : e.port = (j, .link d)) :
    (((meshSys T).mod.handle e.port e.msg st).1 j).mirror d = e.msg := by
  obtain ⟨_, p, m⟩ := e
  simp only at h
  subst h
  simp [Module.array, tileHandle, upd]

theorem applyEvs_nohit : ∀ (L : List (Ev T)) (st : ι → TileI) (j : ι) (d : Dir),
    (∀ e ∈ L, Silent T e) → (∀ e ∈ L, e.port ≠ (j, .link d)) →
    (applyEvs T L st j).mirror d = (st j).mirror d
  | [], _, _, _, _, _ => rfl
  | e :: L, st, j, d, hs, hp => by
    rw [applyEvs_cons, applyEvs_nohit L _ j d (fun x hx => hs x (by simp [hx]))
      (fun x hx => hp x (by simp [hx])),
      handle_mirror_other T st j d (hp e (by simp)) (hs e (by simp))]

theorem applyEvs_hit : ∀ (L : List (Ev T)) (st : ι → TileI) (j : ι) (d : Dir) (x : Ev T),
    (∀ e ∈ L, Silent T e) → x ∈ L → x.port = (j, .link d) →
    (∀ y ∈ L, y.port = (j, .link d) → y = x) →
    (applyEvs T L st j).mirror d = x.msg
  | [], _, _, _, _, _, hx, _, _ => by simp at hx
  | e :: L, st, j, d, x, hs, hx, hxp, huniq => by
    rw [applyEvs_cons]
    by_cases hxL : x ∈ L
    · exact applyEvs_hit L _ j d x (fun y hy => hs y (by simp [hy])) hxL hxp
        (fun y hy => huniq y (by simp [hy]))
    · have hex : e = x := by
        rcases List.mem_cons.mp hx with h | h
        · exact h.symm
        · exact absurd h hxL
      subst hex
      rw [applyEvs_nohit T L _ j d (fun y hy => hs y (by simp [hy]))]
      · exact handle_mirror_hit T st j d hxp
      · intro y hy hyp
        exact hxL (huniq y (by simp [hy]) hyp ▸ hy)

/-! ### リンクイベントの特徴付け -/

theorem meshWire_link {i j : ι} {d e : Dir} (h : meshWire T (i, .link d) = (j, .link e)) :
    T.nbr i d = some j ∧ e = d.opp := by
  simp only [meshWire] at h
  split at h
  · rename_i j' hj'; simp only [Prod.mk.injEq, TIn.link.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hj', rfl⟩
  · simp at h

theorem mem_sendEvs {c : Nat} {s : ι → Tile} {i : ι} {x : Ev T} (h : x ∈ sendEvs T c s i) :
    ∃ d v, (postTile T s i).2 = some (d, v) ∧ x = ⟨2 * c + 1, meshWire T (i, .link d), v⟩ := by
  unfold sendEvs at h
  split at h
  · rename_i d v hdv; simp at h; exact ⟨d, v, hdv, h⟩
  · simp at h

theorem sendEvs_silent {c : Nat} {s : ι → Tile} {i : ι} {x : Ev T} (h : x ∈ sendEvs T c s i) :
    Silent T x := by
  obtain ⟨d, v, -, rfl⟩ := mem_sendEvs T h
  simp only [Silent, meshWire]
  split <;> simp

/-- 今サイクルのミラー更新が終わると、ミラーは仕様の次状態での隣接出力と一致する -/
theorem mirror_after (c : Nat) (s : ι → Tile) (tiles : List ι) (hall : ∀ i, i ∈ tiles)
    (st : ι → TileI) (hst : ∀ j, (st j).mirror = nbrOut T s j) (j : ι) (d : Dir) :
    let P := tiles.filter fun i => !(s i).halted
    (applyEvs T (P.flatMap (sendEvs T c s)) st j).mirror d = nbrOut T (meshStep T s) j d := by
  intro P
  have hsil : ∀ e ∈ P.flatMap (sendEvs T c s), Silent T e := by
    intro e he
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp he
    exact sendEvs_silent T hi
  -- (j, link d) を宛先とするイベントの送り主は nbr j d に限る
  have hsrc : ∀ e ∈ P.flatMap (sendEvs T c s), e.port = (j, .link d) →
      ∃ i dd v, T.nbr j d = some i ∧ dd = d.opp ∧ (postTile T s i).2 = some (dd, v) ∧
        e = ⟨2 * c + 1, (j, .link d), v⟩ := by
    intro e he hp
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp he
    obtain ⟨dd, v, hdv, rfl⟩ := mem_sendEvs T hi
    simp only at hp
    obtain ⟨hn, hdd⟩ := meshWire_link T hp
    have hdd' : dd = d.opp := by rw [hdd]; simp
    refine ⟨i, dd, v, ?_, hdd', hdv, ?_⟩
    · have := T.symm i dd j hn; rw [hdd'] at this; simpa using this
    · simp only [hp]
  simp only [nbrOut, meshStep]
  cases hn : T.nbr j d with
  | none =>
    rw [applyEvs_nohit T _ st j d hsil, hst j]
    · simp [nbrOut, hn]
    · intro e he hp
      obtain ⟨i, -, -, hn', -⟩ := hsrc e he hp
      rw [hn] at hn'; cases hn'
  | some i =>
    have hrev : T.nbr i d.opp = some j := T.symm j d i hn
    have hout := tileStep_out (s i) (nbrOut T s i)
    rcases hpi : (postTile T s i).2 with _ | ⟨dd, v⟩
    · -- i は今サイクル SEND していない
      rw [applyEvs_nohit T _ st j d hsil, hst j]
      · simp only [nbrOut, hn]
        try simp only [postTile] at hpi
        rw [hout, hpi]
      · intro e he hp
        obtain ⟨i', _, _, hn', rfl, hv, -⟩ := hsrc e he hp
        rw [hn] at hn'; cases hn'; rw [hpi] at hv; cases hv
    · by_cases hdd : dd = d.opp
      · -- i が d.opp 方向に SEND した: ミラーはその値
        subst hdd
        have hP : i ∈ P := by
          simp only [P, List.mem_filter]
          refine ⟨hall i, ?_⟩
          simp [tileStep_send_not_halted (by try simp only [postTile] at hpi; exact hpi)]
        have hx : (⟨2 * c + 1, (j, .link d), v⟩ : Ev T) ∈ P.flatMap (sendEvs T c s) := by
          refine List.mem_flatMap.mpr ⟨i, hP, ?_⟩
          simp only [sendEvs, hpi, meshWire, hrev, Gem5.NoC.Dir.opp_opp, List.mem_singleton]
        rw [applyEvs_hit T _ st j d _ hsil hx rfl]
        · try simp only [postTile] at hpi
          show v = (tileStep (s i) (nbrOut T s i)).1.out d.opp
          rw [hout, hpi]; simp [upd]
        · intro y hy hyp
          obtain ⟨i', _, v', hn', rfl, hv, rfl⟩ := hsrc y hy hyp
          rw [hn] at hn'; cases hn'; rw [hpi] at hv; cases hv; rfl
      · -- 別方向に SEND した: この方向の値は不変
        rw [applyEvs_nohit T _ st j d hsil, hst j]
        · simp only [nbrOut, hn]
          try simp only [postTile] at hpi
          rw [hout, hpi]; simp [upd, Ne.symm hdd]
        · intro e he hp
          obtain ⟨i', _, _, hn', rfl, hv, -⟩ := hsrc e he hp
          rw [hn] at hn'; cases hn'; rw [hpi] at hv; cases hv; exact hdd rfl

theorem filter_halted (s : ι → Tile) (l : List ι) :
    (l.filter fun i => !(s i).halted).flatMap (clkEv2 T c s) =
      clkEvs T (2 * (c + 1)) (meshStep T s) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.filter_cons, clkEvs] at ih ⊢
    by_cases hh : (s i).halted = true
    · have : (meshStep T s i).halted = true := tileStep_halted_mono _ hh
      simp [hh, this, ih]
    · have hh' : (s i).halted = false := by simpa using hh
      simp only [hh', Bool.not_false, if_true, List.flatMap_cons, ih, clkEv2, postTile]
      by_cases hm : (tileStep (s i) (nbrOut T s i)).1.halted = true
      · simp [hm, meshStep]
      · have hm' : (tileStep (s i) (nbrOut T s i)).1.halted = false := by simpa using hm
        simp [hm', meshStep, clkEv, show 2 * c + 2 = 2 * (c + 1) by omega]

/-- **1 サイクルの refinement**: 対応関係 `Rel` は 1 サイクル分の TLM 実行で保存される -/
theorem mesh_step_refines (tiles : List ι) (hnd : tiles.Nodup) (hall : ∀ i, i ∈ tiles)
    (c : Nat) (s : ι → Tile) (σ : SimState (meshSys T)) (hr : Rel T tiles c s σ) :
    ∃ n, Rel T tiles (c + 1) (meshStep T s) (run n σ) := by
  obtain ⟨hst, hq, hn⟩ := hr
  let P := tiles.filter fun i => !(s i).halted
  have hPnd : P.Nodup := by
    have := List.nodup_iff_pairwise_ne.mp hnd
    exact List.nodup_iff_pairwise_ne.mpr (this.filter _)
  obtain ⟨σ', hσ⟩ : ∃ σ' : SimState (meshSys T), σ = σ' := ⟨σ, rfl⟩
  obtain ⟨now, q, st⟩ := σ'
  subst hσ
  simp only at hst hq hn
  subst hst; subst hq
  -- Phase 1
  obtain ⟨t1, ht1, h1⟩ := phase1 T c s P now (implOf T s) [] [] hPnd (fun _ _ => rfl) (by omega)
    (by simp) (by simp)
  have hq0 : clkEvs T (2 * c) s tiles = P.map (clkEv T (2 * c)) ++ ([] ++ []) := by simp [clkEvs, P]
  -- Phase 2
  let st1 : ι → TileI := fun j => if j ∈ P then ⟨(postTile T s j).1, (implOf T s j).mirror⟩ else implOf T s j
  have hsilAll : ∀ e ∈ P.flatMap (sendEvs T c s), Silent T e := by
    intro e he
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp he
    exact sendEvs_silent T hi
  have htAll : ∀ e ∈ P.flatMap (sendEvs T c s), e.time ≤ 2 * c + 1 := by
    intro e he
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp he
    obtain ⟨d, v, -, rfl⟩ := mem_sendEvs T hi
    simp
  obtain ⟨t2, ht2, h2⟩ := phase2 T (c := c) (P.flatMap (sendEvs T c s)) (P.flatMap (clkEv2 T c s)) t1 st1
    hsilAll htAll ht1
  refine ⟨P.length + (P.flatMap (sendEvs T c s)).length, ?_⟩
  rw [run_add, hq0, h1]
  simp only [List.nil_append] at h2 ⊢
  rw [h2]
  refine ⟨?_, filter_halted T s tiles, show t2 ≤ 2 * (c + 1) by omega⟩
  -- 状態の一致
  funext j
  apply TileI.ext'
  · rw [applyEvs_tile T _ _ j hsilAll]
    simp only [st1, implOf, meshStep]
    split
    · rfl
    · rename_i hj
      have : (s j).halted = true := by
        simp only [P, List.mem_filter, hall j, true_and] at hj; simpa using hj
      rw [tileStep_halted this]
  · funext d
    have := mirror_after T c s tiles hall st1 (by intro k; simp only [st1]; split <;> rfl) j d
    simp only at this
    rw [this]; rfl

/-- **主定理 (k サイクル refinement)**: 初期状態から k サイクル分の TLM 実行で、
全タイルの状態が仕様 `meshRun` と一致し、ミラーも正しい -/
theorem mesh_refines (tiles : List ι) (hnd : tiles.Nodup) (hall : ∀ i, i ∈ tiles) :
    ∀ (k c : Nat) (s : ι → Tile) (σ : SimState (meshSys T)), Rel T tiles c s σ →
      ∃ n, Rel T tiles (c + k) (meshRun T k s) (run n σ)
  | 0, c, s, σ, h => ⟨0, h⟩
  | k + 1, c, s, σ, h => by
    obtain ⟨n1, h1⟩ := mesh_step_refines T tiles hnd hall c s σ h
    obtain ⟨n2, h2⟩ := mesh_refines tiles hnd hall k (c + 1) (meshStep T s) _ h1
    refine ⟨n1 + n2, ?_⟩
    rw [run_add, show c + (k + 1) = c + 1 + k by omega]
    exact h2

/-- 系: 各タイルのアーキテクチャ状態 (レジスタ、PC、dmem、出力レジスタ、停止フラグ) は仕様と一致 -/
theorem mesh_refines_init (tiles : List ι) (hnd : tiles.Nodup) (hall : ∀ i, i ∈ tiles)
    (s0 : ι → Tile) (k : Nat) :
    ∃ n, ∀ i, ((run n (initSim T tiles s0)).st i).tile = meshRun T k s0 i := by
  obtain ⟨n, h, -, -⟩ := mesh_refines T tiles hnd hall k 0 s0 _ (init_rel T tiles s0)
  exact ⟨n, fun i => by rw [h]; rfl⟩

end proofs

/-! ## 具体的なトポロジ: R 行 × C 列メッシュ (RTL と同じく N = 行 −1, S = 行 +1, W = 列 −1, E = 列 +1) -/

def meshNbr (R C : Nat) : Fin R × Fin C → Dir → Option (Fin R × Fin C)
  | (r, c), .N => if h : 0 < r.val then some (⟨r.val - 1, by omega⟩, c) else none
  | (r, c), .S => if h : r.val + 1 < R then some (⟨r.val + 1, h⟩, c) else none
  | (r, c), .W => if h : 0 < c.val then some (r, ⟨c.val - 1, by omega⟩) else none
  | (r, c), .E => if h : c.val + 1 < C then some (r, ⟨c.val + 1, h⟩) else none

theorem meshNbr_symm (R C : Nat) :
    ∀ i d j, meshNbr R C i d = some j → meshNbr R C j d.opp = some i := by
  rintro ⟨r, c⟩ d ⟨r', c'⟩ h
  have hr := r.isLt
  have hc := c.isLt
  cases d <;> simp only [meshNbr] at h <;> split at h <;> (try contradiction) <;> cases h <;>
    rename_i h0 <;> simp only [meshNbr, Gem5.NoC.Dir.opp]
  all_goals
    rw [dif_pos (by (try simp) <;> omega)]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> first | rfl | trivial | (apply Fin.ext; (try simp) <;> omega)

def meshTopo (R C : Nat) : Topology (Fin R × Fin C) := ⟨meshNbr R C, meshNbr_symm R C⟩

def meshTiles (R C : Nat) : List (Fin R × Fin C) :=
  (List.finRange R).flatMap fun r => (List.finRange C).map fun c => (r, c)

theorem mem_finRange' {n : Nat} (i : Fin n) : i ∈ List.finRange n :=
  List.mem_iff_getElem.mpr ⟨i.val, by simp [List.length_finRange], by simp [List.getElem_finRange]⟩

theorem meshTiles_complete (R C : Nat) (i : Fin R × Fin C) : i ∈ meshTiles R C := by
  obtain ⟨r, c⟩ := i
  exact List.mem_flatMap.mpr ⟨r, mem_finRange' r, List.mem_map.mpr ⟨c, mem_finRange' c, rfl⟩⟩

/-- 4×4 メッシュ (TileRiscV の既定構成) についての主定理 -/
theorem mesh4x4_refines (s0 : Fin 4 × Fin 4 → Tile) (k : Nat) :
    ∃ n, ∀ i, ((run n (initSim (meshTopo 4 4) (meshTiles 4 4) s0)).st i).tile = meshRun (meshTopo 4 4) k s0 i :=
  mesh_refines_init _ _ (by decide) (meshTiles_complete 4 4) s0 k

end Gem5.Tile
