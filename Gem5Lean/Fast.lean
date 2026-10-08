import Gem5Lean.Tile
import Std.Data.HashMap

/-!
# Gem5Lean.Fast — TileRiscV メッシュの高速実行版 (仕様との等価性つき)

`Tile.lean` の仕様 `meshStep` は状態を関数 (`Reg → Word`, `Mem`, `ι → Tile`) で持つため、
証明はしやすいが、実行すると更新ごとに閉包が積み重なって遅い (O(n²))。

ここでは同じ意味論を

* レジスタファイル: `Array Word` (32 要素, 参照数 1 なら破壊的更新)
* 出力レジスタ: `Array Word` (4 要素)
* dmem: `Std.HashMap Nat Word` + 初期値関数
* メッシュ: `Array FTile` (行優先, R*C 要素)

で実装し、抽象化関数 `FTile.abs` / `absMesh` を通して

* `fstep_abs`      : 1 タイル 1 サイクルが仕様 `tileStep` と一致
* `fmeshStep_abs`  : メッシュ 1 サイクルが仕様 `meshStep` と一致
* `fmeshRun_abs`   : k サイクルが仕様 `meshRun` と一致
* `fast_eq_tlm`    : `Tile.mesh_refines` と合わせて、高速版の結果は TLM (イベント駆動) とも一致

を証明する。命令のデコード・実行 (`tdecode`, `alu`, …) は仕様と同じ関数を使う。
-/

namespace Gem5.Fast
open Gem5 Gem5.RV32 Gem5.Tile
open Gem5.NoC (Dir)

/-! ## exec をレジスタ書き込みの形に分解 -/

/-- (レジスタ書き込み, 次の PC, メモリ操作)。`none` は illegal -/
def execW (i : Instr) (s : Arch) : Option (Option (Reg × Word) × Word × MemOp) :=
  let next := s.pc + 4
  match i with
  | .lui rd imm      => some (some (rd, imm), next, .none)
  | .auipc rd imm    => some (some (rd, s.pc + imm), next, .none)
  | .jal rd off      => some (some (rd, next), s.pc + off, .none)
  | .jalr rd rs1 off => some (some (rd, next), (s.get rs1 + off) &&& ~~~1#32, .none)
  | .branch op rs1 rs2 off =>
    some (none, if branchTaken op (s.get rs1) (s.get rs2) then s.pc + off else next, .none)
  | .lw rd rs1 off   => some (none, next, .load rd (s.get rs1 + off))
  | .sw rs1 rs2 off  => some (none, next, .store (s.get rs1 + off) (s.get rs2))
  | .opimm op rd rs1 imm => some (some (rd, alu op (s.get rs1) imm), next, .none)
  | .op op rd rs1 rs2    => some (some (rd, alu op (s.get rs1) (s.get rs2)), next, .none)
  | .illegal => none

def applyW (s : Arch) : Option (Reg × Word) → Arch
  | none => s
  | some (rd, v) => s.set rd v

theorem exec_eq (i : Instr) (s : Arch) :
    exec i s = (execW i s).map fun (w, pc, op) => ({ applyW s w with pc := pc }, op) := by
  cases i <;> rfl

/-! ## 高速版の状態 -/

def dirIdx : Dir → Nat
  | .N => 0 | .S => 1 | .E => 2 | .W => 3

theorem dirIdx_lt (d : Dir) : dirIdx d < 4 := by cases d <;> decide

theorem dirIdx_inj {d e : Dir} (h : dirIdx d = dirIdx e) : d = e := by
  cases d <;> cases e <;> simp_all [dirIdx]

structure FMem where
  base : Mem
  tbl  : Std.HashMap Nat Word

def FMem.read (m : FMem) (a : Word) : Word :=
  match m.tbl[a.toNat]? with
  | some v => v
  | none => m.base a

def FMem.write (m : FMem) (a v : Word) : FMem := { m with tbl := m.tbl.insert a.toNat v }

theorem FMem.read_write (m : FMem) (a v : Word) : (m.write a v).read = Mem.write m.read a v := by
  funext x
  simp only [FMem.read, FMem.write, Mem.write, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h : x = a
  · subst h; simp
  · have : a.toNat ≠ x.toNat := fun h' => h (BitVec.toNat_inj.mp h').symm
    simp [this, h, FMem.read]

structure FTile where
  pc     : Word
  regs   : Array Word
  imem   : Mem
  dmem   : FMem
  out    : Array Word
  halted : Bool

instance : Inhabited FTile := ⟨⟨0, #[], fun _ => 0, ⟨fun _ => 0, {}⟩, #[], true⟩⟩

def archOf (pc : Word) (regs : Array Word) : Arch := ⟨pc, fun r => regs[r.toNat]!⟩

def FTile.arch (t : FTile) : Arch := archOf t.pc t.regs

@[simp] theorem archOf_pc (p : Word) (r : Array Word) : (archOf p r).pc = p := rfl
@[simp] theorem mk_archOf (p q : Word) (r : Array Word) : (⟨q, (archOf p r).regs⟩ : Arch) = archOf q r := rfl

/-- 抽象化関数: 高速版の状態 → 仕様の状態 -/
def FTile.abs (t : FTile) : Tile :=
  ⟨t.arch, t.imem, t.dmem.read, fun d => t.out[dirIdx d]!, t.halted⟩

def FTile.Inv (t : FTile) : Prop := t.regs.size = 32 ∧ t.out.size = 4

def wreg (regs : Array Word) (rd : Reg) (v : Word) : Array Word :=
  if rd = 0 then regs else regs.set! rd.toNat v

def applyWA (regs : Array Word) : Option (Reg × Word) → Array Word
  | none => regs
  | some (rd, v) => wreg regs rd v

/-- 高速版の 1 サイクル (`tileStep` と同じ構造) -/
def fstep (t : FTile) (inp : Dir → Word) : FTile × Option (Dir × Word) :=
  if t.halted then (t, none) else
  match tdecode (t.imem t.pc) with
  | .send d rs1 =>
    let v := t.arch.get rs1
    ({ t with out := t.out.set! (dirIdx d) v, pc := t.pc + 4 }, some (d, v))
  | .recv rd d =>
    ({ t with regs := wreg t.regs rd (inp d), pc := t.pc + 4 }, none)
  | .base i =>
    match execW i t.arch with
    | none => ({ t with halted := true }, none)
    | some (w, pc', .none) => ({ t with regs := applyWA t.regs w, pc := pc' }, none)
    | some (w, pc', .load rd addr) =>
      ({ t with regs := wreg (applyWA t.regs w) rd (t.dmem.read addr), pc := pc' }, none)
    | some (w, pc', .store addr v) =>
      ({ t with regs := applyWA t.regs w, pc := pc', dmem := t.dmem.write addr v }, none)

/-! ## 1 タイルの正しさ -/

theorem size_wreg (regs : Array Word) (rd : Reg) (v : Word) : (wreg regs rd v).size = regs.size := by
  unfold wreg; split
  · rfl
  · simp [Array.set!_eq_setIfInBounds]

theorem size_applyWA (regs : Array Word) (w) : (applyWA regs w).size = regs.size := by
  cases w with
  | none => rfl
  | some p => obtain ⟨rd, v⟩ := p; exact size_wreg regs rd v

theorem set_archOf (pc : Word) (regs : Array Word) (h : regs.size = 32) (rd : Reg) (v : Word) :
    (archOf pc regs).set rd v = archOf pc (wreg regs rd v) := by
  unfold Arch.set wreg archOf
  by_cases h0 : rd = 0
  · simp [h0]
  · simp only [h0, if_false]
    congr 1
    funext i
    have hi : i.toNat < regs.size := by have := i.isLt; rw [h]; exact this
    have hrd : rd.toNat < regs.size := by have := rd.isLt; rw [h]; exact this
    have hs : i.toNat < (regs.set! rd.toNat v).size := by simp [Array.set!_eq_setIfInBounds]; exact hi
    rw [getElem!_pos (regs.set! rd.toNat v) i.toNat hs, getElem!_pos regs i.toNat hi]
    by_cases hir : i = rd
    · subst hir; simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds]
    · have : rd.toNat ≠ i.toNat := fun h' => hir (BitVec.toNat_inj.mp h').symm
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds hi, if_neg this]
      simp [hir]

theorem applyW_archOf (pc : Word) (regs : Array Word) (h : regs.size = 32) (w) :
    applyW (archOf pc regs) w = archOf pc (applyWA regs w) := by
  cases w with
  | none => rfl
  | some p => obtain ⟨rd, v⟩ := p; exact set_archOf pc regs h rd v

theorem out_abs (out : Array Word) (h : out.size = 4) (d : Dir) (v : Word) :
    (fun e => (out.set! (dirIdx d) v)[dirIdx e]!) = upd (fun e => out[dirIdx e]!) d v := by
  funext e
  have he : dirIdx e < out.size := by have := dirIdx_lt e; omega
  have hs : dirIdx e < (out.set! (dirIdx d) v).size := by simp [Array.set!_eq_setIfInBounds]; exact he
  rw [getElem!_pos (out.set! (dirIdx d) v) (dirIdx e) hs]
  simp only [upd]
  by_cases hed : e = d
  · subst hed; simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds]
  · have : dirIdx d ≠ dirIdx e := fun h' => hed (dirIdx_inj h').symm
    rw [if_neg hed, getElem!_pos out (dirIdx e) he]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds he, if_neg this]

/-- **1 タイル 1 サイクルの正しさ**: 高速版の結果を抽象化すると仕様 `tileStep` の結果に一致し、
不変条件 (配列サイズ) も保たれる -/
theorem fstep_abs (t : FTile) (h : t.Inv) (inp : Dir → Word) :
    ((fstep t inp).1.abs, (fstep t inp).2) = tileStep t.abs inp ∧ (fstep t inp).1.Inv := by
  obtain ⟨hr, ho⟩ := h
  by_cases hh : t.halted = true
  · have e1 : fstep t inp = (t, none) := by simp [fstep, hh]
    have e2 : tileStep t.abs inp = (t.abs, none) := by simp [tileStep, FTile.abs, hh]
    rw [e1, e2]; exact ⟨rfl, hr, ho⟩
  · have hf : t.halted = false := by simpa using hh
    unfold fstep tileStep
    simp only [hf, FTile.abs, FTile.arch, archOf_pc, Bool.false_eq_true, if_false]
    cases hd : tdecode (t.imem t.pc) with
    | send d rs1 =>
      dsimp only
      refine ⟨?_, hr, by simp [Array.set!_eq_setIfInBounds, ho]⟩
      simp only [mk_archOf]
      rw [out_abs t.out ho d]
    | recv rd d =>
      dsimp only
      refine ⟨?_, by simp only; rw [size_wreg]; exact hr, ho⟩
      rw [set_archOf _ _ hr]; rfl
    | base i =>
      dsimp only
      rw [exec_eq]
      cases hx : execW i (archOf t.pc t.regs) with
      | none => exact ⟨rfl, hr, ho⟩
      | some x =>
        obtain ⟨w, pc', op⟩ := x
        simp only [Option.map_some]
        rw [applyW_archOf _ _ hr]
        cases op with
        | none =>
          refine ⟨?_, by simp only; rw [size_applyWA]; exact hr, ho⟩
          simp only [mk_archOf]
        | load rd addr =>
          refine ⟨?_, by simp only; rw [size_wreg, size_applyWA]; exact hr, ho⟩
          simp only [mk_archOf]
          rw [set_archOf _ _ (by rw [size_applyWA]; exact hr)]
        | store addr v =>
          refine ⟨?_, by simp only; rw [size_applyWA]; exact hr, ho⟩
          simp only [mk_archOf, FMem.read_write]

/-! ## タイル実装の抽象インタフェース

メッシュ層は、タイルの内部表現 (BitVec 版 / UInt32 版 …) によらず、
「抽象化すると `tileStep` と一致する 1 サイクル関数」さえあれば証明が通る。 -/

structure TileImpl where
  S       : Type
  dflt    : S
  abs     : S → Tile
  Inv     : S → Prop
  step    : S → (Dir → Word) → S
  outRd   : S → Dir → Word
  halted  : S → Bool
  ofTile  : Tile → S
  outRd_eq  : ∀ s, Inv s → outRd s = (abs s).out
  step_abs  : ∀ s inp, Inv s → abs (step s inp) = (tileStep (abs s) inp).1 ∧ Inv (step s inp)
  ofTile_abs : ∀ t, abs (ofTile t) = t
  ofTile_inv : ∀ t, Inv (ofTile t)

instance TileImpl.instInh (I : TileImpl) : Inhabited I.S := ⟨I.dflt⟩

/-! ## メッシュ (R 行 × C 列, 行優先の配列) -/

section mesh
variable (R C : Nat)

def idx (i : Fin R × Fin C) : Nat := i.1.val * C + i.2.val

theorem idx_lt (i : Fin R × Fin C) : idx R C i < R * C := by
  obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := i
  simp only [idx]
  have : (r + 1) * C ≤ R * C := Nat.mul_le_mul_right C hr
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

def toRC (k : Fin (R * C)) : Fin R × Fin C :=
  have hC : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h | h
    · subst h; simp at k; exact k.elim0
    · exact h
  (⟨k.val / C, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm R C))⟩, ⟨k.val % C, Nat.mod_lt _ hC⟩)

theorem toRC_idx (i : Fin R × Fin C) : toRC R C ⟨idx R C i, idx_lt R C i⟩ = i := by
  obtain ⟨⟨r, hr⟩, ⟨c, hc⟩⟩ := i
  have hC : 0 < C := by omega
  simp only [toRC, idx, Prod.mk.injEq]
  constructor
  · apply Fin.ext; simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hC, Nat.div_eq_of_lt hc, Nat.zero_add]
  · apply Fin.ext; simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

variable (I : TileImpl)

/-- 隣接タイルの出力レジスタ (端は 0) -/
def fnbr (arr : Array I.S) (i : Fin R × Fin C) (d : Dir) : Word :=
  match meshNbr R C i d with
  | some j => I.outRd arr[idx R C j]! d.opp
  | none => 0

/-- **高速版のメッシュ 1 サイクル**: 旧配列から入力を読み、新配列を作る -/
def fmeshStep (arr : Array I.S) : Array I.S :=
  Array.ofFn (n := R * C) fun k => I.step arr[k.val]! (fnbr R C I arr (toRC R C k))

/-! ### 破壊的更新版 (実行用)

`fmeshStep` は旧配列から読みながら新配列を作るため、各タイルの内部配列 (レジスタなど) が
旧配列と共有され、更新のたびにコピーが発生する。
出力レジスタだけスナップショットしてから配列を 1 要素ずつ `Array.modify` で書き換えると、
参照が 1 本になり Lean のランタイムが破壊的に更新する。`fmeshStep` と等しいことを証明してある。 -/

/-- 全タイルの出力レジスタのスナップショット (値のみ。タイル本体への参照は残さない) -/
def snapOuts (arr : Array I.S) : Array (Array Word) :=
  arr.map fun t => #[I.outRd t .N, I.outRd t .S, I.outRd t .E, I.outRd t .W]

/-- タイル k の方向 d の入力。隣接位置の計算は RECV で読まれたときだけ行う (遅延) -/
def inpL (outs : Array (Array Word)) (k : Nat) (d : Dir) : Word :=
  if hk : k < R * C then
    match meshNbr R C (toRC R C ⟨k, hk⟩) d with
    | some j => (outs[idx R C j]!)[dirIdx d.opp]!
    | none => 0
  else 0

def stepFrom (inp : Nat → Dir → Word) (k : Nat) (arr : Array I.S) : Array I.S :=
  if k < arr.size then stepFrom inp (k + 1) (arr.modify k fun t => I.step t (inp k)) else arr
termination_by arr.size - k
decreasing_by simp only [Array.size_modify]; omega

def fmeshStepFast (arr : Array I.S) : Array I.S :=
  if arr.size = R * C then stepFrom I (inpL R C (snapOuts I arr)) 0 arr else fmeshStep R C I arr

theorem stepFrom_spec (inp : Nat → Dir → Word) : ∀ (n k : Nat) (arr : Array I.S), arr.size - k = n →
    (stepFrom I inp k arr).size = arr.size ∧
    ∀ j (h1 : j < (stepFrom I inp k arr).size) (h2 : j < arr.size),
      (stepFrom I inp k arr)[j] = if k ≤ j then I.step arr[j] (inp j) else arr[j] := by
  intro n
  induction n with
  | zero =>
    intro k arr hn
    rw [stepFrom]
    have : ¬ k < arr.size := by omega
    simp only [this, if_false]
    refine ⟨by trivial, fun j _ h2 => ?_⟩
    have : ¬ k ≤ j := by omega
    simp [this]
  | succ n ih =>
    intro k arr hn
    have hk : k < arr.size := by omega
    have e : stepFrom I inp k arr = stepFrom I inp (k + 1) (arr.modify k fun t => I.step t (inp k)) := by
      rw [stepFrom]; simp [hk]
    obtain ⟨h1, h2⟩ := ih (k + 1) (arr.modify k fun t => I.step t (inp k)) (by simp only [Array.size_modify]; omega)
    rw [e]
    refine ⟨by rw [h1, Array.size_modify], fun j hj1 hj2 => ?_⟩
    rw [h2 j hj1 (by simp only [Array.size_modify]; exact hj2)]
    simp only [Array.getElem_modify]
    by_cases hkj : k = j
    · subst hkj; simp; omega
    · by_cases hle : k + 1 ≤ j
      · have : k ≤ j := by omega
        simp [hle, hkj, this]
      · have : ¬ k ≤ j := by omega
        simp [hle, hkj, this]

theorem inpL_snap (arr : Array I.S) (hs : arr.size = R * C) (k : Nat) (hk : k < R * C) :
    inpL R C (snapOuts I arr) k = fnbr R C I arr (toRC R C ⟨k, hk⟩) := by
  funext d
  simp only [inpL, hk, dif_pos, fnbr]
  cases meshNbr R C (toRC R C ⟨k, hk⟩) d with
  | none => rfl
  | some j =>
    simp only
    have hj : idx R C j < (snapOuts I arr).size := by simp [snapOuts, hs]; exact idx_lt R C j
    rw [getElem!_pos (snapOuts I arr) _ hj]
    simp only [snapOuts, Array.getElem_map]
    rw [getElem!_pos arr _ (by rw [hs]; exact idx_lt R C j)]
    cases d <;> rfl

theorem fmeshStepFast_eq (arr : Array I.S) : fmeshStepFast R C I arr = fmeshStep R C I arr := by
  unfold fmeshStepFast
  split
  · rename_i hs
    obtain ⟨h1, h2⟩ := stepFrom_spec I (inpL R C (snapOuts I arr)) _ 0 arr rfl
    apply Array.ext
    · rw [h1, hs]; simp [fmeshStep]
    · intro j hj1 hj2
      have hj : j < R * C := by rw [h1, hs] at hj1; exact hj1
      rw [h2 j hj1 (by omega)]
      simp only [Nat.zero_le, if_true, fmeshStep, Array.getElem_ofFn]
      rw [getElem!_pos _ _ (by omega), inpL_snap R C I arr hs j hj]
  · rfl

/-- `@[csimp]` で `fmeshStep` をこれに差し替えることもできるが、実測では
(4×4、波面プログラム) 出力スナップショットのコストがコピー削減を上回り遅くなったので、既定では使わない。 -/
theorem fmeshStep_eq_fast : @fmeshStep = @fmeshStepFast := by
  funext R C I arr; exact (fmeshStepFast_eq R C I arr).symm

def absMesh (arr : Array I.S) : Fin R × Fin C → Tile := fun i => I.abs arr[idx R C i]!

def MeshInv (arr : Array I.S) : Prop := arr.size = R * C ∧ ∀ k (h : k < arr.size), I.Inv arr[k]

theorem inv_get {arr : Array I.S} (h : MeshInv R C I arr) (k : Nat) (hk : k < R * C) : I.Inv arr[k]! := by
  rw [getElem!_pos _ _ (by rw [h.1]; exact hk)]; exact h.2 _ _

theorem fnbr_eq (arr : Array I.S) (h : MeshInv R C I arr) (i : Fin R × Fin C) :
    fnbr R C I arr i = nbrOut (meshTopo R C) (absMesh R C I arr) i := by
  funext d
  simp only [fnbr, nbrOut, meshTopo, absMesh]
  cases hn : meshNbr R C i d with
  | none => rfl
  | some j => simp only; rw [I.outRd_eq _ (inv_get R C I h _ (idx_lt R C j))]

/-- **メッシュ 1 サイクルの正しさ** -/
theorem fmeshStep_abs (arr : Array I.S) (h : MeshInv R C I arr) :
    absMesh R C I (fmeshStep R C I arr) = meshStep (meshTopo R C) (absMesh R C I arr) ∧
      MeshInv R C I (fmeshStep R C I arr) := by
  refine ⟨?_, by simp [fmeshStep], ?_⟩
  · funext i
    have hi := idx_lt R C i
    simp only [absMesh, meshStep]
    rw [getElem!_pos _ _ (by simp [fmeshStep]; exact hi)]
    simp only [fmeshStep, Array.getElem_ofFn]
    rw [toRC_idx, fnbr_eq R C I arr h]
    exact (I.step_abs _ _ (inv_get R C I h _ hi)).1
  · intro k hk
    simp only [fmeshStep, Array.getElem_ofFn]
    have hk' : k < R * C := by simpa [fmeshStep] using hk
    exact (I.step_abs _ _ (inv_get R C I h _ hk')).2

def fmeshRun : Nat → Array I.S → Array I.S
  | 0, arr => arr
  | k + 1, arr => fmeshRun k (fmeshStep R C I arr)

/-- **k サイクルの正しさ**: 高速版は仕様 `meshRun` と一致 -/
theorem fmeshRun_abs : ∀ (k : Nat) (arr : Array I.S), MeshInv R C I arr →
    absMesh R C I (fmeshRun R C I k arr) = meshRun (meshTopo R C) k (absMesh R C I arr)
  | 0, _, _ => rfl
  | k + 1, arr, h => by
    have ⟨h1, h2⟩ := fmeshStep_abs R C I arr h
    simp only [fmeshRun, meshRun]
    rw [fmeshRun_abs k _ h2, h1]

def meshOf (s0 : Fin R × Fin C → Tile) : Array I.S :=
  Array.ofFn (n := R * C) fun k => I.ofTile (s0 (toRC R C k))

theorem meshOf_inv (s0 : Fin R × Fin C → Tile) : MeshInv R C I (meshOf R C I s0) := by
  refine ⟨by simp [meshOf], fun k hk => ?_⟩
  simp only [meshOf, Array.getElem_ofFn]
  exact I.ofTile_inv _

theorem absMesh_meshOf (s0 : Fin R × Fin C → Tile) : absMesh R C I (meshOf R C I s0) = s0 := by
  funext i
  simp only [absMesh, meshOf]
  rw [getElem!_pos _ _ (by simp; exact idx_lt R C i), Array.getElem_ofFn, toRC_idx, I.ofTile_abs]

/-- **主定理**: 任意の初期状態 `s0` について、高速版を k サイクル回した結果は
(1) 仕様 `meshRun` と一致し、(2) イベント駆動 TLM を有限ステップ回した結果とも一致する -/
theorem fast_correct (s0 : Fin R × Fin C → Tile) (hnd : (meshTiles R C).Nodup) (k : Nat) :
    absMesh R C I (fmeshRun R C I k (meshOf R C I s0)) = meshRun (meshTopo R C) k s0 ∧
    ∃ n, ∀ i, ((run n (initSim (meshTopo R C) (meshTiles R C) s0)).st i).tile =
      absMesh R C I (fmeshRun R C I k (meshOf R C I s0)) i := by
  have h1 := fmeshRun_abs R C I k _ (meshOf_inv R C I s0)
  rw [absMesh_meshOf] at h1
  obtain ⟨n, hn⟩ := mesh_refines_init (meshTopo R C) (meshTiles R C) hnd (meshTiles_complete R C) s0 k
  exact ⟨h1, n, fun i => by rw [hn, h1]⟩

/-- 停止するまで回す (実行用) -/
def fmeshRunUntilHalt (fuel : Nat) (arr : Array I.S) : Nat × Array I.S := Id.run do
  let mut a := arr
  let mut c := 0
  for _ in [0:fuel] do
    if a.all I.halted then break
    a := fmeshStep R C I a
    c := c + 1
  return (c, a)

end mesh

/-! ## BitVec 版のインスタンス -/

def FTile.ofTile (t : Tile) : FTile where
  pc := t.arch.pc
  regs := (Array.range 32).map fun k => t.arch.regs (BitVec.ofNat 5 k)
  imem := t.imem
  dmem := ⟨t.dmem, {}⟩
  out := #[t.out .N, t.out .S, t.out .E, t.out .W]
  halted := t.halted

theorem FTile.ofTile_abs_eq (t : Tile) : (FTile.ofTile t).abs = t := by
  obtain ⟨⟨pc, regs⟩, imem, dmem, out, halted⟩ := t
  simp only [FTile.abs, FTile.ofTile, FTile.arch, archOf, Tile.mk.injEq, Arch.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext r
    have : r.toNat < 32 := by have := r.isLt; simpa using this
    rw [getElem!_pos _ _ (by simpa using this)]
    simp [BitVec.ofNat_toNat]
  · funext a; simp [FMem.read]
  · exact ⟨by funext d; cases d <;> rfl, trivial⟩

def bvImpl : TileImpl where
  S := FTile
  dflt := default
  abs := FTile.abs
  Inv := FTile.Inv
  step t inp := (fstep t inp).1
  outRd t d := t.out[dirIdx d]!
  halted := FTile.halted
  ofTile := FTile.ofTile
  outRd_eq _ _ := rfl
  step_abs t inp h := ⟨congrArg Prod.fst (fstep_abs t h inp).1, (fstep_abs t h inp).2⟩
  ofTile_abs := FTile.ofTile_abs_eq
  ofTile_inv t := by simp [FTile.ofTile, FTile.Inv]

/-- 4×4 (TileRiscV の既定構成) -/
theorem bv_correct_4x4 (s0 : Fin 4 × Fin 4 → Tile) (k : Nat) :
    absMesh 4 4 bvImpl (fmeshRun 4 4 bvImpl k (meshOf 4 4 bvImpl s0)) = meshRun (meshTopo 4 4) k s0 :=
  (fast_correct 4 4 bvImpl s0 (by decide) k).1

end Gem5.Fast
