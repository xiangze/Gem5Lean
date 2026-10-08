import Gem5Lean.Fast

/-!
# Gem5Lean.Fast32 — 32 ビットネイティブ (UInt32) + デコードキャッシュ版

`Fast.lean` の BitVec 版は、BitVec の演算が実行時に多倍長 Nat (GMP) で計算されるため遅い。
ここでは

* 値はすべて `UInt32` (ネイティブの 32 ビット整数)。符号付き比較は `Int32`
* 命令は初期化時に一度だけデコードして `icache : Array FI` に置く (gem5 の decode cache と同じ発想)
* よく使う ALU 演算 (add/sub/論理/シフト/比較/mul) は UInt32 で直接計算し、
  まれな演算 (mulh 系、div/rem 系、sra) は仕様の BitVec 関数にフォールバック

とし、`TileImpl` のインスタンスとして仕様 `tileStep` との一致を証明する。
メッシュの正しさ (`fast_correct`) は `Fast.lean` の一般定理がそのまま使える。
-/

namespace Gem5.Fast32
open Gem5 Gem5.RV32 Gem5.Tile Gem5.Fast
open Gem5.NoC (Dir)

abbrev U := UInt32

/-! ## 事前デコード済み命令 -/

inductive FI
  | lui    (rd : Reg) (imm : U)
  | auipc  (rd : Reg) (imm : U)
  | jal    (rd : Reg) (off : U)
  | jalr   (rd rs1 : Reg) (off : U)
  | branch (op : BrOp) (rs1 rs2 : Reg) (off : U)
  | lw     (rd rs1 : Reg) (off : U)
  | sw     (rs1 rs2 : Reg) (off : U)
  | opimm  (op : AluOp) (rd rs1 : Reg) (imm : U)
  | op     (op : AluOp) (rd rs1 rs2 : Reg)
  | illegal
  | send   (d : Dir) (rs1 : Reg)
  | recv   (rd : Reg) (d : Dir)

instance : Inhabited FI := ⟨.illegal⟩

def FI.ofI : Instr → FI
  | .lui rd imm => .lui rd ⟨imm⟩
  | .auipc rd imm => .auipc rd ⟨imm⟩
  | .jal rd off => .jal rd ⟨off⟩
  | .jalr rd rs1 off => .jalr rd rs1 ⟨off⟩
  | .branch o rs1 rs2 off => .branch o rs1 rs2 ⟨off⟩
  | .lw rd rs1 off => .lw rd rs1 ⟨off⟩
  | .sw rs1 rs2 off => .sw rs1 rs2 ⟨off⟩
  | .opimm o rd rs1 imm => .opimm o rd rs1 ⟨imm⟩
  | .op o rd rs1 rs2 => .op o rd rs1 rs2
  | .illegal => .illegal

def FI.ofT : TInstr → FI
  | .send d rs1 => .send d rs1
  | .recv rd d => .recv rd d
  | .base i => FI.ofI i

/-! ## ALU / 分岐 (UInt32) -/

def slt32 (a b : U) : Bool := a.toInt32 < b.toInt32   -- ネイティブの符号付き比較

def alu32 (op : AluOp) (a b : U) : U :=
  match op with
  | .add  => a + b
  | .sub  => a - b
  | .sll  => a <<< b
  | .slt  => if slt32 a b then 1 else 0
  | .sltu => if a < b then 1 else 0
  | .xor  => a ^^^ b
  | .srl  => a >>> b
  | .or   => a ||| b
  | .and  => a &&& b
  | .mul  => a * b
  | o     => ⟨alu o a.toBitVec b.toBitVec⟩    -- sra, mulh*, div*, rem*: 仕様にフォールバック

def br32 (op : BrOp) (a b : U) : Bool :=
  match op with
  | .beq  => a == b
  | .bne  => a != b
  | .blt  => slt32 a b
  | .bge  => !(slt32 a b)
  | .bltu => a < b
  | .bgeu => !(a < b)

theorem ult32_eq (a b : U) : decide (a < b) = a.toBitVec.ult b.toBitVec := by
  unfold BitVec.ult; exact decide_eq_decide.mpr UInt32.lt_iff_toNat_lt

theorem slt32_eq (a b : U) : slt32 a b = a.toBitVec.slt b.toBitVec := by
  simp [slt32, Int32.lt_iff_toBitVec_slt]

theorem shamt_eq (b : U) : (b.toBitVec % 32).toNat = b.toBitVec.toNat % 32 := by
  rw [BitVec.toNat_umod]; rfl

theorem alu32_eq (op : AluOp) (a b : U) : (alu32 op a b).toBitVec = alu op a.toBitVec b.toBitVec := by
  cases op <;> simp only [alu32, alu, UInt32.toBitVec_add, UInt32.toBitVec_sub, UInt32.toBitVec_mul,
    UInt32.toBitVec_xor, UInt32.toBitVec_or, UInt32.toBitVec_and]
  · rw [UInt32.toBitVec_shiftLeft, BitVec.shiftLeft_eq', shamt_eq]
  · rw [← slt32_eq]; split <;> rfl
  · rw [show a.toBitVec.ult b.toBitVec = decide (a < b) from (ult32_eq a b).symm]; split <;> simp_all
  · rw [UInt32.toBitVec_shiftRight, BitVec.ushiftRight_eq', shamt_eq]

theorem br32_eq (op : BrOp) (a b : U) : br32 op a b = branchTaken op a.toBitVec b.toBitVec := by
  cases op <;> simp only [br32, branchTaken, slt32_eq]
  · rw [Bool.eq_iff_iff]; simp [UInt32.toBitVec_inj]
  · rw [Bool.eq_iff_iff]; simp [UInt32.toBitVec_inj]
  · rw [← ult32_eq]
  · rw [← ult32_eq]

/-! ## タイル状態 -/

structure FTile32 where
  pc       : U
  regs     : Array U
  imem     : Mem
  icache   : Array FI
  dmemBase : Mem
  dmem     : Std.HashMap U U
  out      : Array U
  halted   : Bool

instance : Inhabited FTile32 := ⟨⟨0, #[], fun _ => 0, #[], fun _ => 0, {}, #[], true⟩⟩

def rget (regs : Array U) (r : Reg) : U := if r = 0 then 0 else regs[r.toNat]!

def wr32 (regs : Array U) (rd : Reg) (v : U) : Array U := if rd = 0 then regs else regs.set! rd.toNat v

def dread (t : FTile32) (a : U) : U :=
  match t.dmem[a]? with
  | some v => v
  | none => ⟨t.dmemBase a.toBitVec⟩

/-- フェッチ: 整列していてキャッシュ内なら事前デコード済み命令、そうでなければその場でデコード -/
def fetch (t : FTile32) : FI :=
  let n := t.pc.toNat
  if n % 4 = 0 ∧ n / 4 < t.icache.size then t.icache[n / 4]!
  else FI.ofT (tdecode (t.imem t.pc.toBitVec))

def step32 (t : FTile32) (inp : Dir → Word) : FTile32 :=
  if t.halted then t else
  let pc := t.pc
  let next := pc + 4
  match fetch t with
  | .send d rs1 => { t with out := t.out.set! (dirIdx d) (rget t.regs rs1), pc := next }
  | .recv rd d => { t with regs := wr32 t.regs rd ⟨inp d⟩, pc := next }
  | .lui rd imm => { t with regs := wr32 t.regs rd imm, pc := next }
  | .auipc rd imm => { t with regs := wr32 t.regs rd (pc + imm), pc := next }
  | .jal rd off => { t with regs := wr32 t.regs rd next, pc := pc + off }
  | .jalr rd rs1 off =>
    { t with regs := wr32 t.regs rd next, pc := (rget t.regs rs1 + off) &&& ~~~1 }
  | .branch o rs1 rs2 off =>
    { t with pc := if br32 o (rget t.regs rs1) (rget t.regs rs2) then pc + off else next }
  | .lw rd rs1 off => { t with regs := wr32 t.regs rd (dread t (rget t.regs rs1 + off)), pc := next }
  | .sw rs1 rs2 off =>
    { t with dmem := t.dmem.insert (rget t.regs rs1 + off) (rget t.regs rs2), pc := next }
  | .opimm o rd rs1 imm => { t with regs := wr32 t.regs rd (alu32 o (rget t.regs rs1) imm), pc := next }
  | .op o rd rs1 rs2 =>
    { t with regs := wr32 t.regs rd (alu32 o (rget t.regs rs1) (rget t.regs rs2)), pc := next }
  | .illegal => { t with halted := true }

/-! ## 抽象化と不変条件 -/

def archAbs (pc : U) (regs : Array U) : Arch := ⟨pc.toBitVec, fun r => (regs[r.toNat]!).toBitVec⟩

def dmemAbs (base : Mem) (m : Std.HashMap U U) : Mem := fun a =>
  match m[(⟨a⟩ : U)]? with
  | some v => v.toBitVec
  | none => base a

def FTile32.abs (t : FTile32) : Tile :=
  ⟨archAbs t.pc t.regs, t.imem, dmemAbs t.dmemBase t.dmem, fun d => (t.out[dirIdx d]!).toBitVec, t.halted⟩

def FTile32.Inv (t : FTile32) : Prop :=
  t.regs.size = 32 ∧ t.out.size = 4 ∧
  ∀ k (h : k < t.icache.size), t.icache[k] = FI.ofT (tdecode (t.imem (BitVec.ofNat 32 (4 * k))))

theorem fetch_eq (t : FTile32) (h : t.Inv) : fetch t = FI.ofT (tdecode (t.imem t.pc.toBitVec)) := by
  dsimp only [fetch]
  split
  · rename_i hc
    obtain ⟨h4, hk⟩ := hc
    rw [getElem!_pos t.icache (t.pc.toNat / 4) hk, h.2.2 _ hk]
    congr 3
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have : 4 * (t.pc.toNat / 4) = t.pc.toNat := by omega
    rw [this, Nat.mod_eq_of_lt (by have := t.pc.toBitVec.isLt; simpa using this)]
    rfl
  · rfl

theorem get_archAbs (pc : U) (regs : Array U) (r : Reg) : (archAbs pc regs).get r = (rget regs r).toBitVec := by
  simp only [Arch.get, archAbs, rget]
  split <;> rfl

theorem set_archAbs (pc : U) (regs : Array U) (h : regs.size = 32) (rd : Reg) (v : U) :
    (archAbs pc regs).set rd v.toBitVec = archAbs pc (wr32 regs rd v) := by
  unfold Arch.set wr32 archAbs
  by_cases h0 : rd = 0
  · simp [h0]
  · simp only [h0, if_false]
    congr 1
    funext i
    have hi : i.toNat < regs.size := by have := i.isLt; rw [h]; exact this
    have hs : i.toNat < (regs.set! rd.toNat v).size := by simp [Array.set!_eq_setIfInBounds]; exact hi
    rw [getElem!_pos (regs.set! rd.toNat v) i.toNat hs, getElem!_pos regs i.toNat hi]
    by_cases hir : i = rd
    · subst hir; simp [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds]
    · have : rd.toNat ≠ i.toNat := fun h' => hir (BitVec.toNat_inj.mp h').symm
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds hi, if_neg this]
      simp [hir]

theorem size_wr32 (regs : Array U) (rd : Reg) (v : U) : (wr32 regs rd v).size = regs.size := by
  unfold wr32; split
  · rfl
  · simp [Array.set!_eq_setIfInBounds]

theorem mk_archAbs (p : Word) (q : U) (r : Array U) (h : p = q.toBitVec) :
    (⟨p, (archAbs q r).regs⟩ : Arch) = archAbs q r := by subst h; rfl

theorem mk_archAbs' (p : Word) (q q' : U) (r : Array U) (h : p = q'.toBitVec) :
    (⟨p, (archAbs q r).regs⟩ : Arch) = archAbs q' r := by subst h; rfl

theorem archAbs_pc (q : U) (r : Array U) : (archAbs q r).pc = q.toBitVec := rfl

theorem out32_abs (out : Array U) (h : out.size = 4) (d : Dir) (v : U) :
    (fun e => (out.set! (dirIdx d) v)[dirIdx e]!.toBitVec) = upd (fun e => (out[dirIdx e]!).toBitVec) d v.toBitVec := by
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

theorem dread_insert (base : Mem) (m : Std.HashMap U U) (a v : U) :
    dmemAbs base (m.insert a v) = Mem.write (dmemAbs base m) a.toBitVec v.toBitVec := by
  funext x
  simp only [dmemAbs, Mem.write, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h : x = a.toBitVec
  · subst h; simp
  · have : a ≠ ⟨x⟩ := fun h' => h (by subst h'; rfl)
    simp [this, h]

theorem dread_abs (t : FTile32) (a : U) : (dread t a).toBitVec = dmemAbs t.dmemBase t.dmem a.toBitVec := by
  simp only [dread, dmemAbs, UInt32.ofBitVec_toBitVec]
  cases t.dmem[a]? <;> rfl

theorem toBV_four : (4 : U).toBitVec = 4#32 := rfl
theorem toBV_one : (1 : U).toBitVec = 1#32 := rfl
theorem toBV_not (a : U) : (~~~a).toBitVec = ~~~a.toBitVec := UInt32.toBitVec_not

/-- **1 タイル 1 サイクルの正しさ** -/
theorem step32_abs (t : FTile32) (inp : Dir → Word) (h : t.Inv) :
    (step32 t inp).abs = (tileStep t.abs inp).1 ∧ (step32 t inp).Inv := by
  obtain ⟨hr, ho, hc⟩ := h
  by_cases hh : t.halted = true
  · have e1 : step32 t inp = t := by simp [step32, hh]
    have e2 : tileStep t.abs inp = (t.abs, none) := by simp [tileStep, FTile32.abs, hh]
    rw [e1, e2]; exact ⟨rfl, hr, ho, hc⟩
  · have hf : t.halted = false := by simpa using hh
    have hfe := fetch_eq t ⟨hr, ho, hc⟩
    unfold step32 tileStep
    simp only [FTile32.abs, archAbs_pc, hf, Bool.false_eq_true, if_false, hfe]
    cases hd : tdecode (t.imem t.pc.toBitVec) with
    | send d rs1 =>
      try simp only [FI.ofT]
      refine ⟨?_, hr, by simp [Array.set!_eq_setIfInBounds, ho], hc⟩
      simp only [Tile.mk.injEq, and_true, true_and]
      refine ⟨mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc]), ?_⟩
      rw [out32_abs _ ho, get_archAbs]
    | recv rd d =>
      try simp only [FI.ofT]
      refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
      simp only [Tile.mk.injEq, and_true, true_and]
      rw [show inp d = (UInt32.ofBitVec (inp d)).toBitVec from rfl, set_archAbs _ _ hr]
      exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc])
    | base i =>
      cases i with
      | illegal =>
        try simp only [FI.ofT, FI.ofI, exec]
        exact ⟨by first | trivial | rfl, hr, ho, hc⟩
      | lui rd imm =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and]
        rw [show imm = (UInt32.ofBitVec imm).toBitVec from rfl, set_archAbs _ _ hr]
        exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc])
      | auipc rd imm =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [show t.pc.toBitVec + imm = (t.pc + UInt32.ofBitVec imm).toBitVec by simp [UInt32.toBitVec_add],
          set_archAbs _ _ hr]
        exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc])
      | jal rd off =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [show t.pc.toBitVec + 4 = (t.pc + 4).toBitVec by simp [UInt32.toBitVec_add, toBV_four],
          set_archAbs _ _ hr]
        exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add])
      | jalr rd rs1 off =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [show t.pc.toBitVec + 4 = (t.pc + 4).toBitVec by simp [UInt32.toBitVec_add, toBV_four],
          set_archAbs _ _ hr]
        refine mk_archAbs _ _ _ ?_
        rw [get_archAbs]
        simp [UInt32.toBitVec_add, UInt32.toBitVec_and, toBV_not, toBV_one]
      | branch o rs1 rs2 off =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        refine mk_archAbs _ _ _ ?_
        rw [get_archAbs, get_archAbs, ← br32_eq]
        cases br32 o (rget t.regs rs1) (rget t.regs rs2) <;>
          (simp (config := { failIfUnchanged := false }) [UInt32.toBitVec_add, toBV_four]; try rfl)
      | lw rd rs1 off =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [mk_archAbs' _ t.pc (t.pc + 4) _ (by simp [UInt32.toBitVec_add, toBV_four]), get_archAbs,
          show (rget t.regs rs1).toBitVec + off = (rget t.regs rs1 + UInt32.ofBitVec off).toBitVec by
            simp [UInt32.toBitVec_add],
          ← dread_abs, set_archAbs _ _ hr]
      | sw rs1 rs2 off =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        refine ⟨mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc]), ?_⟩
        rw [get_archAbs, get_archAbs,
          show (rget t.regs rs1).toBitVec + off = (rget t.regs rs1 + UInt32.ofBitVec off).toBitVec by
            simp [UInt32.toBitVec_add],
          ← dread_insert]
      | opimm o rd rs1 imm =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [get_archAbs, show imm = (UInt32.ofBitVec imm).toBitVec from rfl, ← alu32_eq, set_archAbs _ _ hr]
        exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc])
      | op o rd rs1 rs2 =>
        try simp only [FI.ofT, FI.ofI, exec]
        refine ⟨?_, by simp only; rw [size_wr32]; exact hr, ho, hc⟩
        simp only [Tile.mk.injEq, and_true, true_and, archAbs_pc]
        rw [get_archAbs, get_archAbs, ← alu32_eq, set_archAbs _ _ hr]
        exact mk_archAbs _ _ _ (by simp [UInt32.toBitVec_add, toBV_four, archAbs_pc])

/-! ## 初期化 -/

/-- 仕様のタイルから作る。命令メモリの先頭 `n` ワードを事前デコードする -/
def FTile32.ofTile (n : Nat) (t : Tile) : FTile32 where
  pc := ⟨t.arch.pc⟩
  regs := (Array.range 32).map fun k => ⟨t.arch.regs (BitVec.ofNat 5 k)⟩
  imem := t.imem
  icache := (Array.range n).map fun k => FI.ofT (tdecode (t.imem (BitVec.ofNat 32 (4 * k))))
  dmemBase := t.dmem
  dmem := {}
  out := #[⟨t.out .N⟩, ⟨t.out .S⟩, ⟨t.out .E⟩, ⟨t.out .W⟩]
  halted := t.halted

theorem FTile32.ofTile_abs (n : Nat) (t : Tile) : (FTile32.ofTile n t).abs = t := by
  obtain ⟨⟨pc, regs⟩, imem, dmem, out, halted⟩ := t
  simp only [FTile32.abs, FTile32.ofTile, archAbs, Tile.mk.injEq, Arch.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩
  · funext r
    have : r.toNat < 32 := by have := r.isLt; simpa using this
    rw [getElem!_pos _ _ (by simpa using this)]
    simp [BitVec.ofNat_toNat]
  · funext a; simp [dmemAbs]
  · exact ⟨by funext d; cases d <;> rfl, trivial⟩

theorem FTile32.ofTile_inv (n : Nat) (t : Tile) : (FTile32.ofTile n t).Inv := by
  refine ⟨by simp [FTile32.ofTile], by simp [FTile32.ofTile], ?_⟩
  intro k hk
  simp [FTile32.ofTile]

/-- UInt32 版のタイル実装 (`n` = 事前デコードするワード数) -/
def u32Impl (n : Nat) : TileImpl where
  S := FTile32
  dflt := default
  abs := FTile32.abs
  Inv := FTile32.Inv
  step := step32
  outRd t d := (t.out[dirIdx d]!).toBitVec
  halted := FTile32.halted
  ofTile := FTile32.ofTile n
  outRd_eq _ _ := rfl
  step_abs t inp h := step32_abs t inp h
  ofTile_abs := FTile32.ofTile_abs n
  ofTile_inv := FTile32.ofTile_inv n

/-- **主定理 (UInt32 版)**: 4×4 メッシュで、UInt32 版を k サイクル回した結果は仕様 `meshRun` と一致し、
イベント駆動 TLM とも一致する -/
theorem u32_correct_4x4 (n : Nat) (s0 : Fin 4 × Fin 4 → Tile) (k : Nat) :
    absMesh 4 4 (u32Impl n) (fmeshRun 4 4 (u32Impl n) k (meshOf 4 4 (u32Impl n) s0)) =
      meshRun (meshTopo 4 4) k s0 ∧
    ∃ m, ∀ i, ((run m (initSim (meshTopo 4 4) (meshTiles 4 4) s0)).st i).tile =
      absMesh 4 4 (u32Impl n) (fmeshRun 4 4 (u32Impl n) k (meshOf 4 4 (u32Impl n) s0)) i :=
  fast_correct 4 4 (u32Impl n) s0 (by decide) k

/-! ## UInt32 版専用のメッシュステップ (間接呼び出しなし)

一般版 `fmeshStep R C (u32Impl n)` は `TileImpl` のフィールド経由で間接呼び出しになる。
同じ定義を直接書いたものを用意し、定義上等しい (`rfl`) ことを示して実行に使う。 -/

section mesh32
variable (R C : Nat)

def fnbr32 (arr : Array FTile32) (i : Fin R × Fin C) (d : Dir) : Word :=
  match meshNbr R C i d with
  | some j => ((arr[idx R C j]!).out[dirIdx d.opp]!).toBitVec
  | none => 0

def mesh32Step (arr : Array FTile32) : Array FTile32 :=
  Array.ofFn (n := R * C) fun k => step32 arr[k.val]! (fnbr32 R C arr (toRC R C k))

theorem mesh32Step_eq (n : Nat) (arr : Array FTile32) : mesh32Step R C arr = fmeshStep R C (u32Impl n) arr := rfl

def mesh32Run : Nat → Array FTile32 → Array FTile32
  | 0, arr => arr
  | k + 1, arr => mesh32Run k (mesh32Step R C arr)

theorem mesh32Run_eq (n : Nat) : ∀ k arr, mesh32Run R C k arr = fmeshRun R C (u32Impl n) k arr
  | 0, _ => rfl
  | k + 1, arr => by simp only [mesh32Run, fmeshRun]; rw [mesh32Step_eq R C n]; exact mesh32Run_eq n k _

/-- **主定理 (専用版)**: 専用ステップで k サイクル回した結果は仕様 `meshRun` と一致 -/
theorem mesh32_correct (n : Nat) (s0 : Fin R × Fin C → Tile) (k : Nat) :
    absMesh R C (u32Impl n) (mesh32Run R C k (meshOf R C (u32Impl n) s0)) = meshRun (meshTopo R C) k s0 := by
  rw [mesh32Run_eq R C n]
  have h := fmeshRun_abs R C (u32Impl n) k _ (meshOf_inv R C (u32Impl n) s0)
  rw [absMesh_meshOf] at h
  exact h

def mesh32RunUntilHalt (fuel : Nat) (arr : Array FTile32) : Nat × Array FTile32 := Id.run do
  let mut a := arr
  let mut c := 0
  for _ in [0:fuel] do
    if a.all (·.halted) then break
    a := mesh32Step R C a
    c := c + 1
  return (c, a)

end mesh32

end Gem5.Fast32
