import Gem5Lean.SoC

/-! # SoC の実行テスト (ISA 仕様との differential test) -/

namespace Gem5.SoC.Test
open Gem5 Gem5.RV32 Gem5.RV32.Asm Gem5.SoC

/-- sum = Σ_{i=1}^{10} i を計算し、RAM1 (0x2000) に格納、読み戻して +1 -/
def prog : List Word :=
  [ addi 1 0 0        -- 0x00: x1 = 0
  , addi 2 0 10       -- 0x04: x2 = 10
  , add 1 1 2         -- 0x08: x1 += x2
  , addi 2 2 (-1)     -- 0x0c: x2 -= 1
  , bne 2 0 (-8)      -- 0x10: if x2 != 0 goto 0x08
  , lui 3 2           -- 0x14: x3 = 0x2000  (RAM1)
  , sw 3 1 0          -- 0x18: mem[x3] = x1
  , lw 4 3 0          -- 0x1c: x4 = mem[x3]
  , addi 4 4 1        -- 0x20: x4 += 1
  , halt ]            -- 0x24: illegal → 停止

def cfg (xl l0 l1 : Nat) : Config := ⟨fun a => decide (a.toNat < 0x1000), xl, l0, l1⟩

def arch0 : Arch := ⟨0, fun _ => 0⟩
def ram0 : Mem := loadProgram prog 0 (fun _ => 0)
def ram1 : Mem := fun _ => 0

def simulate (c : Config) (fuel : Nat) : SimState (soc c) := run fuel (initialState c arch0 ram0 ram1)

def summary (c : Config) : Nat × Nat × Nat × Nat × Bool :=
  let s := simulate c 1000
  let (cs, _, _, m1) := s.st
  (s.now, (cs.arch.get 1).toNat, (cs.arch.get 4).toNat, (m1 0x2000).toNat,
   match cs.phase with | .halted => true | _ => false)

-- (終了時刻, x1, x4, RAM1[0x2000], halted)
#eval summary (cfg 1 1 1)
#eval summary (cfg 2 3 20)     -- RAM1 が遅い構成
#eval summary (cfg 5 50 7)

#guard (summary (cfg 1 1 1)).2 == (55, 56, 55, true)
#guard (summary (cfg 2 3 20)).2 == (55, 56, 55, true)
#guard (summary (cfg 5 50 7)).2 == (55, 56, 55, true)

-- ISA 仕様側: 36 命令 (2 + 10×3 + 4) 実行後、次の命令で停止
def isaResult : Option (Nat × Nat × Nat) :=
  match isaRun 36 arch0 (flat (cfg 1 1 1) ram0 ram1) with
  | some (a, m) => some ((a.get 1).toNat, (a.get 4).toNat, (m 0x2000).toNat)
  | none => none
#eval isaResult
#guard isaResult == some (55, 56, 55)
#guard (isaStep (match isaRun 36 arch0 (flat (cfg 1 1 1) ram0 ram1) with
  | some (a, _) => a | none => arch0) (flat (cfg 1 1 1) ram0 ram1)).isNone

end Gem5.SoC.Test
