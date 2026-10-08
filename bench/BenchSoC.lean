import Gem5Lean.SoCTest
open Gem5 Gem5.RV32 Gem5.RV32.Asm Gem5.SoC Gem5.SoC.Test

/-- 0x00: x1=0; x2=N; loop: x1+=x2; x2-=1; bne; ... (SoCTest.prog の N 可変版) -/
def progN (n : Nat) : List Word :=
  [ addi 1 0 0, lui 2 (n >>> 12), addi 2 2 (Int.ofNat (n % 4096)), add 1 1 2, addi 2 2 (-1), bne 2 0 (-8),
    lui 3 2, sw 3 1 0, lw 4 3 0, addi 4 4 1, halt ]

def regLook (a : Array Word) (i : BitVec 5) : Word := a[i.toNat]!
def compactArch (a : Arch) : Arch :=
  { a with regs := regLook ((List.range 32).toArray.map fun k => a.regs (BitVec.ofNat 5 k)) }

def runSoC (n : Nat) (compact : Bool) : Nat × Nat × Nat := Id.run do
  let c := cfg 1 1 1
  let ram0 := loadProgram (progN n) 0 (fun _ => 0)
  let mut σ := initialState c arch0 ram0 (fun _ => 0)
  let mut ev := 0
  for _ in [0:1000000000] do
    match step σ with
    | some σ' =>
      σ := σ'; ev := ev + 1
      if compact && ev % 256 == 0 then
        let (cs, x, m0, m1) := σ.st
        σ := { σ with st := ({ cs with arch := compactArch cs.arch }, x, m0, m1) }
    | none => break
  let (cs, _, _, _) := σ.st
  return (ev, (cs.arch.get 1).toNat, (cs.arch.get 4).toNat)

def main (args : List String) : IO Unit := do
  for n in args.map String.toNat! do
    for compact in [false, true] do
      if !compact && n > 20000 then continue
      let t0 ← IO.monoMsNow
      let (ev, x1, x4) := runSoC n compact
      let t1 ← IO.monoMsNow
      let instrs := 3 * n + 8
      let ms := t1 - t0
      IO.println s!"N={n} compact={compact} instrs={instrs} events={ev} x1={x1} x4={x4} time_ms={ms} KIPS={if ms > 0 then instrs / ms else 0}"
