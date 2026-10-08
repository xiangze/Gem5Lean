import Gem5Lean.TileTest
import Gem5Lean.Fast32
open Gem5 Gem5.RV32 Gem5.RV32.Asm Gem5.Tile Gem5.Tile.Test

def waveS0n (iters : Nat) : Fin 4 × Fin 4 → Tile := fun i =>
  mkTile waveProg [(10, if i.1.val = 0 ∧ i.2.val = 0 then 1 else 0), (11, iters)]

def main (args : List String) : IO Unit := do
  let only32 := args.head? == some "u32"
  let args := if only32 then args.tail else args
  for it in args.map String.toNat! do
    let instrs := 16 * (8 * it + 2)
    do
      let t4 ← IO.monoMsNow
      let (cyc, arr) := Gem5.Fast32.mesh32RunUntilHalt 4 4 100000000 (Gem5.Fast.meshOf 4 4 (Gem5.Fast32.u32Impl 16) (waveS0n it))
      let t5 ← IO.monoMsNow
      let ms := t5 - t4
      IO.println s!"[u32-direct] iters={it} cycles={cyc} instrs={instrs} time_ms={ms} MIPS={if ms > 0 then (instrs * 10 / ms / 1000).toFloat / 10 else 0} dmem33={(Gem5.Fast.absMesh 4 4 (Gem5.Fast32.u32Impl 16) arr (3,3)).dmem 0x100 |>.toNat}"
    let impls := if only32 then [("u32", Gem5.Fast32.u32Impl 16)] else [("bitvec", Gem5.Fast.bvImpl), ("u32", Gem5.Fast32.u32Impl 16)]
    for (name, I) in impls do
      let t4 ← IO.monoMsNow
      let (cyc, arr) := Gem5.Fast.fmeshRunUntilHalt 4 4 I 100000000 (Gem5.Fast.meshOf 4 4 I (waveS0n it))
      let t5 ← IO.monoMsNow
      let ms := t5 - t4
      IO.println s!"[{name}] iters={it} cycles={cyc} instrs={instrs} time_ms={ms} MIPS={if ms > 0 then (instrs * 10 / ms / 1000).toFloat / 10 else 0} dmem33={(Gem5.Fast.absMesh 4 4 I arr (3,3)).dmem 0x100 |>.toNat}"
