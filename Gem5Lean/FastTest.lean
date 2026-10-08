import Gem5Lean.Fast32
import Gem5Lean.TileTest

/-! # 高速版のテスト: 仕様 (表による実行) と毎サイクル比較 (BitVec 版 / UInt32 版) -/

namespace Gem5.Fast.Test
open Gem5 Gem5.RV32 Gem5.Tile Gem5.Tile.Test Gem5.Fast Gem5.Fast32

def diffFast (I : TileImpl) (R C : Nat) (s0 : Fin R × Fin C → Tile) (cycles : Nat) : List Nat := Id.run do
  let tiles := meshTiles R C
  let mut tbl := tbl0 tiles s0
  let mut arr := meshOf R C I s0
  let mut bad : List Nat := []
  for c in List.range (cycles + 1) do
    let s := lookupD tbl
    let ok := tiles.all fun i => snap (absMesh R C I arr i) == snap (s i)
    if !ok then bad := bad ++ [c]
    tbl := tiles.map fun i => (i, meshStep (meshTopo R C) (lookupD tbl) i)
    arr := fmeshStep R C I arr
  return bad

def fastDmem (I : TileImpl) (R C : Nat) (s0 : Fin R × Fin C → Tile) : List Nat :=
  let (_, arr) := fmeshRunUntilHalt R C I 100000 (meshOf R C I s0)
  (meshTiles R C).map fun i => (absMesh R C I arr i).dmem 0x100 |>.toNat

-- BitVec 版
#guard diffFast bvImpl 1 4 row4s0 40 == []
#guard diffFast bvImpl 1 2 hazardS0 5 == []
#guard diffFast bvImpl 4 4 waveS0 90 == []
#guard fastDmem bvImpl 4 4 waveS0 == [1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6, 10, 1, 4, 10, 20]

-- UInt32 版 (先頭 16 ワードを事前デコード)
#guard diffFast (u32Impl 16) 1 4 row4s0 40 == []
#guard diffFast (u32Impl 16) 1 2 hazardS0 5 == []
#guard diffFast (u32Impl 16) 4 4 waveS0 90 == []
#guard fastDmem (u32Impl 16) 4 4 waveS0 == [1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6, 10, 1, 4, 10, 20]
#guard fastDmem (u32Impl 16) 1 4 row4s0 == [1, 3, 6, 10]
-- キャッシュ外 (n = 2) でもフォールバックで正しく動く
#guard diffFast (u32Impl 2) 4 4 waveS0 90 == []

/-! RV32M・分岐・ロード/ストアを網羅する追加テスト (1×1) -/
open Gem5.RV32.Asm in
def mixProg : List Word :=
  [ addi 1 0 (-7), addi 2 0 2, div 3 1 2, rem 4 1 2, mul 5 1 2,
    encR 0x20 5 6 1 2,          -- sra
    encR 0 2 7 1 2,             -- slt
    encR 0 3 8 1 2,             -- sltu
    encR 1 1 9 1 2,             -- mulh
    sw 0 5 0x40, lw 10 0 0x40,
    encB 4 1 2 8,               -- blt x1, x2, +8 (taken)
    addi 11 0 99,               -- skipped
    addi 12 0 1,
    halt ]
def mixS0 : Fin 1 × Fin 1 → Tile := fun _ => mkTile mixProg []
#guard diffFast bvImpl 1 1 mixS0 20 == []
#guard diffFast (u32Impl 16) 1 1 mixS0 20 == []
#eval (let (_, arr) := fmeshRunUntilHalt 1 1 (u32Impl 16) 100 (meshOf 1 1 (u32Impl 16) mixS0)
       (List.range 13).map fun k => ((absMesh 1 1 (u32Impl 16) arr (0, 0)).arch.get (BitVec.ofNat 5 k)).toInt)

-- UInt32 専用ステップ (`mesh32Step`) も仕様と毎サイクル一致
def diff32 (R C : Nat) (s0 : Fin R × Fin C → Tile) (cycles : Nat) : List Nat := Id.run do
  let tiles := meshTiles R C
  let mut tbl := tbl0 tiles s0
  let mut arr := meshOf R C (u32Impl 16) s0
  let mut bad : List Nat := []
  for c in List.range (cycles + 1) do
    let s := lookupD tbl
    if !(tiles.all fun i => snap (absMesh R C (u32Impl 16) arr i) == snap (s i)) then bad := bad ++ [c]
    tbl := tiles.map fun i => (i, meshStep (meshTopo R C) (lookupD tbl) i)
    arr := mesh32Step R C arr
  return bad
#guard diff32 4 4 waveS0 90 == []
#guard diff32 1 1 mixS0 20 == []
-- 破壊的更新版 (`fmeshStepFast`) も一致
#guard (List.range 40).all fun k =>
  let a := fmeshRun 4 4 (u32Impl 16) k (meshOf 4 4 (u32Impl 16) waveS0)
  (meshTiles 4 4).all fun i =>
    snap (absMesh 4 4 (u32Impl 16) (fmeshStepFast 4 4 (u32Impl 16) a) i) ==
    snap (absMesh 4 4 (u32Impl 16) (fmeshStep 4 4 (u32Impl 16) a) i)

end Gem5.Fast.Test
