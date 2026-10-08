import Gem5Lean.TileTest
open Gem5.Tile.Test
def main : IO Unit := for w in waveProg do IO.println (String.mk (Nat.toDigits 16 w.toNat))
