import Gem5Lean.TileTest
open Gem5 Gem5.RV32 Gem5.RV32.Asm Gem5.Tile Gem5.Tile.Test

def waveS0n (iters : Nat) : Fin 4 × Fin 4 → Tile := fun i =>
  mkTile waveProg [(10, if i.1.val = 0 ∧ i.2.val = 0 then 1 else 0), (11, iters)]

/-- TLM を最後まで走らせ、処理イベント数と最終時刻を返す -/
def tlmRun (iters : Nat) : Nat × Nat := Id.run do
  let mut σ := initSim wave (meshTiles 4 4) (waveS0n iters)
  let mut n := 0
  for _ in [0:100000000] do
    match step σ with
    | some σ' => σ := σ'; n := n + 1
    | none => break
  return (n, σ.now)

/-! 状態の詰め直し (外延的には恒等写像) -/
def regLook (a : Array Word) (i : BitVec 5) : Word := a[i.toNat]!
def dirLook (n s e w : Word) : Gem5.NoC.Dir → Word
  | .N => n | .S => s | .E => e | .W => w
def compactTile (t : Tile) : Tile :=
  { t with arch := { t.arch with regs := regLook ((List.range 32).toArray.map fun k => t.arch.regs (BitVec.ofNat 5 k)) },
           out := dirLook (t.out .N) (t.out .S) (t.out .E) (t.out .W) }
def compactI (x : TileI) : TileI :=
  ⟨compactTile x.tile, dirLook (x.mirror .N) (x.mirror .S) (x.mirror .E) (x.mirror .W)⟩
instance : Inhabited TileI := ⟨dummyTile⟩
def stLook (a : Array TileI) (i : Fin 4 × Fin 4) : TileI := a[i.1.val * 4 + i.2.val]!

def tlmRunCompact (iters every : Nat) : Nat × Nat := Id.run do
  let mut σ := initSim wave (meshTiles 4 4) (waveS0n iters)
  let mut n := 0
  for _ in [0:100000000] do
    match step σ with
    | some σ' =>
      σ := σ'; n := n + 1
      if n % every == 0 then
        let arr := (meshTiles 4 4).toArray.map fun i => compactI (σ.st i)
        σ := { σ with st := stLook arr }
    | none => break
  return (n, σ.now)

def main (args : List String) : IO Unit := do
  for it in args.map String.toNat! do
    let t0 ← IO.monoMsNow
    let (n, now) := tlmRun it
    let t1 ← IO.monoMsNow
    IO.println s!"[closure] iters={it} events={n} cycles={now/2} time_ms={t1-t0}"
    let t2 ← IO.monoMsNow
    let (n2, now2) := tlmRunCompact it 64
    let t3 ← IO.monoMsNow
    IO.println s!"[compact] iters={it} events={n2} cycles={now2/2} time_ms={t3-t2} ev_per_s={if t3 > t2 then n2*1000/(t3-t2) else 0}"
