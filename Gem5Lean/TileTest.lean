import Gem5Lean.Tile

/-! # TileRiscV メッシュの実行テスト

* 仕様 (同期メッシュ `meshStep`) と TLM (`meshSys` をイベント駆動で実行) を **毎サイクル** 突き合わせる
* レジスタ方式特有の「読むのが早すぎると古い値 (0) が見える」挙動を確認する
* RTL `TileRiscV.lean` の `mExtResult` (Int の `/` `%` = Euclid 除算) との差分を確認する
-/

namespace Gem5.Tile.Test
open Gem5 Gem5.RV32 Gem5.RV32.Asm Gem5.Tile
open Gem5.NoC (Dir)

/-! ## アセンブラ (RTL と同じエンコーディング) -/

def dirBits : Dir → Nat | .N => 0 | .S => 1 | .E => 2 | .W => 3

def tsend (d : Dir) (rs1 : Nat) : Word :=
  (BitVec.ofNat 7 1 ++ r 0 ++ r rs1 ++ BitVec.ofNat 3 (dirBits d) ++ r 0 ++ BitVec.ofNat 7 0x0B)
def trecv (rd : Nat) (d : Dir) : Word :=
  (BitVec.ofNat 7 0 ++ r 0 ++ r 0 ++ BitVec.ofNat 3 (dirBits d) ++ r rd ++ BitVec.ofNat 7 0x0B)

-- デコードの往復確認
#guard match tdecode (tsend .E 5) with | .send .E rs => rs == r 5 | _ => false
#guard match tdecode (trecv 7 .W) with | .recv rd .W => rd == r 7 | _ => false
#guard match tdecode (tsend .N 1) with | .send .N _ => true | _ => false
#guard match tdecode (trecv 1 .S) with | .recv _ .S => true | _ => false

/-! ## 実行用ヘルパ -/

def mkTile (prog : List Word) (regs : List (Nat × Nat)) : Tile where
  arch := ⟨0, fun i => match regs.find? (fun p => BitVec.ofNat 5 p.1 == i) with
                       | some (_, v) => BitVec.ofNat 32 v | none => 0⟩
  imem := loadProgram prog 0 (fun _ => 0)
  dmem := fun _ => 0
  out := fun _ => 0
  halted := false

/-! 仕様 `meshStep` は関数 `ι → Tile` 上の定義なので、そのまま何サイクルも回すと
閉包が入れ子になって指数的に再計算される。実行用には表 (データ) を持ち回す。 -/

def lookupD {ι : Type} [DecidableEq ι] (tbl : List (ι × Tile)) (i : ι) : Tile :=
  match tbl.find? (fun p => decide (p.1 = i)) with
  | some p => p.2
  | none => dummyTile.tile

theorem lookupD_map {ι : Type} [DecidableEq ι] (tiles : List ι) (f : ι → Tile) (i : ι) (hi : i ∈ tiles) :
    lookupD (tiles.map fun j => (j, f j)) i = f i := by
  simp only [lookupD]
  split
  · rename_i p hp
    have := List.find?_some hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hp)
    simp at this; subst this; rfl
  · rename_i hp
    have := List.find?_eq_none.mp hp (i, f i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
    simp at this

def specRunTbl {ι : Type} [DecidableEq ι] (T : Topology ι) (tiles : List ι) :
    Nat → List (ι × Tile) → List (ι × Tile)
  | 0, tbl => tbl
  | k + 1, tbl => specRunTbl T tiles k (tiles.map fun i => (i, meshStep T (lookupD tbl) i))

/-- 表による実行は仕様 `meshRun` そのもの -/
theorem specRunTbl_eq {ι : Type} [DecidableEq ι] (T : Topology ι) (tiles : List ι) (hall : ∀ i, i ∈ tiles) :
    ∀ k tbl, lookupD (specRunTbl T tiles k tbl) = meshRun T k (lookupD tbl)
  | 0, _ => rfl
  | k + 1, tbl => by
    simp only [specRunTbl, meshRun]
    rw [specRunTbl_eq T tiles hall k]
    have : lookupD (tiles.map fun i => (i, meshStep T (lookupD tbl) i)) = meshStep T (lookupD tbl) :=
      funext fun i => lookupD_map tiles _ i (hall i)
    rw [this]

def tbl0 {ι : Type} (tiles : List ι) (s0 : ι → Tile) : List (ι × Tile) := tiles.map fun i => (i, s0 i)

/-- 時刻 `limit` 未満のイベントだけを処理する -/
def runUntil {ι : Type} [DecidableEq ι] {T : Topology ι} (limit : Nat) :
    Nat → SimState (meshSys T) → SimState (meshSys T)
  | 0, σ => σ
  | fuel + 1, σ =>
    match σ.queue with
    | e :: _ => if e.time < limit then
                  match step σ with
                  | some σ' => runUntil limit fuel σ'
                  | none => σ
                else σ
    | [] => σ

def snap (t : Tile) : List Nat :=
  [t.arch.pc.toNat] ++ ((List.range 16).map fun k => (t.arch.get (BitVec.ofNat 5 k)).toNat) ++
  [t.out .N, t.out .S, t.out .E, t.out .W].map BitVec.toNat ++
  [(t.dmem 0x100).toNat, if t.halted then 1 else 0]

/-- 毎サイクル、全タイルの (アーキ状態, ミラー) を仕様と TLM で比較する。不一致のあったサイクルを返す -/
def diffCheck {ι : Type} [DecidableEq ι] (T : Topology ι) (tiles : List ι) (s0 : ι → Tile)
    (cycles : Nat) : List Nat := Id.run do
  let mut bad : List Nat := []
  let mut tbl := tbl0 tiles s0
  let mut σ := initSim T tiles s0
  for c in List.range (cycles + 1) do
    -- TLM: 時刻 2c 未満のイベントを全部処理した時点 = サイクル c の直前
    σ := runUntil (2 * c) 100000 σ
    let s := lookupD tbl
    let ok := tiles.all fun i =>
      snap (σ.st i).tile == snap (s i) &&
      [Dir.N, .S, .E, .W].all fun d => (σ.st i).mirror d == nbrOut T s i d
    if !ok then bad := bad ++ [c]
    tbl := tiles.map fun i => (i, meshStep T (lookupD tbl) i)
  return bad

/-! ## テスト 1: 1×4 の行でリレー (プレフィックス和) -/

def relayProg : List Word :=
  [ trecv 1 .W          -- 0x00: x1 ← west.out[E]
  , add 2 1 10          -- 0x04: x2 ← x1 + id
  , tsend .E 2          -- 0x08: out[E] ← x2
  , addi 11 11 (-1)     -- 0x0c
  , bne 11 0 (-16)      -- 0x10: 6 回ループ
  , sw 0 2 0x100        -- 0x14: dmem[0x100] ← x2
  , halt ]

def row4 : Topology (Fin 1 × Fin 4) := meshTopo 1 4
def row4s0 : Fin 1 × Fin 4 → Tile := fun i => mkTile relayProg [(10, i.2.val + 1), (11, 6)]

def finalDmem {ι : Type} [DecidableEq ι] (T : Topology ι) (tiles : List ι) (s0 : ι → Tile) (k : Nat) : List Nat :=
  let s := lookupD (specRunTbl T tiles k (tbl0 tiles s0))
  tiles.map fun i => (s i).dmem 0x100 |>.toNat

#eval finalDmem row4 (meshTiles 1 4) row4s0 60          -- [1, 3, 6, 10]
#guard finalDmem row4 (meshTiles 1 4) row4s0 60 == [1, 3, 6, 10]
#guard diffCheck row4 (meshTiles 1 4) row4s0 40 == []

/-! ## テスト 2: レジスタ方式のハザード (SEND と同じサイクルの RECV は古い値を読む) -/

def hazardS0 : Fin 1 × Fin 2 → Tile
  | (_, ⟨0, _⟩) => mkTile [tsend .E 10, halt] [(10, 7)]
  | (_, _)      => mkTile [trecv 1 .W, trecv 2 .W, halt] []

def hazardResult : Nat × Nat :=
  let s := lookupD (specRunTbl (meshTopo 1 2) (meshTiles 1 2) 5 (tbl0 (meshTiles 1 2) hazardS0))
  let t := s (0, 1)
  ((t.arch.get 1).toNat, (t.arch.get 2).toNat)

#eval hazardResult                  -- (0, 7): cycle 0 の RECV は 0、cycle 1 の RECV は 7
#guard hazardResult == (0, 7)
#guard diffCheck (meshTopo 1 2) (meshTiles 1 2) hazardS0 5 == []

/-! ## テスト 3: 4×4 全タイルの波面計算 (二項係数) -/

def waveProg : List Word :=
  [ trecv 1 .N          -- x1 ← north
  , trecv 2 .W          -- x2 ← west
  , add 3 1 2
  , add 3 3 10          -- (0,0) だけ x10 = 1
  , tsend .S 3
  , tsend .E 3
  , addi 11 11 (-1)
  , bne 11 0 (-28)      -- 10 回ループ
  , sw 0 3 0x100
  , halt ]

def wave : Topology (Fin 4 × Fin 4) := meshTopo 4 4
def waveS0 : Fin 4 × Fin 4 → Tile := fun i =>
  mkTile waveProg [(10, if i.1.val = 0 ∧ i.2.val = 0 then 1 else 0), (11, 10)]

#eval finalDmem wave (meshTiles 4 4) waveS0 100
-- C(r+c, r) を行優先で
#guard finalDmem wave (meshTiles 4 4) waveS0 100 == [1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6, 10, 1, 4, 10, 20]
#guard diffCheck wave (meshTiles 4 4) waveS0 90 == []

/-! ## RTL `mExtResult` との差分 (Int の `/` `%` は Euclid 除算) -/

def rtlDivS (a b : Word) : Word := BitVec.ofInt 32 (a.toInt / b.toInt)
def rtlRemS (a b : Word) : Word := BitVec.ofInt 32 (a.toInt % b.toInt)

#eval ((rtlDivS (BitVec.ofInt 32 (-7)) 2).toInt, (alu .div (BitVec.ofInt 32 (-7)) 2).toInt)  -- (-4, -3)
#eval ((rtlRemS (BitVec.ofInt 32 (-7)) 2).toInt, (alu .rem (BitVec.ofInt 32 (-7)) 2).toInt)  -- (1, -1)
#guard rtlDivS (BitVec.ofInt 32 (-7)) 2 != alu .div (BitVec.ofInt 32 (-7)) 2
#guard rtlRemS (BitVec.ofInt 32 (-7)) 2 != alu .rem (BitVec.ofInt 32 (-7)) 2
-- Int.tdiv / Int.tmod を使えば一致する
#guard BitVec.ofInt 32 ((BitVec.ofInt 32 (-7)).toInt.tdiv 2) == alu .div (BitVec.ofInt 32 (-7)) 2
#guard BitVec.ofInt 32 ((BitVec.ofInt 32 (-7)).toInt.tmod 2) == alu .rem (BitVec.ofInt 32 (-7)) 2

end Gem5.Tile.Test
