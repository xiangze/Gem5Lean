import Gem5Lean.Kernel
import Gem5Lean.RV32

/-!
# Gem5Lean.SoC — 最小 SoC: TimingCPU + NoncoherentXBar + 2 × SimpleMemory

```
            ┌──────┐ req  ┌──────┐ req (addr∈R0) ┌──────┐
            │ CPU  │─────▶│ XBar │──────────────▶│ RAM0 │
            │      │◀─────│      │◀──────────────│      │
            └──────┘ resp │      │ req (else)    ├──────┤
                          │      │──────────────▶│ RAM1 │
                          │      │◀──────────────│      │
                          └──────┘               └──────┘
```

gem5 の Python config に相当するのが `soc` (Module.par による合成 + 配線)。
レイテンシ (`xbarLat`, `lat0`, `lat1`) は任意のパラメータで、
**機能的正しさはレイテンシに依存しない**ことを証明する。

主定理 `soc_refines_isa`: 静止状態から k 命令を ISA 仕様で実行した結果と、
TLM シミュレータを有限ステップ実行した結果が (抽象化関数を通して) 一致する。
-/

namespace Gem5.SoC
open Gem5 Gem5.RV32

inductive MemCmd | readReq | writeReq | readResp | writeResp
  deriving DecidableEq, Repr

structure Packet where
  cmd  : MemCmd
  addr : Word
  data : Word

/-! ## CPU -/

inductive Phase
  | fetch                 -- 命令フェッチ応答待ち
  | load (rd : Reg)       -- LW 応答待ち
  | store                 -- SW 応答待ち
  | halted

structure CpuSt where
  arch  : Arch
  phase : Phase

def fetchReq (pc : Word) : Packet := ⟨.readReq, pc, 0⟩

/-- 次の命令フェッチを発行 -/
def CpuSt.issueFetch (a : Arch) : CpuSt × List (Nat × Unit × Packet) :=
  (⟨a, .fetch⟩, [(1, (), fetchReq a.pc)])

def cpuHandle (pkt : Packet) (s : CpuSt) : CpuSt × List (Nat × Unit × Packet) :=
  match s.phase with
  | .fetch =>
    match exec (decode pkt.data) s.arch with
    | none => (⟨s.arch, .halted⟩, [])
    | some (a', .none) => CpuSt.issueFetch a'
    | some (a', .load rd addr) => (⟨a', .load rd⟩, [(1, (), ⟨.readReq, addr, 0⟩)])
    | some (a', .store addr v) => (⟨a', .store⟩, [(1, (), ⟨.writeReq, addr, v⟩)])
  | .load rd => CpuSt.issueFetch (s.arch.set rd pkt.data)
  | .store => CpuSt.issueFetch s.arch
  | .halted => (s, [])

def cpu (a0 : Arch) : Module Packet where
  I := Unit; O := Unit; State := CpuSt
  init := ⟨a0, .fetch⟩
  handle _ pkt s := cpuHandle pkt s

/-! ## Crossbar -/

inductive XIn  | cpuSide | memSide0 | memSide1
inductive XOut | toMem0 | toMem1 | toCpu

def xbar (inR0 : Word → Bool) (lat : Nat) : Module Packet where
  I := XIn; O := XOut; State := Unit
  init := ()
  handle
    | .cpuSide,  pkt, _ => ((), [(lat, if inR0 pkt.addr then .toMem0 else .toMem1, pkt)])
    | .memSide0, pkt, _ => ((), [(lat, .toCpu, pkt)])
    | .memSide1, pkt, _ => ((), [(lat, .toCpu, pkt)])

/-! ## SimpleMemory -/

def memHandle (lat : Nat) (pkt : Packet) (m : Mem) : Mem × List (Nat × Unit × Packet) :=
  match pkt.cmd with
  | .readReq  => (m, [(lat, (), ⟨.readResp, pkt.addr, m pkt.addr⟩)])
  | .writeReq => (m.write pkt.addr pkt.data, [(lat, (), ⟨.writeResp, pkt.addr, pkt.data⟩)])
  | _ => (m, [])

def simpleMem (m0 : Mem) (lat : Nat) : Module Packet where
  I := Unit; O := Unit; State := Mem
  init := m0
  handle _ pkt m := memHandle lat pkt m

/-! ## Python config 相当: 合成と配線 -/

structure Config where
  inR0 : Word → Bool
  xbarLat : Nat
  lat0 : Nat
  lat1 : Nat

def socMod (c : Config) (a0 : Arch) (m0 m1 : Mem) : Module Packet :=
  (cpu a0).par ((xbar c.inR0 c.xbarLat).par ((simpleMem m0 c.lat0).par (simpleMem m1 c.lat1)))

/-- `system.cpu.port = system.membus.cpu_side_ports` などに相当 -/
def socWire (c : Config) (a0 : Arch) (m0 m1 : Mem) : (socMod c a0 m0 m1).O → (socMod c a0 m0 m1).I
  | .inl ()                    => .inr (.inl .cpuSide)
  | .inr (.inl .toMem0)        => .inr (.inr (.inl ()))
  | .inr (.inl .toMem1)        => .inr (.inr (.inr ()))
  | .inr (.inl .toCpu)         => .inl ()
  | .inr (.inr (.inl ()))      => .inr (.inl .memSide0)
  | .inr (.inr (.inr ()))      => .inr (.inl .memSide1)

/-- システム全体。初期値は「型」を決めるためだけに使う (状態は SimState 側) -/
def soc (c : Config) : System Packet where
  mod  := socMod c ⟨0, fun _ => 0⟩ (fun _ => 0) (fun _ => 0)
  wire := socWire c _ _ _

/-! ## 抽象化 -/

/-- 分割された 2 つのメモリをフラットなアドレス空間として見る -/
def flat (c : Config) (m0 m1 : Mem) : Mem := fun a => if c.inR0 a then m0 a else m1 a

def pCpuSide (c : Config) : (soc c).mod.I := .inr (.inl .cpuSide)
def pCpu (c : Config) : (soc c).mod.I := .inl ()

/-- 静止状態: CPU がフェッチ要求を発行した直後で、キューにはそれだけがある -/
def quiescent (c : Config) (t : Nat) (a : Arch) (m0 m1 : Mem) : SimState (soc c) where
  now := t
  queue := [⟨t + 1, pCpuSide c, fetchReq a.pc⟩]
  st := (⟨a, .fetch⟩, (), m0, m1)

/-- 停止状態 -/
def haltedState (c : Config) (t : Nat) (a : Arch) (m0 m1 : Mem) : SimState (soc c) where
  now := t
  queue := []
  st := (⟨a, .halted⟩, (), m0, m1)

def initialState (c : Config) (a : Arch) (m0 m1 : Mem) : SimState (soc c) := quiescent c 0 a m0 m1

/-! ## メモリ補題 -/

theorem flat_write0 (c : Config) (m0 m1 : Mem) (a v : Word) (h : c.inR0 a = true) :
    flat c (m0.write a v) m1 = (flat c m0 m1).write a v := by
  funext x; simp only [flat, Mem.write]; by_cases hx : x = a <;> simp_all

theorem flat_write1 (c : Config) (m0 m1 : Mem) (a v : Word) (h : c.inR0 a = false) :
    flat c m0 (m1.write a v) = (flat c m0 m1).write a v := by
  funext x; simp only [flat, Mem.write]; by_cases hx : x = a <;> simp_all

/-! ## 1 回のメモリトランザクション (4 イベント) -/


/-! ## 1 回のメモリトランザクション: CPU → XBar → RAM_i → XBar → (CPU 手前) の 3 イベント -/

attribute [local simp] run step schedule enqueue mkEv soc socMod socWire Module.par xbar simpleMem
  memHandle mapOuts pCpu pCpuSide cpu

/-- 読み出し: どちらの RAM に振り分けられても、戻ってくる値はフラットメモリの値 -/
theorem txnRead (c : Config) (t : Nat) (cs : CpuSt) (m0 m1 : Mem) (a d : Word) :
    ∃ tA tB, run 3 (⟨t, [⟨t + 1, pCpuSide c, ⟨.readReq, a, d⟩⟩], (cs, (), m0, m1)⟩ : SimState (soc c)) =
      ⟨tA, [⟨tB, pCpu c, ⟨.readResp, a, flat c m0 m1 a⟩⟩], (cs, (), m0, m1)⟩ := by
  cases hr : c.inR0 a
  · exact ⟨t + 1 + c.xbarLat + c.lat1, t + 1 + c.xbarLat + c.lat1 + c.xbarLat, by simp [hr, flat]⟩
  · exact ⟨t + 1 + c.xbarLat + c.lat0, t + 1 + c.xbarLat + c.lat0 + c.xbarLat, by simp [hr, flat]⟩

/-- 書き込み: 振り分け先の RAM が更新され、フラットメモリとしては 1 ワード書き込みと一致 -/
theorem txnWrite (c : Config) (t : Nat) (cs : CpuSt) (m0 m1 : Mem) (a v : Word) :
    ∃ tA tB m0' m1',
      run 3 (⟨t, [⟨t + 1, pCpuSide c, ⟨.writeReq, a, v⟩⟩], (cs, (), m0, m1)⟩ : SimState (soc c)) =
        ⟨tA, [⟨tB, pCpu c, ⟨.writeResp, a, v⟩⟩], (cs, (), m0', m1')⟩ ∧
      flat c m0' m1' = (flat c m0 m1).write a v := by
  cases hr : c.inR0 a
  · exact ⟨t + 1 + c.xbarLat + c.lat1, t + 1 + c.xbarLat + c.lat1 + c.xbarLat, m0, m1.write a v,
      by simp [hr], flat_write1 c m0 m1 a v hr⟩
  · exact ⟨t + 1 + c.xbarLat + c.lat0, t + 1 + c.xbarLat + c.lat0 + c.xbarLat, m0.write a v, m1,
      by simp [hr], flat_write0 c m0 m1 a v hr⟩

/-- CPU へのイベント配送 1 回 -/
theorem cpuStep (c : Config) (tA tB : Nat) (cs : CpuSt) (m0 m1 : Mem) (pkt : Packet) :
    run 1 (⟨tA, [⟨tB, pCpu c, pkt⟩], (cs, (), m0, m1)⟩ : SimState (soc c)) =
      ⟨tB, schedule (soc c) tB (mapOuts Sum.inl (cpuHandle pkt cs).2) [], ((cpuHandle pkt cs).1, (), m0, m1)⟩ := by
  simp

theorem issue_eq (c : Config) (t : Nat) (a : Arch) (m0 m1 : Mem) :
    (⟨t, schedule (soc c) t (mapOuts Sum.inl (CpuSt.issueFetch a).2) [], ((CpuSt.issueFetch a).1, (), m0, m1)⟩
      : SimState (soc c)) = quiescent c t a m0 m1 := by
  simp [CpuSt.issueFetch, quiescent]

/-! ## 主定理 -/

/-- **1 命令の refinement**:
静止状態から、ISA 仕様が停止しなければ TLM システムは有限ステップで次の静止状態に到達し、
アーキテクチャ状態とフラットメモリが ISA 仕様の結果と一致する。
ISA 仕様が停止するなら、TLM システムも (キューが空の) 停止状態になる。
これはレイテンシ (`c.xbarLat`, `c.lat0`, `c.lat1`) とアドレスマップ `c.inR0` によらない。 -/
theorem instr_refines (c : Config) (t : Nat) (a : Arch) (m0 m1 : Mem) :
    match isaStep a (flat c m0 m1) with
    | none => ∃ n t', run n (quiescent c t a m0 m1) = haltedState c t' a m0 m1
    | some (a', m') => ∃ n t' m0' m1',
        run n (quiescent c t a m0 m1) = quiescent c t' a' m0' m1' ∧ flat c m0' m1' = m' := by
  obtain ⟨tA, tB, h1⟩ := txnRead c t ⟨a, .fetch⟩ m0 m1 a.pc 0
  have hq : quiescent c t a m0 m1 =
      (⟨t, [⟨t + 1, pCpuSide c, ⟨.readReq, a.pc, 0⟩⟩], (⟨a, .fetch⟩, (), m0, m1)⟩ : SimState (soc c)) := rfl
  unfold isaStep
  cases hx : exec (decode (flat c m0 m1 a.pc)) a with
  | none =>
    refine ⟨3 + 1, tB, ?_⟩
    rw [run_add, hq, h1, cpuStep]
    simp [cpuHandle, hx, schedule, haltedState]
  | some p =>
    obtain ⟨a', op⟩ := p
    cases op with
    | none =>
      refine ⟨3 + 1, tB, m0, m1, ?_, rfl⟩
      rw [run_add, hq, h1, cpuStep]
      simp only [cpuHandle, hx]
      exact issue_eq c tB a' m0 m1
    | load rd addr =>
      have h2 : run 1 (⟨tA, [⟨tB, pCpu c, ⟨.readResp, a.pc, flat c m0 m1 a.pc⟩⟩], (⟨a, .fetch⟩, (), m0, m1)⟩
          : SimState (soc c)) =
          ⟨tB, [⟨tB + 1, pCpuSide c, ⟨.readReq, addr, 0⟩⟩], (⟨a', .load rd⟩, (), m0, m1)⟩ := by
        rw [cpuStep]; simp [cpuHandle, hx]
      obtain ⟨tC, tD, h3⟩ := txnRead c tB ⟨a', .load rd⟩ m0 m1 addr 0
      refine ⟨3 + (1 + (3 + 1)), tD, m0, m1, ?_, rfl⟩
      rw [run_add, hq, h1, run_add, h2, run_add, h3, cpuStep]
      simp only [cpuHandle]
      exact issue_eq c tD _ m0 m1
    | store addr v =>
      have h2 : run 1 (⟨tA, [⟨tB, pCpu c, ⟨.readResp, a.pc, flat c m0 m1 a.pc⟩⟩], (⟨a, .fetch⟩, (), m0, m1)⟩
          : SimState (soc c)) =
          ⟨tB, [⟨tB + 1, pCpuSide c, ⟨.writeReq, addr, v⟩⟩], (⟨a', .store⟩, (), m0, m1)⟩ := by
        rw [cpuStep]; simp [cpuHandle, hx]
      obtain ⟨tC, tD, m0', m1', h3, hf⟩ := txnWrite c tB ⟨a', .store⟩ m0 m1 addr v
      refine ⟨3 + (1 + (3 + 1)), tD, m0', m1', ?_, hf⟩
      rw [run_add, hq, h1, run_add, h2, run_add, h3, cpuStep]
      simp only [cpuHandle]
      exact issue_eq c tD _ m0' m1'

/-- **k 命令の refinement** (主定理): ISA 仕様で k 命令実行できるなら、
TLM SoC も有限ステップでそれと同じ状態 (抽象化を通して) の静止状態に到達する -/
theorem soc_refines_isa (c : Config) :
    ∀ (k : Nat) (t : Nat) (a a' : Arch) (m0 m1 m' : Mem),
      isaRun k a (flat c m0 m1) = some (a', m') →
      ∃ n t' m0' m1', run n (quiescent c t a m0 m1) = quiescent c t' a' m0' m1' ∧ flat c m0' m1' = m'
  | 0, t, a, a', m0, m1, m', h => by
    simp [isaRun] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, t, m0, m1, rfl, rfl⟩
  | k + 1, t, a, a', m0, m1, m', h => by
    simp only [isaRun] at h
    have hi := instr_refines c t a m0 m1
    split at h
    · contradiction
    · rename_i a1 mm1 hs
      rw [hs] at hi
      obtain ⟨n1, t1, m01, m11, hr1, hf1⟩ := hi
      rw [← hf1] at h
      obtain ⟨n2, t2, m02, m12, hr2, hf2⟩ := soc_refines_isa c k t1 a1 a' m01 m11 m' h
      exact ⟨n1 + n2, t2, m02, m12, by rw [run_add, hr1, hr2], hf2⟩

/-- 停止の対応: ISA 仕様が k 命令目で停止するなら TLM SoC も停止状態に到達する -/
theorem soc_halts (c : Config) (t : Nat) (a : Arch) (m0 m1 : Mem) (h : isaStep a (flat c m0 m1) = none) :
    ∃ n t', run n (quiescent c t a m0 m1) = haltedState c t' a m0 m1 := by
  have hi := instr_refines c t a m0 m1
  rw [h] at hi
  exact hi

end Gem5.SoC
