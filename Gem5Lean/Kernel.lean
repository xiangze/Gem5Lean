/-!
# Gem5Lean.Kernel — gem5 の SimObject / Port / EventQueue を Lean 4 で再定義する

gem5 との対応:

| gem5 (C++/Python)                    | ここ                                 |
|--------------------------------------|--------------------------------------|
| `SimObject` + `recvTimingReq/Resp`    | `Module.handle`                      |
| `RequestPort` / `ResponsePort` の名前 | `Module.O` / `Module.I`              |
| Python config (`a.port = b.port`)     | `Module.par` + `System.wire`         |
| `EventQueue` (tick, 挿入順 FIFO)      | `enqueue` / `schedule`               |
| `simulate()` のメインループ           | `step` / `run`                       |

実行可能な `step` と、非決定的な関係的意味論 `Step` の両方を与え、
`step_sound` で前者が後者の実装であることを証明する。
-/

namespace Gem5

abbrev Tick := Nat

/-! ## SimObject (Module) -/

/-- gem5 の SimObject に相当。`I` は入力ポート名、`O` は出力ポート名。
`handle` は 1 つのメッセージに反応し、新状態と「(遅延, 出力ポート, メッセージ)」のリストを返す。
(gem5 の `schedule(event, curTick() + latency)` に相当) -/
structure Module (M : Type) where
  I : Type
  O : Type
  State : Type
  init : State
  handle : I → M → State → State × List (Nat × O × M)

/-- 出力リストのポート名を写す補助関数 -/
def mapOuts {O O' M : Type} (f : O → O') (outs : List (Nat × O × M)) : List (Nat × O' × M) :=
  outs.map fun (d, o, m) => (d, f o, m)

/-- 2 つの SimObject の並列合成。ポート空間・状態空間は直和・直積。 -/
def Module.par {M : Type} (A B : Module M) : Module M where
  I := A.I ⊕ B.I
  O := A.O ⊕ B.O
  State := A.State × B.State
  init := (A.init, B.init)
  handle
    | .inl i, m, (a, b) => let r := A.handle i m a; ((r.1, b), mapOuts Sum.inl r.2)
    | .inr i, m, (a, b) => let r := B.handle i m b; ((a, r.1), mapOuts Sum.inr r.2)

/-- 合成のフレーム性: 左側へのメッセージは右側の状態を変えない (isolation) -/
theorem Module.par_frame_left {M} (A B : Module M) (i : A.I) (m : M) (a : A.State) (b : B.State) :
    ((A.par B).handle (.inl i) m (a, b)).1.2 = b := rfl

theorem Module.par_frame_right {M} (A B : Module M) (i : B.I) (m : M) (a : A.State) (b : B.State) :
    ((A.par B).handle (.inr i) m (a, b)).1.1 = a := rfl

/-- 閉じたシステム: すべての出力ポートがどこかの入力ポートに接続されている
(gem5 の Python config で全ポートを接続した状態) -/
structure System (M : Type) where
  mod : Module M
  wire : mod.O → mod.I

/-! ## Event queue -/

structure Event (P M : Type) where
  time : Tick
  port : P
  msg  : M

/-- 時刻順に挿入。同時刻は挿入順 (FIFO) — gem5 で同一 priority のイベントと同じ挙動 -/
def enqueue {P M} (e : Event P M) : List (Event P M) → List (Event P M)
  | [] => [e]
  | x :: xs => if e.time < x.time then e :: x :: xs else x :: enqueue e xs

def mkEv {M} (S : System M) (t : Tick) : Nat × S.mod.O × M → Event S.mod.I M
  | (d, o, m) => ⟨t + d, S.wire o, m⟩

def schedule {M} (S : System M) (t : Tick) :
    List (Nat × S.mod.O × M) → List (Event S.mod.I M) → List (Event S.mod.I M)
  | [], q => q
  | o :: os, q => schedule S t os (enqueue (mkEv S t o) q)

structure SimState {M} (S : System M) where
  now   : Tick
  queue : List (Event S.mod.I M)
  st    : S.mod.State

/-- 実行可能なシミュレーションの 1 ステップ: 先頭イベントを配送する -/
def step {M} {S : System M} (s : SimState S) : Option (SimState S) :=
  match s.queue with
  | [] => none
  | e :: q =>
    let r := S.mod.handle e.port e.msg s.st
    some { now := e.time, queue := schedule S e.time r.2 q, st := r.1 }

def run {M} {S : System M} : Nat → SimState S → SimState S
  | 0, s => s
  | n + 1, s => match step s with
    | none => s
    | some s' => run n s'

def SimState.initial {M} (S : System M) (q : List (Event S.mod.I M)) : SimState S :=
  { now := 0, queue := q, st := S.mod.init }

/-! ## 関係的意味論 (仕様) -/

/-- 非決定的な仕様: キュー中の「最小時刻」のイベントのどれを配送してもよい。
新しいキューは、残りのイベントと新規イベントの任意の並べ替え (multiset として一致) -/
inductive Step {M} (S : System M) : SimState S → SimState S → Prop
  | deliver {s : SimState S} {e : Event S.mod.I M} {rest q' : List (Event S.mod.I M)} :
      s.queue.Perm (e :: rest) →
      (∀ e' ∈ rest, e.time ≤ e'.time) →
      s.now ≤ e.time →
      q'.Perm ((S.mod.handle e.port e.msg s.st).2.map (mkEv S e.time) ++ rest) →
      Step S s ⟨e.time, q', (S.mod.handle e.port e.msg s.st).1⟩

/-! ## 補題 -/

section lemmas
variable {P M : Type}

def Sorted (q : List (Event P M)) : Prop := q.Pairwise (fun a b => a.time ≤ b.time)

theorem enqueue_perm (e : Event P M) : ∀ q, (enqueue e q).Perm (e :: q)
  | [] => .refl _
  | x :: xs => by
    unfold enqueue
    split
    · exact .refl _
    · exact (List.Perm.cons x (enqueue_perm e xs)).trans (List.Perm.swap e x xs)

theorem mem_enqueue {e x : Event P M} {q} : x ∈ enqueue e q ↔ x = e ∨ x ∈ q := by
  rw [(enqueue_perm e q).mem_iff]; simp

theorem enqueue_sorted (e : Event P M) : ∀ q, Sorted q → Sorted (enqueue e q)
  | [], _ => by simp [enqueue, Sorted]
  | x :: xs, h => by
    unfold Sorted at h
    rw [List.pairwise_cons] at h
    unfold enqueue
    split
    · rename_i hlt
      unfold Sorted
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, h.1, h.2⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_of_lt hlt
      · exact Nat.le_trans (Nat.le_of_lt hlt) (h.1 y hy)
    · rename_i hge
      unfold Sorted
      rw [List.pairwise_cons]
      refine ⟨?_, enqueue_sorted e xs h.2⟩
      intro y hy
      rcases mem_enqueue.mp hy with rfl | hy
      · exact Nat.le_of_not_lt hge
      · exact h.1 y hy

end lemmas

section sched
variable {M : Type} (S : System M)

theorem schedule_perm (t : Tick) :
    ∀ outs q, (schedule S t outs q).Perm (outs.map (mkEv S t) ++ q)
  | [], q => by simp [schedule]
  | o :: os, q => by
    simp only [schedule, List.map_cons, List.cons_append]
    refine (schedule_perm t os _).trans ?_
    refine ((List.Perm.append_left _ (enqueue_perm _ q))).trans ?_
    exact List.perm_middle

theorem schedule_sorted (t : Tick) :
    ∀ outs q, Sorted q → Sorted (schedule S t outs q)
  | [], _, h => h
  | _ :: os, q, h => schedule_sorted t os _ (enqueue_sorted _ q h)

theorem mem_schedule {t : Tick} {outs q x} :
    x ∈ schedule S t outs q ↔ x ∈ outs.map (mkEv S t) ∨ x ∈ q := by
  rw [(schedule_perm S t outs q).mem_iff, List.mem_append]

theorem mkEv_time {t : Tick} {o} : t ≤ (mkEv S t o).time := by
  obtain ⟨d, p, m⟩ := o; simp [mkEv]

end sched

/-! ## 主定理 -/

/-- 整合性不変条件: キューが時刻順で、すべて現在時刻以降 -/
def WF {M} {S : System M} (s : SimState S) : Prop :=
  Sorted s.queue ∧ ∀ e ∈ s.queue, s.now ≤ e.time

theorem initial_wf {M} (S : System M) (q) (h : Sorted q) : WF (SimState.initial S q) :=
  ⟨h, fun _ _ => Nat.zero_le _⟩

theorem step_none_iff {M} {S : System M} (s : SimState S) : step s = none ↔ s.queue = [] := by
  unfold step; split <;> simp_all

/-- 不変条件の保存 -/
theorem step_wf {M} {S : System M} {s s' : SimState S} (hwf : WF s) (h : step s = some s') :
    WF s' := by
  obtain ⟨hs, hge⟩ := hwf
  unfold step at h
  split at h
  · contradiction
  · rename_i e q hq
    cases h
    rw [hq] at hs
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    refine ⟨schedule_sorted S _ _ _ hs.2, ?_⟩
    intro x hx
    rcases (mem_schedule S).mp hx with hx | hx
    · obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
      exact mkEv_time S
    · exact hs.1 x hx

/-- シミュレーション時刻は単調非減少 (因果律) -/
theorem step_mono {M} {S : System M} {s s' : SimState S} (hwf : WF s) (h : step s = some s') :
    s.now ≤ s'.now := by
  unfold step at h
  split at h
  · contradiction
  · rename_i e q hq
    cases h
    exact hwf.2 e (by rw [hq]; simp)

/-- 実行可能なカーネルは関係的仕様を実装する -/
theorem step_sound {M} {S : System M} {s s' : SimState S} (hwf : WF s) (h : step s = some s') :
    Step S s s' := by
  have hmono := step_mono hwf h
  obtain ⟨hs, _⟩ := hwf
  unfold step at h
  split at h
  · contradiction
  · rename_i e q hq
    cases h
    rw [hq] at hs
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    exact Step.deliver (by rw [hq]) hs.1 hmono (schedule_perm S _ _ _)

/-- 進行性: 仕様上ステップ可能なら、カーネルも止まらない -/
theorem step_progress {M} {S : System M} {s s' : SimState S} (h : Step S s s') :
    (step s).isSome := by
  cases h with
  | deliver hp _ _ _ =>
    cases hq : s.queue with
    | nil => rw [hq] at hp; exact absurd hp.length_eq (by simp)
    | cons _ _ => simp [step, hq]

/-- 複数ステップ実行でも不変条件と時刻単調性が保たれる -/
theorem run_wf {M} {S : System M} : ∀ n (s : SimState S), WF s → WF (run n s) ∧ s.now ≤ (run n s).now
  | 0, s, h => ⟨h, Nat.le_refl _⟩
  | n + 1, s, h => by
    unfold run
    split
    · exact ⟨h, Nat.le_refl _⟩
    · rename_i s' hs'
      have ⟨h1, h2⟩ := run_wf n s' (step_wf h hs')
      exact ⟨h1, Nat.le_trans (step_mono h hs') h2⟩

end Gem5
