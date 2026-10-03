/-!
# Gem5Lean.Port — gem5 timing-mode port protocol

gem5 の timing モードでは

* requestor が `sendTimingReq(pkt)` を呼び、responder は `true`(受理) か `false`(拒否) を返す
* 拒否した responder は、後で必ず `sendRetryReq()` を呼ぶ義務を負う
* requestor は retry を受け取るまで再送してはいけない
* responder は受理した要求にだけ `sendTimingResp` を返す

この規則をモニタ (`pstep`) として定義し、

1. モニタが受理するトレースでは「応答数 ≤ 受理要求数」
2. 有限バッファの responder (SimpleMemory 型) と標準的な requestor の組は、
   **任意のスケジュール**でプロトコル違反を起こさず、retry を取りこぼさない (lost-retry deadlock がない)
3. retry 義務を忘れる buggy responder ではデッドロック状態に到達する (反例)

を証明する。
-/

namespace Gem5.Port

inductive PEv
  | sendReq (accepted : Bool)
  | retry
  | resp
  deriving DecidableEq, Repr

structure Mon where
  outstanding : Nat
  blocked : Bool
  deriving DecidableEq, Repr

/-- プロトコルモニタ。`none` はプロトコル違反 -/
def pstep (m : Mon) : PEv → Option Mon
  | .sendReq true  => if m.blocked then none else some { m with outstanding := m.outstanding + 1 }
  | .sendReq false => if m.blocked then none else some { m with blocked := true }
  | .retry         => if m.blocked then some { m with blocked := false } else none
  | .resp          => if m.outstanding = 0 then none else some { m with outstanding := m.outstanding - 1 }

def check : Mon → List PEv → Option Mon
  | m, [] => some m
  | m, e :: es => (pstep m e).bind (check · es)

def Mon.init : Mon := ⟨0, false⟩

def countAcc : List PEv → Nat
  | [] => 0
  | .sendReq true :: es => countAcc es + 1
  | _ :: es => countAcc es

def countResp : List PEv → Nat
  | [] => 0
  | .resp :: es => countResp es + 1
  | _ :: es => countResp es

/-- モニタの outstanding は「受理数 − 応答数」をちょうど数えている -/
theorem check_outstanding : ∀ (tr : List PEv) (m m' : Mon), check m tr = some m' →
    m'.outstanding + countResp tr = m.outstanding + countAcc tr
  | [], m, m', h => by cases h; simp [countResp, countAcc]
  | e :: es, m, m', h => by
    simp only [check, Option.bind_eq_some_iff] at h
    obtain ⟨m1, h1, h2⟩ := h
    have ih := check_outstanding es m1 m' h2
    cases e with
    | sendReq a =>
      cases a <;> simp only [pstep] at h1 <;> split at h1 <;> cases h1 <;>
        simp only [countResp, countAcc] at ih ⊢ <;> omega
    | retry => simp only [pstep] at h1; split at h1 <;> cases h1; simp only [countResp, countAcc]; omega
    | resp =>
      simp only [pstep] at h1; split at h1
      · cases h1
      · cases h1; simp only [countResp, countAcc] at ih ⊢; omega

/-- 合法なトレースでは、要求されていない応答は存在しない -/
theorem legal_resp_le_acc (tr : List PEv) (h : (check Mon.init tr).isSome) :
    countResp tr ≤ countAcc tr := by
  cases hc : check Mon.init tr with
  | none => simp [hc] at h
  | some m' => have := check_outstanding tr _ _ hc; simp [Mon.init] at this; omega

/-! ## requestor + 有限バッファ responder の合成 -/

/-- 結合状態 -/
structure Joint where
  blocked : Bool   -- requestor は retry 待ち
  owes    : Bool   -- responder は retry を送る義務を負っている
  queue   : Nat    -- responder のバッファ使用量 (= 応答待ち要求数)
  deriving DecidableEq, Repr

/-- スケジューラの選択: requestor を動かすか responder を動かすか -/
inductive Sched | issue | serve
  deriving DecidableEq, Repr

/-- 正しい responder (gem5 SimpleMemory の `retryReq` フラグ相当) -/
def jstep (cap : Nat) (s : Joint) : Sched → Joint × List PEv
  | .issue =>
    if s.blocked then (s, [])
    else if s.queue < cap then ({ s with queue := s.queue + 1 }, [.sendReq true])
    else ({ s with blocked := true, owes := true }, [.sendReq false])
  | .serve =>
    if s.queue = 0 then (s, [])
    else if s.owes then ({ blocked := false, owes := false, queue := s.queue - 1 }, [.resp, .retry])
    else ({ s with queue := s.queue - 1 }, [.resp])

def jrun (cap : Nat) : Joint → List Sched → Joint × List PEv
  | s, [] => (s, [])
  | s, c :: cs =>
    let r1 := jstep cap s c
    let r2 := jrun cap r1.1 cs
    (r2.1, r1.2 ++ r2.2)

def Joint.init : Joint := ⟨false, false, 0⟩

/-- 結合不変条件。特に `blocked = owes` が「retry の取りこぼしなし」 -/
def Inv (cap : Nat) (s : Joint) : Prop :=
  s.blocked = s.owes ∧ s.queue ≤ cap ∧ (s.blocked = true → s.queue = cap)

def abs (s : Joint) : Mon := ⟨s.queue, s.blocked⟩

theorem check_append (m : Mon) (a b : List PEv) :
    check m (a ++ b) = (check m a).bind (check · b) := by
  induction a generalizing m with
  | nil => simp [check]
  | cons e es ih =>
    simp only [List.cons_append, check]
    cases pstep m e <;> simp [ih]

theorem jstep_ok (cap : Nat) (hcap : 0 < cap) (s : Joint) (c : Sched) (hi : Inv cap s) :
    Inv cap (jstep cap s c).1 ∧ check (abs s) (jstep cap s c).2 = some (abs (jstep cap s c).1) := by
  obtain ⟨hbo, hq, hbq⟩ := hi
  obtain ⟨b, o, q⟩ := s
  simp only at hbo hq hbq
  subst hbo
  cases c <;> cases b <;> simp_all [jstep, Inv, check, abs] <;>
    first
    | omega
    | (split <;> simp_all [check, pstep] <;> omega)
    | (split <;> split <;> simp_all [check, pstep] <;> omega)
    | skip

/-- **定理**: 任意のスケジュールで、生成されたトレースはプロトコル合法で、不変条件が保たれる -/
theorem jrun_ok (cap : Nat) (hcap : 0 < cap) :
    ∀ (cs : List Sched) (s : Joint), Inv cap s →
      Inv cap (jrun cap s cs).1 ∧ check (abs s) (jrun cap s cs).2 = some (abs (jrun cap s cs).1)
  | [], s, h => ⟨h, rfl⟩
  | c :: cs, s, h => by
    have ⟨h1, h2⟩ := jstep_ok cap hcap s c h
    have ⟨h3, h4⟩ := jrun_ok cap hcap cs _ h1
    refine ⟨h3, ?_⟩
    simp only [jrun, check_append, h2, Option.bind_some, h4]

/-- 系: 初期状態からのどんな実行も合法で、requestor が retry 待ちなら必ず responder が retry 義務を
負っており、しかも `serve` が実行可能 (バッファが満杯) — すなわち lost-retry デッドロックは起きない -/
theorem no_lost_retry (cap : Nat) (hcap : 0 < cap) (cs : List Sched) :
    let s := (jrun cap Joint.init cs).1
    (check Mon.init (jrun cap Joint.init cs).2).isSome ∧
    (s.blocked = true → s.owes = true ∧ s.queue ≠ 0) := by
  have ⟨⟨hbo, _, hbq⟩, hc⟩ := jrun_ok cap hcap cs Joint.init ⟨rfl, Nat.zero_le _, by simp [Joint.init]⟩
  refine ⟨by simp only [abs] at hc; simp only [Mon.init, Joint.init] at hc ⊢; rw [hc]; rfl, fun hb => ⟨hbo ▸ hb, ?_⟩⟩
  have := hbq hb; omega

/-! ## 反例: retry 義務を記録しない buggy responder -/

def jstepBuggy (cap : Nat) (s : Joint) : Sched → Joint × List PEv
  | .issue =>
    if s.blocked then (s, [])
    else if s.queue < cap then ({ s with queue := s.queue + 1 }, [.sendReq true])
    else ({ s with blocked := true }, [.sendReq false])      -- owes を立て忘れる
  | .serve =>
    if s.queue = 0 then (s, [])
    else if s.owes then ({ blocked := false, owes := false, queue := s.queue - 1 }, [.resp, .retry])
    else ({ s with queue := s.queue - 1 }, [.resp])

def jrunBuggy (cap : Nat) : Joint → List Sched → Joint
  | s, [] => s
  | s, c :: cs => jrunBuggy cap (jstepBuggy cap s c).1 cs

/-- cap = 1 で issue, issue, serve とすると、requestor は blocked なのに誰も retry を送らない:
以後どのスケジュールでも blocked のまま (デッドロック) -/
theorem buggy_deadlock :
    let s := jrunBuggy 1 Joint.init [.issue, .issue, .serve]
    s.blocked = true ∧ s.owes = false ∧ s.queue = 0 := by decide

theorem buggy_stuck_forever (cs : List Sched) :
    (jrunBuggy 1 ⟨true, false, 0⟩ cs) = ⟨true, false, 0⟩ := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simpa [jrunBuggy, jstepBuggy] using ih

end Gem5.Port
