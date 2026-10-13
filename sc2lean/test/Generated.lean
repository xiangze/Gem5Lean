-- sc2lean で自動生成。手で編集する場合は生成元とルールも合わせて更新すること。

inductive Cmd | read | write | ignore
  deriving Repr, BEq, DecidableEq, Inhabited
inductive Status | ok | incomplete | genericError | addressError | commandError
  | burstError | byteEnableError
  deriving Repr, BEq, DecidableEq, Inhabited
/-- TLM generic payload のうちワード単位のデータ転送に必要な部分 -/
structure Payload where
  cmd    : Cmd    := .ignore
  addr   : UInt64 := 0
  data   : UInt32 := 0
  len    : UInt32 := 0
  status : Status := .incomplete
  deriving Repr, BEq, Inhabited

namespace Memory

structure St where
  reads : UInt32 := 0
  mem : Array UInt32 := Array.replicate 256 0
  deriving Repr

inductive Msg
  | stop
  | socket_req (p : Payload)
  | socket_resp (p : Payload) (d : Nat)
  deriving Repr

/-- Memory::b_transport（socket の b_transport） -/
def socket_b_transport (s : St) (trans : Payload) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  let mut trans := trans
  let mut delay : Nat := 0
  let mut addr : UInt64 := trans.addr
  if (decide (addr ≥ 1024)) || (trans.len != 4) then
    trans := { trans with status := .addressError }
    return (s, out ++ [(0, .socket_resp trans delay)])
  if trans.cmd == .read then
    trans := { trans with data := s.mem[(addr / 4).toNat]! }
    s := { s with reads := s.reads + 1 }
    delay := delay + ((20 * 1000))
  else
    s := { s with mem := s.mem.set! ((addr / 4).toNat) trans.data }
    delay := delay + ((30 * 1000))
  trans := { trans with status := .ok }
  return (s, out ++ [(0, .socket_resp trans delay)])

/-- コンストラクタ本体を実行した初期状態 -/
def init : St := Id.run do
  let mut s : St := {}
  s := { s with reads := 0 }
  let mut i : Int := 0
  while decide (i < 256) do
    s := { s with mem := s.mem.set! ((i).toNat) 0 }
    i := i + 1
  return s

/-- 時刻 0 に投入するメッセージ（プロセスの起動） -/
def initEvents : List (Nat × Msg) := []

/-- 1 メッセージを配送する。同じメッセージで起きるプロセスは宣言順に実行する。 -/
def step (s : St) (m : Msg) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  match m with
  | .socket_req p =>
    let r := socket_b_transport s p
    s := r.1
    out := out ++ r.2
  | _ => pure ()
  return (s, out)

end Memory

namespace Initiator

inductive RunPc | start | w0 | w1 | w2 | w3 | w4 | done
  deriving Repr, BEq, DecidableEq

structure St where
  sum : UInt32 := 0
  i : UInt32 := 0
  run_pc : RunPc := .start
  run_trans : Payload := {}
  run_delay : Nat := 0
  run_data : UInt32 := 0
  deriving Repr

inductive Msg
  | stop
  | ev_done
  | socket_req (p : Payload)
  | socket_resp (p : Payload) (d : Nat)
  | start_run
  | wake_run
  deriving Repr

/-- SC_THREAD run: 起動から次の待ちまで -/
def run_start (s : St) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with run_trans := {} }
  s := { s with run_delay := 0 }
  s := { s with run_data := 0 }
  s := { s with run_data := s.i * s.i }
  s := { s with run_trans := { s.run_trans with cmd := .write } }
  s := { s with run_trans := { s.run_trans with addr := ((s.i * 4).toUInt64) } }
  s := { s with run_trans := { s.run_trans with len := 4 } }
  s := { s with run_delay := 0 }
  s := { s with run_trans := { s.run_trans with data := s.run_data } }
  out := out ++ [(0, .socket_req s.run_trans)]
  s := { s with run_pc := .w0 }
  return (s, out)

/-- SC_THREAD run: w0 の再開から次の待ちまで -/
def run_w0 (s : St) (p : Payload) (d : Nat) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with run_trans := p }
  s := { s with run_delay := s.run_delay + d }
  s := { s with run_data := s.run_trans.data }
  out := out ++ [(s.run_delay, .wake_run)]
  s := { s with run_pc := .w1 }
  return (s, out)

/-- SC_THREAD run: w1 の再開から次の待ちまで -/
def run_w1 (s : St) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with run_trans := { s.run_trans with cmd := .read } }
  s := { s with run_delay := 0 }
  s := { s with run_trans := { s.run_trans with data := s.run_data } }
  out := out ++ [(0, .socket_req s.run_trans)]
  s := { s with run_pc := .w2 }
  return (s, out)

/-- SC_THREAD run: w2 の再開から次の待ちまで -/
def run_w2 (s : St) (p : Payload) (d : Nat) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with run_trans := p }
  s := { s with run_delay := s.run_delay + d }
  s := { s with run_data := s.run_trans.data }
  out := out ++ [(s.run_delay, .wake_run)]
  s := { s with run_pc := .w3 }
  return (s, out)

/-- SC_THREAD run: w3 の再開から次の待ちまで -/
def run_w3 (s : St) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with sum := s.sum + s.run_data }
  s := { s with i := ((s.i + 1)) &&& 3 }
  if s.i == 0 then
    out := out ++ [((1 * 1000), .ev_done)]
  out := out ++ [((10 * 1000), .wake_run)]
  s := { s with run_pc := .w4 }
  return (s, out)

/-- SC_THREAD run: w4 の再開から次の待ちまで -/
def run_w4 (s : St) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  s := { s with run_data := s.i * s.i }
  s := { s with run_trans := { s.run_trans with cmd := .write } }
  s := { s with run_trans := { s.run_trans with addr := ((s.i * 4).toUInt64) } }
  s := { s with run_trans := { s.run_trans with len := 4 } }
  s := { s with run_delay := 0 }
  s := { s with run_trans := { s.run_trans with data := s.run_data } }
  out := out ++ [(0, .socket_req s.run_trans)]
  s := { s with run_pc := .w0 }
  return (s, out)

/-- コンストラクタ本体を実行した初期状態 -/
def init : St := Id.run do
  let mut s : St := {}
  s := { s with sum := 0 }
  s := { s with i := 0 }
  return s

/-- 時刻 0 に投入するメッセージ（プロセスの起動） -/
def initEvents : List (Nat × Msg) := [(0, .start_run)]

/-- 1 メッセージを配送する。同じメッセージで起きるプロセスは宣言順に実行する。 -/
def step (s : St) (m : Msg) : St × List (Nat × Msg) := Id.run do
  let mut s := s
  let mut out : List (Nat × Msg) := []
  match m with
  | .start_run =>
    if s.run_pc == .start then
      let r := run_start s
      s := r.1
      out := out ++ r.2
  | .socket_resp p d =>
    if s.run_pc == .w0 then
      let r := run_w0 s p d
      s := r.1
      out := out ++ r.2
    else if s.run_pc == .w2 then
      let r := run_w2 s p d
      s := r.1
      out := out ++ r.2
  | .wake_run =>
    if s.run_pc == .w1 then
      let r := run_w1 s
      s := r.1
      out := out ++ r.2
    else if s.run_pc == .w3 then
      let r := run_w3 s
      s := r.1
      out := out ++ r.2
    else if s.run_pc == .w4 then
      let r := run_w4 s
      s := r.1
      out := out ++ r.2
  | _ => pure ()
  return (s, out)

end Initiator
