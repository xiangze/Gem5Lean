import Generated

/-! 生成された Initiator と Memory を配線し、簡単なイベントキューで走らせる。
    SystemC の LT 実行での期待値:
      1 反復 = 書き込み 30ns + 読み出し 20ns + wait 10ns = 60ns、sum の更新は 60k+50 ns。
      1000ns までに sum は 16 回更新 → 4 周 × (0+1+4+9) = 56。mem[0..3] = [0,1,4,9]。
      読み出しは 60k+30 ns に起きるので 1000ns までに 17 回。 -/

inductive Ev | ini (m : Initiator.Msg) | mem (m : Memory.Msg)

structure Sys where
  now : Nat := 0
  q   : List (Nat × Ev) := []      -- 時刻順（同時刻は投入順）
  ini : Initiator.St
  mem : Memory.St

def Sys.push (s : Sys) (t : Nat) (e : Ev) : Sys :=
  let (a, b) := s.q.span (fun p => p.1 ≤ t)
  { s with q := a ++ [(t, e)] ++ b }

/-- 配線: Initiator.socket ⇄ Memory.socket -/
def routeIni (now : Nat) : Nat × Initiator.Msg → Nat × Ev
  | (d, .socket_req p) => (now + d, .mem (.socket_req p))
  | (d, m)             => (now + d, .ini m)
def routeMem (now : Nat) : Nat × Memory.Msg → Nat × Ev
  | (d, .socket_resp p dl) => (now + d, .ini (.socket_resp p dl))
  | (d, m)                 => (now + d, .mem m)

def Sys.step (s : Sys) : Option Sys :=
  match s.q with
  | [] => none
  | (t, e) :: rest =>
    let s := { s with now := t, q := rest }
    match e with
    | .ini m =>
      let (st, out) := Initiator.step s.ini m
      some <| (out.map (routeIni t)).foldl (fun s (t, e) => s.push t e) { s with ini := st }
    | .mem m =>
      let (st, out) := Memory.step s.mem m
      some <| (out.map (routeMem t)).foldl (fun s (t, e) => s.push t e) { s with mem := st }

def Sys.runUntil (s : Sys) (tEnd : Nat) : Nat → Sys
  | 0 => s
  | fuel + 1 =>
    match s.q with
    | (t, _) :: _ => if t ≤ tEnd then match s.step with
        | some s' => s'.runUntil tEnd fuel
        | none => s
      else s
    | [] => s

def sys0 : Sys :=
  let s : Sys := { ini := Initiator.init, mem := Memory.init }
  let s := Initiator.initEvents.foldl (fun s (d, m) => s.push d (.ini m)) s
  Memory.initEvents.foldl (fun s (d, m) => s.push d (.mem m)) s

def after := sys0.runUntil 1000000 10000

#eval (after.ini.sum, after.mem.reads, after.mem.mem.toList.take 4)
#guard after.ini.sum == 56
#guard after.mem.reads == 17
#guard after.mem.mem.toList.take 4 == [0, 1, 4, 9]
