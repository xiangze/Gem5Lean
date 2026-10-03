/-!
# Gem5Lean.NoC — W×H メッシュ NoC, XY 次元順ルーティング, デッドロック自由性

gem5 Garnet のメッシュ + `XY` routing algorithm に相当するモデル。

* チャネル `Chan` = (送信元ノード, 方向) の物理リンク。各チャネルの受信側に 1 フリット分のバッファ
* `Flit` = (今いるチャネル, 宛先)。フリットはチャネル `ch` の受信バッファ (= ノード `ch.dst`) に居る
* `Move` = 1 フリットの前進 (次チャネルのバッファが空いているとき) / 排出 (宛先到着) / 注入

証明する性質:

1. `dep_rank`      : チャネル依存グラフ (CDG) の辺に沿ってランクが狭義増加
2. `cdg_acyclic`   : CDG は非巡回 (Dally–Seitz の条件)
3. `move_valid`    : 合法状態は Move で保存 (バッファ排他性 = チャネル重複なし を含む)
4. `progress`      : 空でない合法状態では必ず何かが動ける (**デッドロック自由**)
5. `drain`         : 注入を止めれば、どんなスケジュールでも有限ステップで空になる (**ライブロック自由**)
6. `route_minimal` : XY ルーティングは最短経路 (各ホップでマンハッタン距離が 1 減る)
7. 反例: 全方向最小適応ルーティングでは 2×2 で 4 フリットの循環待ち (デッドロック) が作れる
-/

namespace Gem5.NoC

inductive Dir | E | W | N | S
  deriving DecidableEq, Repr

structure Node where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def Node.move : Node → Dir → Node
  | ⟨x, y⟩, .E => ⟨x + 1, y⟩
  | ⟨x, y⟩, .W => ⟨x - 1, y⟩
  | ⟨x, y⟩, .N => ⟨x, y + 1⟩
  | ⟨x, y⟩, .S => ⟨x, y - 1⟩

/-- XY 次元順ルーティング: まず X を合わせ、次に Y -/
def route (cur dst : Node) : Option Dir :=
  if cur.x < dst.x then some .E
  else if dst.x < cur.x then some .W
  else if cur.y < dst.y then some .N
  else if dst.y < cur.y then some .S
  else none

structure Chan where
  src : Node
  dir : Dir
  deriving DecidableEq, Repr

def Chan.dst (c : Chan) : Node := c.src.move c.dir

structure Flit where
  ch   : Chan
  dest : Node
  deriving DecidableEq, Repr

/-- フリットが次に要求するチャネル (`none` = 到着済みで排出可能) -/
def Flit.next (f : Flit) : Option Chan := (route f.ch.dst f.dest).map (Chan.mk f.ch.dst)

/-! ## ルーティングの特徴付け -/

theorem route_E {c d : Node} : route c d = some .E ↔ c.x < d.x := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega
theorem route_W {c d : Node} : route c d = some .W ↔ d.x < c.x := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega
theorem route_N {c d : Node} : route c d = some .N ↔ c.x = d.x ∧ c.y < d.y := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega
theorem route_S {c d : Node} : route c d = some .S ↔ c.x = d.x ∧ d.y < c.y := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega
theorem route_none {c d : Node} : route c d = none ↔ c.x = d.x ∧ c.y = d.y := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega

theorem route_cases (c d : Node) :
    (route c d = some .E ∧ c.x < d.x) ∨ (route c d = some .W ∧ d.x < c.x) ∨
    (route c d = some .N ∧ c.x = d.x ∧ c.y < d.y) ∨ (route c d = some .S ∧ c.x = d.x ∧ d.y < c.y) ∨
    (route c d = none ∧ c.x = d.x ∧ c.y = d.y) := by
  unfold route
  by_cases h1 : c.x < d.x <;> by_cases h2 : d.x < c.x <;> by_cases h3 : c.y < d.y <;>
    by_cases h4 : d.y < c.y <;> simp [h1, h2, h3, h4] <;> omega

/-! ## 合法性とランク -/

/-- フリットが合法: メッシュ内にあり、今いるチャネルは XY ルーティングが選んだもの -/
def Legal (W H : Nat) (f : Flit) : Prop :=
  f.ch.src.x < W ∧ f.ch.src.y < H ∧ f.dest.x < W ∧ f.dest.y < H ∧ route f.ch.src f.dest = some f.ch.dir

instance (W H : Nat) (f : Flit) : Decidable (Legal W H f) := by unfold Legal; infer_instance

/-- チャネルのランク: X チャネル (E は x 昇順, W は x 降順) < Y チャネル (N は y 昇順, S は y 降順) -/
def rank (W H : Nat) (c : Chan) : Nat :=
  match c.dir with
  | .E => c.src.x
  | .W => W - c.src.x
  | .N => W + 1 + c.src.y
  | .S => W + 1 + H - c.src.y

def bound (W H : Nat) : Nat := W + H + 2

theorem rank_lt_bound {W H : Nat} {f : Flit} (h : Legal W H f) : rank W H f.ch < bound W H := by
  obtain ⟨⟨⟨x, y⟩, d⟩, ⟨dx, dy⟩⟩ := f
  obtain ⟨hx, hy, -, -, -⟩ := h
  dsimp only at hx hy
  cases d <;> simp only [rank, bound] at * <;> omega

/-- **補題 1**: 合法なフリットの次チャネルはランクが真に大きく、そこへ移ったフリットも合法 -/
theorem next_rank {W H : Nat} {f : Flit} {c' : Chan} (h : Legal W H f) (hn : f.next = some c') :
    rank W H f.ch < rank W H c' ∧ Legal W H ⟨c', f.dest⟩ := by
  obtain ⟨⟨⟨x, y⟩, d⟩, ⟨dx, dy⟩⟩ := f
  obtain ⟨hx, hy, hdx, hdy, hr⟩ := h
  dsimp only at hx hy hdx hdy hr
  simp only [Flit.next, Chan.dst, Option.map_eq_some_iff] at hn
  obtain ⟨d', hr', rfl⟩ := hn
  refine ⟨?_, ?_⟩ <;>
  cases d <;> cases d' <;>
    simp only [route_E, route_W, route_N, route_S, Node.move, rank, Legal] at hr hr' ⊢ <;> omega

/-! ## CDG の非巡回性 -/

/-- チャネル依存: ある合法フリットが c₁ を保持したまま c₂ を要求しうる -/
def Dep (W H : Nat) (c₁ c₂ : Chan) : Prop :=
  ∃ dest, Legal W H ⟨c₁, dest⟩ ∧ Flit.next ⟨c₁, dest⟩ = some c₂

theorem dep_rank {W H : Nat} {c₁ c₂ : Chan} (h : Dep W H c₁ c₂) : rank W H c₁ < rank W H c₂ := by
  obtain ⟨dest, hl, hn⟩ := h
  exact (next_rank hl hn).1

theorem transgen_rank {W H : Nat} {a b : Chan} (h : Relation.TransGen (Dep W H) a b) :
    rank W H a < rank W H b := by
  induction h with
  | single h => exact dep_rank h
  | tail _ h ih => exact Nat.lt_trans ih (dep_rank h)

/-- **定理 (Dally–Seitz)**: XY ルーティングのチャネル依存グラフは非巡回 -/
theorem cdg_acyclic (W H : Nat) (c : Chan) : ¬ Relation.TransGen (Dep W H) c c :=
  fun h => Nat.lt_irrefl _ (transgen_rank h)

/-! ## 操作的モデル -/

/-- 合法な網状態: 全フリット合法 + 1 チャネル (バッファ) に高々 1 フリット -/
def Valid (W H : Nat) (s : List Flit) : Prop :=
  (∀ f ∈ s, Legal W H f) ∧ (s.map Flit.ch).Nodup

/-- 網内の 1 ステップ (注入以外) -/
inductive Move : List Flit → List Flit → Prop
  | eject {l₁ l₂ : List Flit} {f : Flit} :
      f.next = none → Move (l₁ ++ f :: l₂) (l₁ ++ l₂)
  | fwd {l₁ l₂ : List Flit} {f : Flit} {c' : Chan} :
      f.next = some c' → (∀ g ∈ l₁ ++ f :: l₂, g.ch ≠ c') →
      Move (l₁ ++ f :: l₂) (l₁ ++ ⟨c', f.dest⟩ :: l₂)

/-- 注入: ノード n の NI から最初のリンクへ -/
inductive Inject (W H : Nat) : List Flit → List Flit → Prop
  | inj {s : List Flit} {n dest : Node} {d : Dir} :
      n.x < W → n.y < H → dest.x < W → dest.y < H → route n dest = some d →
      (∀ g ∈ s, g.ch ≠ ⟨n, d⟩) → Inject W H s (⟨⟨n, d⟩, dest⟩ :: s)

theorem nodup_replace {l₁ l₂ : List Chan} {a b : Chan}
    (h : (l₁ ++ a :: l₂).Nodup) (hb : b ∉ l₁ ++ a :: l₂) : (l₁ ++ b :: l₂).Nodup := by
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or] at *
  obtain ⟨h1, ⟨-, h2⟩, h3⟩ := h
  refine ⟨h1, ⟨hb.2.2, h2⟩, ?_⟩
  intro x hx y hy
  rcases hy with rfl | hy
  · intro hxy; subst hxy; exact hb.1 hx
  · exact h3 x hx y (Or.inr hy)

/-- **補題 2**: 合法性 (バッファ排他性を含む) は Move と Inject で保存される -/
theorem move_valid {W H : Nat} {s s' : List Flit} (hv : Valid W H s) (hm : Move s s') : Valid W H s' := by
  obtain ⟨hl, hnd⟩ := hv
  cases hm with
  | eject _ =>
    refine ⟨fun g hg => hl g (List.mem_append.mpr ((List.mem_append.mp hg).imp id (List.mem_cons_of_mem _))), ?_⟩
    simp only [List.map_append, List.map_cons] at hnd ⊢
    exact List.Nodup.sublist ((List.sublist_cons_self _ _).append_left _) hnd
  | @fwd l₁ l₂ f c' hn hfree =>
    have hf := hl f (by simp)
    have ⟨_, hl'⟩ := next_rank hf hn
    refine ⟨?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons] at hg
      rcases hg with hg | rfl | hg
      · exact hl g (by simp [hg])
      · exact hl'
      · exact hl g (by simp [hg])
    · simp only [List.map_append, List.map_cons] at hnd ⊢
      apply nodup_replace hnd
      intro hc
      simp only [List.mem_append, List.mem_map, List.mem_cons] at hc
      rcases hc with ⟨g, hg, hgc⟩ | hc | ⟨g, hg, hgc⟩
      · exact hfree g (by simp [hg]) hgc
      · exact hfree f (by simp) hc.symm
      · exact hfree g (by simp [hg]) hgc

theorem inject_valid {W H : Nat} {s s' : List Flit} (hv : Valid W H s) (hm : Inject W H s s') :
    Valid W H s' := by
  obtain ⟨hl, hnd⟩ := hv
  cases hm with
  | inj hnx hny hdx hdy hr hfree =>
    refine ⟨?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨hnx, hny, hdx, hdy, hr⟩
      · exact hl g hg
    · simp only [List.map_cons, List.nodup_cons, List.mem_map]
      exact ⟨fun ⟨g, hg, hgc⟩ => hfree g hg hgc, hnd⟩

/-! ## デッドロック自由性 -/

theorem progress_aux {W H : Nat} {s : List Flit} (hv : Valid W H s) :
    ∀ n, ∀ f ∈ s, bound W H - rank W H f.ch ≤ n → ∃ s', Move s s' := by
  intro n
  induction n with
  | zero =>
    intro f hf hk
    have := rank_lt_bound (hv.1 f hf); omega
  | succ n ih =>
    intro f hf hk
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hf
    cases hn : f.next with
    | none => exact ⟨_, Move.eject hn⟩
    | some c' =>
      by_cases hfree : ∀ g ∈ l₁ ++ f :: l₂, g.ch ≠ c'
      · exact ⟨_, Move.fwd hn hfree⟩
      · -- c' を占有しているフリット g は、よりランクの高いチャネルに居る
        have : ∃ g ∈ l₁ ++ f :: l₂, g.ch = c' :=
          Classical.byContradiction fun hne => hfree fun g hg hgc => hne ⟨g, hg, hgc⟩
        obtain ⟨g, hg, hgc⟩ := this
        have hr := (next_rank (hv.1 f hf) hn).1
        have hb := rank_lt_bound (hv.1 g hg)
        exact ih g hg (by rw [hgc] at hb ⊢; omega)

/-- **定理 (デッドロック自由)**: 合法で空でない網状態では、必ずどれかのフリットが前進または排出できる -/
theorem progress {W H : Nat} {s : List Flit} (hv : Valid W H s) (hne : s ≠ []) : ∃ s', Move s s' := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil s hne
  exact progress_aux hv _ f hf (Nat.le_refl _)

/-! ## ライブロック自由 / 排出 -/

def dist (a b : Node) : Nat := (a.x - b.x) + (b.x - a.x) + (a.y - b.y) + (b.y - a.y)

/-- **定理 (最短性)**: XY ルーティングの 1 ホップでマンハッタン距離はちょうど 1 減る -/
theorem route_minimal (c d : Node) (dir : Dir) (h : route c d = some dir) :
    dist (c.move dir) d + 1 = dist c d := by
  obtain ⟨x, y⟩ := c
  cases dir <;>
    simp only [route_E, route_W, route_N, route_S] at h <;> simp only [Node.move, dist] <;> omega

def measure : List Flit → Nat
  | [] => 0
  | f :: s => dist f.ch.dst f.dest + 1 + measure s

theorem measure_append (a b : List Flit) : measure (a ++ b) = measure a + measure b := by
  induction a with
  | nil => simp [measure]
  | cons f a ih => simp only [List.cons_append, measure, ih]; omega

theorem move_measure {s s' : List Flit} (hm : Move s s') : measure s' < measure s := by
  cases hm with
  | eject _ => simp only [measure_append, measure]; omega
  | @fwd l₁ l₂ f c' hn _ =>
    simp only [Flit.next, Option.map_eq_some_iff] at hn
    obtain ⟨d, hr, rfl⟩ := hn
    have := route_minimal _ _ _ hr
    simp only [measure_append, measure, Chan.dst] at this ⊢
    omega

/-- 反射推移閉包 -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl {a} : Star R a a
  | head {a b c} : R a b → Star R b c → Star R a c

theorem drain_aux {W H : Nat} : ∀ (n : Nat) (s : List Flit), measure s ≤ n → Valid W H s → Star Move s []
  | 0, s, h, _ => by
    cases s with
    | nil => exact .refl
    | cons f s => simp [measure] at h
  | n + 1, s, h, hv => by
    by_cases hne : s = []
    · subst hne; exact .refl
    · obtain ⟨s', hm⟩ := progress hv hne
      exact .head hm (drain_aux n s' (by have := move_measure hm; omega) (move_valid hv hm))

/-- **定理 (排出)**: 注入を止めると、合法状態から空の網へ到達できる -/
theorem drain {W H : Nat} (s : List Flit) (hv : Valid W H s) : Star Move s [] :=
  drain_aux _ s (Nat.le_refl _) hv

/-- 有限の実行列 `s → t₁ → t₂ → …` -/
def Trace : List Flit → List (List Flit) → Prop
  | _, [] => True
  | s, t :: tr => Move s t ∧ Trace t tr

/-- **定理 (ライブロック自由)**: 注入なしのどんな Move 列も、長さは初期 `measure` 以下 -/
theorem moves_bounded : ∀ (s : List Flit) (tr : List (List Flit)), Trace s tr → tr.length ≤ measure s
  | _, [], _ => Nat.zero_le _
  | s, t :: tr, ⟨hm, ht⟩ => by
    have := moves_bounded t tr ht
    have := move_measure hm
    simp only [List.length_cons]; omega

/-- **定理**: 合法状態から到達した、もう動けない状態は空である (= デッドロック状態は到達不能) -/
theorem stuck_is_empty {W H : Nat} {s t : List Flit} (hv : Valid W H s) (hst : Star Move s t)
    (hstuck : ∀ u, ¬ Move t u) : t = [] := by
  have hvt : Valid W H t := by
    clear hstuck
    induction hst with
    | refl => exact hv
    | head hm _ ih => exact ih (move_valid hv hm)
  by_cases hne : t = []
  · exact hne
  · obtain ⟨u, hu⟩ := progress hvt hne; exact absurd hu (hstuck u)

/-! ## 実行可能なスケジューラ -/

def canFree (s : List Flit) (c : Chan) : Bool := s.all fun g => g.ch != c

/-- 先頭から見て最初に動けるフリットを動かす (gem5 の round-robin arbiter の簡易版) -/
def stepNet (s : List Flit) : Option (List Flit) :=
  go [] s
where
  go (pre : List Flit) : List Flit → Option (List Flit)
    | [] => none
    | f :: rest =>
      match f.next with
      | none => some (pre.reverse ++ rest)
      | some c' => if canFree s c' then some (pre.reverse ++ ⟨c', f.dest⟩ :: rest) else go (f :: pre) rest

def drainSim : Nat → List Flit → Nat × List Flit
  | 0, s => (0, s)
  | k + 1, s => match stepNet s with
    | none => (0, s)
    | some s' => let r := drainSim k s'; (r.1 + 1, r.2)

theorem canFree_spec {s : List Flit} {c : Chan} (h : canFree s c = true) : ∀ g ∈ s, g.ch ≠ c := by
  intro g hg hgc
  have := List.all_eq_true.mp h g hg
  simp [hgc] at this

theorem go_sound (s : List Flit) : ∀ (rest pre : List Flit) (s' : List Flit),
    s = pre.reverse ++ rest → stepNet.go s pre rest = some s' → Move s s'
  | [], _, _, _, h => by simp [stepNet.go] at h
  | f :: rest, pre, s', hs, h => by
    unfold stepNet.go at h
    split at h
    · rename_i hn
      cases h; rw [hs]; exact Move.eject hn
    · rename_i c' hn
      split at h
      · rename_i hfree
        cases h; rw [hs]; exact Move.fwd hn (hs ▸ canFree_spec hfree)
      · exact go_sound s rest (f :: pre) s' (by simp [hs]) h

/-- 実行可能スケジューラの健全性: `stepNet` の 1 ステップは仕様 `Move` の 1 ステップ -/
theorem stepNet_sound {s s' : List Flit} (h : stepNet s = some s') : Move s s' :=
  go_sound s s [] s' (by simp) h

theorem go_none (s : List Flit) : ∀ (rest pre : List Flit), stepNet.go s pre rest = none →
    ∀ f ∈ rest, ∃ c', f.next = some c' ∧ canFree s c' = false
  | [], _, _ => by simp
  | f :: rest, pre, h => by
    unfold stepNet.go at h
    split at h
    · cases h
    · rename_i c' hn
      split at h
      · cases h
      · rename_i hfree
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨c', hn, by simpa using hfree⟩
        · exact go_none s rest (f :: pre) h g hg

/-- 実行可能スケジューラの完全性: 合法状態で `stepNet` が止まるのは網が空のときだけ -/
theorem stepNet_none {W H : Nat} {s : List Flit} (hv : Valid W H s) (h : stepNet s = none) : s = [] := by
  by_cases hne : s = []
  · exact hne
  · exfalso
    have hall := go_none s s [] h
    obtain ⟨s', hm⟩ := progress hv hne
    cases hm with
    | @eject l₁ l₂ f hn =>
      obtain ⟨c', hc, -⟩ := hall f (by simp); simp [hn] at hc
    | @fwd l₁ l₂ f c' hn hfree =>
      obtain ⟨c'', hc, hcf⟩ := hall f (by simp)
      rw [hn] at hc; cases hc
      have : canFree (l₁ ++ f :: l₂) c' = true :=
        List.all_eq_true.mpr fun g hg => by simpa using hfree g hg
      simp [this] at hcf

/-! ## 実行例: 4×4 メッシュで転置トラフィック + 対角トラフィック -/

/-- ノード n から dest への注入を試みる (最初のリンクが空いていれば) -/
def tryInject (s : List Flit) (n dest : Node) : List Flit :=
  match route n dest with
  | none => s
  | some d => if canFree s ⟨n, d⟩ then ⟨⟨n, d⟩, dest⟩ :: s else s

def validB (W H : Nat) (s : List Flit) : Bool :=
  s.all (fun f => decide (Legal W H f)) && decide ((s.map Flit.ch).Nodup)

def traffic : List Flit := Id.run do
  let mut s : List Flit := []
  for x in List.range 4 do
    for y in List.range 4 do
      s := tryInject s ⟨x, y⟩ ⟨y, x⟩            -- transpose
      s := tryInject s ⟨x, y⟩ ⟨3 - x, 3 - y⟩    -- bit-complement
  return s

#eval traffic.length
#eval (measure traffic, drainSim 1000 traffic)
#guard validB 4 4 traffic
#guard (drainSim 1000 traffic).2 == []
#guard (drainSim 1000 traffic).1 ≤ measure traffic

/-! ## 反例: 最小適応ルーティング (ターン制限なし) -/

/-- 宛先へ近づく方向ならどれでも可 -/
def productive (c d : Node) : List Dir :=
  (if c.x < d.x then [.E] else []) ++ (if d.x < c.x then [.W] else []) ++
  (if c.y < d.y then [.N] else []) ++ (if d.y < c.y then [.S] else [])

def LegalAdaptive (W H : Nat) (f : Flit) : Bool :=
  decide (f.ch.src.x < W ∧ f.ch.src.y < H ∧ f.dest.x < W ∧ f.dest.y < H) &&
  (productive f.ch.src f.dest).contains f.ch.dir

/-- どのフリットも、行き先候補チャネルがすべて他のフリットに占有されていて動けない -/
def StuckAdaptive (s : List Flit) : Bool :=
  s.all fun f => f.ch.dst != f.dest &&
    (productive f.ch.dst f.dest).all fun d => s.any fun g => g.ch == ⟨f.ch.dst, d⟩

/-- 2×2 メッシュでの循環待ち: E(0,0)→N(1,0)→W(1,1)→S(0,1)→E(0,0) -/
def cycle4 : List Flit :=
  [ ⟨⟨⟨0, 0⟩, .E⟩, ⟨1, 1⟩⟩,
    ⟨⟨⟨1, 0⟩, .N⟩, ⟨0, 1⟩⟩,
    ⟨⟨⟨1, 1⟩, .W⟩, ⟨0, 0⟩⟩,
    ⟨⟨⟨0, 1⟩, .S⟩, ⟨1, 0⟩⟩ ]

/-- 適応ルーティングでは合法だがデッドロックしている -/
theorem adaptive_deadlock :
    cycle4.all (LegalAdaptive 2 2) = true ∧ cycle4 ≠ [] ∧ StuckAdaptive cycle4 = true := by decide

/-- 同じ状態は XY ルーティングでは到達不能 (Valid でない) — N(1,0) のフリットは宛先 x=0 なので
XY では先に W に行くはず -/
theorem cycle4_not_xy : ¬ (∀ f ∈ cycle4, Legal 2 2 f) := by decide

end Gem5.NoC
