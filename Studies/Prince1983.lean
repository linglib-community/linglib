module

public import Linglib.Core.Computability.Edge
public import Linglib.Phonology.Prosody.Grid
public import Mathlib.Data.List.GetD

/-!
# Prince (1983): Relating to the Grid

Prince argues that the metrical grid alone, without the labelled tree, carries the theory of
stress. For a uniformly labelled tree, Liberman and Prince's Relative Prominence Projection Rule
says what the End Rule says, so the labelling does no work. Two grid entries clash when they are
adjacent at a level with no entry one level down between them, and the Rhythm Rule is Move x,
which slides a clashing entry within its level and can never move the peak of a phrase. Word
stress is built from the End Rule at an edge, extrametricality, Perfect Grid Construction sweeping
from an edge, and bipositional heavy syllables; together they derive the alternating systems of
Garawa, Hawaiian and Winnebago and the quantity-sensitive systems of (98).

## Implementation notes

* A grid is the substrate's `Prosody.Grid`, a list of column heights, so the Continuous Column
  Constraint holds by construction.
* The End Rule applies to the highest level present below the level it maps into, the reading of
  §3.7; without Forward Clash Override it withholds a promotion that would clash.
* Perfect Grid Construction is a greedy sweep that raises a column when neither neighbour is
  stressed, a trough start behaving as if a stress preceded the edge.
* The edges and directions of (119) are both `Edge`, a direction being named by the edge it
  starts from; the End Rule, Perfect Grid Construction and Move x run right to left as the
  `List.revConj` mirror images of their left-to-right versions. A syllable of two or more moras
  is bipositional.

## TODO

The End Rule (Final) inside the stress level that makes Garawa's penultimate stress secondary
rather than tertiary, Mora Sluicing, the Forward Clash Override option of Perfect Grid
Construction, the bounding of Move x in §2.2, the extrametrical systems of (99), the feet of §4,
and the pitch-accent systems of §5 are not formalized.

## References

* [prince-1983]
* [liberman-prince-1977]
-/

@[expose] public section

namespace Prince1983

open Prosody Prosody.Grid

/-! ### Trees, the Relative Prominence Projection Rule, and the End Rule (§1.3, §2.1) -/

/-- `place e a b` sets `a` beside `b`, with `a` at edge `e`. -/
def place : Edge → List ℕ → List ℕ → List ℕ
  | .left, a, b => a ++ b
  | .right, a, b => b ++ a

@[simp] theorem mem_place {e : Edge} {a b : List ℕ} {x : ℕ} :
    x ∈ place e a b ↔ x ∈ a ∨ x ∈ b := by
  cases e <;> simp [place, or_comm]

theorem perm_place (e : Edge) (a b : List ℕ) : (place e a b).Perm (a ++ b) := by
  cases e
  · exact .refl _
  · exact List.perm_append_comm

/-- An s/w-labelled binary metrical tree whose terminals carry their grid column heights. A node
holds its strong daughter `s`, its weak daughter `w`, and the edge `e` at which `s` stands, so
the labelling is independent of linear order. -/
inductive SWTree
  | leaf (h : ℕ)
  | node (s w : SWTree) (e : Edge)
  deriving DecidableEq, Repr

namespace SWTree

/-- The grid over a tree lists the column heights of its terminals, left to right. -/
def heights : SWTree → Grid
  | leaf h => [h]
  | node s w e => place e (heights s) (heights w)

/-- `H(N)` is the height of the head terminal, reached from the root through strong daughters. -/
def headHeight : SWTree → ℕ
  | leaf h => h
  | node s _ _ => headHeight s

/-- `weakHeights t` lists the heights of the terminals other than the head. -/
def weakHeights : SWTree → List ℕ
  | leaf _ => []
  | node s w e => place e (weakHeights s) (heights w)

theorem mem_heights {t : SWTree} {h : ℕ} :
    h ∈ heights t ↔ h = headHeight t ∨ h ∈ weakHeights t := by
  induction t with
  | leaf x => simp [heights, headHeight, weakHeights]
  | node s w e ihs _ => simp [heights, headHeight, weakHeights, ihs, or_assoc]

theorem headHeight_mem (t : SWTree) : headHeight t ∈ heights t := mem_heights.2 (.inl rfl)

theorem heights_perm (t : SWTree) : (heights t).Perm (headHeight t :: weakHeights t) := by
  induction t with
  | leaf _ => exact .refl _
  | node s w e ihs _ =>
    exact (perm_place e _ _).trans ((ihs.append_right _).trans (.cons _ (perm_place e _ _).symm))

/-- `Everywhere P t` says that `P` holds of every constituent of `t`. -/
def Everywhere (P : SWTree → Prop) : SWTree → Prop
  | leaf h => P (leaf h)
  | node s w e => Everywhere P s ∧ Everywhere P w ∧ P (node s w e)

theorem Everywhere.self {P : SWTree → Prop} {t : SWTree} (h : Everywhere P t) : P t := by
  cases t with
  | leaf _ => exact h
  | node _ _ _ => exact h.2.2

/-- The Relative Prominence Projection Rule (7) requires `H(s) > H(w)` of every pair of sisters. -/
def Rppr : SWTree → Prop
  | leaf _ => True
  | node s w _ => Rppr s ∧ Rppr w ∧ headHeight w < headHeight s

/-- The head of a constituent is stronger than each of its other terminals. -/
def HeadStrong (t : SWTree) : Prop := ∀ h ∈ weakHeights t, h < headHeight t

theorem HeadStrong.le {t : SWTree} (ht : HeadStrong t) {h : ℕ} (hh : h ∈ heights t) :
    h ≤ headHeight t := by
  rcases mem_heights.1 hh with rfl | hw
  · exact le_rfl
  · exact (ht h hw).le

theorem headStrong_node_iff {s w : SWTree} {e : Edge} (hs : HeadStrong s) (hw : HeadStrong w) :
    HeadStrong (node s w e) ↔ headHeight w < headHeight s := by
  simp only [HeadStrong, weakHeights, headHeight, mem_place]
  exact ⟨fun h ↦ h _ (.inr (headHeight_mem w)),
    fun hlt h ↦ (·.elim (hs h) fun hh ↦ (hw.le hh).trans_lt hlt)⟩

theorem rppr_iff (t : SWTree) : Rppr t ↔ Everywhere HeadStrong t := by
  induction t with
  | leaf _ => simp [Rppr, Everywhere, HeadStrong, weakHeights]
  | node s w e ihs ihw =>
    rw [Rppr, Everywhere, ihs, ihw]
    exact and_congr_right fun hs ↦ and_congr_right fun hw ↦
      (headStrong_node_iff hs.self hw.self).symm

theorem isCulminative_of_rppr {t : SWTree} (h : Rppr t) : IsCulminative (heights t) := by
  have hs := ((rppr_iff t).1 h).self
  have hpeak : peak (heights t) = headHeight t :=
    le_antisymm (peak_le fun x hx ↦ hs.le hx) (le_peak (headHeight_mem t))
  rw [IsCulminative, hpeak, (heights_perm t).countP_eq, List.countP_cons_of_pos (by simp),
    List.countP_eq_zero.2 fun x hx ↦ by simpa using (hs x hx).ne]

/-- `edgeHeight e t` is the height of the terminal at edge `e`. -/
def edgeHeight (e : Edge) : SWTree → ℕ
  | leaf h => h
  | node s w e' => if e' = e then edgeHeight e s else edgeHeight e w

/-- `otherHeights e t` lists the heights of the terminals other than the one at edge `e`. -/
def otherHeights (e : Edge) : SWTree → List ℕ
  | leaf _ => []
  | node s w e' =>
    if e' = e then place e' (otherHeights e s) (heights w)
    else place e' (heights s) (otherHeights e w)

/-- The End Rule (13) at edge `e` makes the terminal there stronger than every other terminal. -/
def EdgeStrong (e : Edge) (t : SWTree) : Prop := ∀ h ∈ otherHeights e t, h < edgeHeight e t

/-- A tree is uniformly labelled at edge `e` when every constituent is strong there. -/
def Uniform (e : Edge) : SWTree → Prop
  | leaf _ => True
  | node s w e' => e' = e ∧ Uniform e s ∧ Uniform e w

theorem Uniform.headHeight_eq {e : Edge} {t : SWTree} (h : Uniform e t) :
    headHeight t = edgeHeight e t := by
  induction t with
  | leaf _ => rfl
  | node s w e' ihs _ => simp [headHeight, edgeHeight, h.1, ihs h.2.1]

theorem Uniform.weakHeights_eq {e : Edge} {t : SWTree} (h : Uniform e t) :
    weakHeights t = otherHeights e t := by
  induction t with
  | leaf _ => rfl
  | node s w e' ihs _ => simp [weakHeights, otherHeights, h.1, ihs h.2.1]

/-- Under uniform labelling at either edge the RPPR says exactly what the End Rule says, so the
labelling of nonterminals does no work. -/
theorem uniform_rppr_iff {e : Edge} {t : SWTree} (h : Uniform e t) :
    Rppr t ↔ Everywhere (EdgeStrong e) t := by
  rw [rppr_iff]
  induction t with
  | leaf _ => simp [Everywhere, HeadStrong, EdgeStrong, weakHeights, otherHeights]
  | node s w e' ihs ihw =>
    simp only [Everywhere, ihs h.2.1, ihw h.2.2, HeadStrong, EdgeStrong, h.headHeight_eq,
      h.weakHeights_eq]

end SWTree

/-! ### Clash and Move x (§2.2) -/

/-- Columns `i < j` clash at level `n` (27) when both reach level `n` and no column between them
reaches level `n - 1`. -/
def Clash (g : Grid) (n i j : ℕ) : Prop :=
  i < j ∧ n ≤ g.getD i 0 ∧ n ≤ g.getD j 0 ∧ ∀ k < j, i < k → g.getD k 0 + 1 < n

instance (g : Grid) (n i j : ℕ) : Decidable (Clash g n i j) := by unfold Clash; infer_instance

/-- A grid is eurhythmic when no two columns clash at any level from `2` up to the peak. -/
def NoClash (g : Grid) : Prop :=
  ∀ n ≤ peak g, 2 ≤ n → ∀ i < g.length, ∀ j < g.length, ¬ Clash g n i j

instance (g : Grid) : Decidable (NoClash g) := by unfold NoClash; infer_instance

theorem noClash_of_alternating {g : Grid} (h : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2)
    (hadj : g.IsChain fun a b ↦ a < 2 ∨ b < 2) : NoClash g := by
  rintro n hn h2 i hi j hj ⟨hij, hni, hnj, hk⟩
  have hp : peak g ≤ 2 := peak_le fun x hx ↦ (h x hx).2
  obtain rfl : n = 2 := by omega
  rw [List.getD_eq_getElem _ _ hi] at hni
  rw [List.getD_eq_getElem _ _ hj] at hnj
  rcases Nat.lt_or_ge (i + 1) j with hlt | hge
  · have h1 := hk (i + 1) hlt (Nat.lt_succ_self i)
    rw [List.getD_eq_getElem _ _ (by omega)] at h1
    have := (h _ (List.getElem_mem (show i + 1 < g.length by omega))).1
    omega
  · obtain rfl : j = i + 1 := by omega
    have := List.isChain_iff_getElem.1 hadj i hj
    omega

private theorem getD_set_of_ne {g : Grid} {i j x : ℕ} (h : i ≠ j) :
    (g.set i x).getD j 0 = g.getD j 0 := by
  simp [List.getElem?_set_ne h]

/-- The landing site of a leftward move at level `n` from column `i` is the nearest column to the
left with an entry at level `n - 1` and none at level `n`. -/
def landing? (g : Grid) (n i : ℕ) : Option ℕ :=
  (List.range i).findRev? fun k ↦ g.getD k 0 == n - 1

/-- The leftmost column that clashes at level `n` with a column to its right. -/
def clashing? (g : Grid) (n : ℕ) : Option ℕ :=
  (List.range g.length).find? fun i ↦ (List.range g.length).any fun j ↦ decide (Clash g n i j)

/-- Leftward Move x at level `n` slides the left member of the first clash within its level to
the landing site, provided its column has no entry above level `n`. -/
def moveXL (n : ℕ) (g : Grid) : Grid :=
  match clashing? g n with
  | none => g
  | some i =>
    if g.getD i 0 = n then
      match landing? g n i with
      | none => g
      | some k => (g.set i (n - 1)).set k n
    else g

/-- Move x(D;L) of (119f) moves entries leftward when it runs right to left, and the rightward
rule is its mirror image. -/
def moveX : Edge → ℕ → Grid → Grid
  | .right, n => moveXL n
  | .left, n => List.revConj (moveXL n)

/-- `Marks.move r i k` slides one mark within row `r` from column `i` to column `k`. -/
def Marks.move (r i k : ℕ) (m : Marks) : Marks :=
  m.modify r fun row ↦ (row.set i false).set k true

/-- Moving the level-`n` entry out of a column reaching above level `n` leaves a hole (32). -/
theorem Marks.not_isContinuous_move {g : Grid} {n i k : ℕ} (hi : i < g.length) (hn : n < g[i])
    (hn1 : 1 ≤ n) (hk : k ≠ i) : ¬ Marks.IsContinuous (Marks.move (n - 1) i k (rows g)) := by
  intro h
  have hlen : n < peak g := hn.trans_le (le_peak (List.getElem_mem hi))
  have := Marks.isContinuous_iff.1 h (n - 1) (by simp [Marks.move]; omega) i
    (by simp [Marks.move, hi]) (by simp [Marks.move, hi])
  simp [Marks.move, show n - 1 + 1 = n by omega, show n - 1 ≠ n by omega, hn, hk] at this

theorem moveXL_eq_or (n : ℕ) (g : Grid) :
    moveXL n g = g ∨ ∃ i j k, i < g.length ∧ j < g.length ∧ Clash g n i j ∧ g.getD i 0 = n ∧
      g.getD k 0 = n - 1 ∧ moveXL n g = (g.set i (n - 1)).set k n := by
  unfold moveXL clashing?
  split
  · exact .inl rfl
  next i hi =>
    obtain ⟨j, hj, hcl⟩ := List.any_eq_true.1 (List.find?_some hi :)
    simp only [List.mem_range, decide_eq_true_eq] at hj hcl
    split_ifs with hn
    · split
      · exact .inl rfl
      next k hk =>
        rw [landing?, List.findRev?_eq_find?_reverse] at hk
        exact .inr ⟨i, j, k, by simpa using List.mem_of_find?_eq_some hi, hj, hcl, hn,
          by simpa using List.find?_some hk, rfl⟩
    · exact .inl rfl

theorem moveXL_eq_self_of_not_clash {n : ℕ} {g : Grid}
    (h : ∀ i < g.length, ∀ j < g.length, ¬ Clash g n i j) : moveXL n g = g :=
  (moveXL_eq_or n g).resolve_right fun ⟨i, j, _, hi, hj, hc, _⟩ ↦ h i hi j hj hc

-- (32)
theorem moveXL_getD_of_lt {n c : ℕ} {g : Grid} (hc : n < g.getD c 0) :
    (moveXL n g).getD c 0 = g.getD c 0 := by
  rcases moveXL_eq_or n g with h | ⟨i, -, k, -, -, -, hi, hk, h⟩
  · rw [h]
  · rw [h, getD_set_of_ne (by rintro rfl; omega), getD_set_of_ne (by rintro rfl; omega)]

theorem not_clash_of_peak_le {g : Grid} (hc : IsCulminative g) {n i j : ℕ} (hn : peak g ≤ n)
    (hi : i < g.length) (hj : j < g.length) : ¬ Clash g n i j := by
  rintro ⟨hij, hni, hnj, -⟩
  rw [List.getD_eq_getElem _ _ hi] at hni
  rw [List.getD_eq_getElem _ _ hj] at hnj
  have := le_peak (List.getElem_mem hi)
  have := le_peak (List.getElem_mem hj)
  exact hij.ne (hc.eq_of_eq_peak hi hj (by omega) (by omega))

/-- On a culminative grid, Move x never moves the absolute peak (31). -/
theorem moveXL_getD_peak {g : Grid} (hc : IsCulminative g) {i n : ℕ} (hi : i < g.length)
    (hp : g[i] = peak g) : (moveXL n g).getD i 0 = g[i] := by
  rw [← List.getD_eq_getElem g 0 hi]
  rcases lt_or_ge n (peak g) with h | h
  · exact moveXL_getD_of_lt (by rwa [List.getD_eq_getElem _ _ hi, hp])
  · rw [moveXL_eq_self_of_not_clash fun _ hi' _ hj ↦ not_clash_of_peak_le hc h hi' hj]

/-! ### The End Rule, extrametricality, and Perfect Grid Construction (§3.2, §3.3) -/

/-! #### The last index -/

/-- The last index whose element satisfies `p`. -/
def lastIdx? (p : ℕ → Bool) : List ℕ → Option ℕ
  | [] => none
  | x :: l => ((lastIdx? p l).map (· + 1)).or (if p x then some 0 else none)

@[simp] theorem lastIdx?_nil (p : ℕ → Bool) : lastIdx? p [] = none := rfl

theorem lastIdx?_cons (p : ℕ → Bool) (x : ℕ) (l : List ℕ) :
    lastIdx? p (x :: l) = ((lastIdx? p l).map (· + 1)).or (if p x then some 0 else none) := rfl

theorem lastIdx?_cons_of_some {p : ℕ → Bool} {l : List ℕ} {i : ℕ} (h : lastIdx? p l = some i)
    (x : ℕ) : lastIdx? p (x :: l) = some (i + 1) := by
  simp [lastIdx?_cons, h]

theorem lastIdx?_append (p : ℕ → Bool) (l₁ l₂ : List ℕ) :
    lastIdx? p (l₁ ++ l₂) = ((lastIdx? p l₂).map (· + l₁.length)).or (lastIdx? p l₁) := by
  induction l₁ with
  | nil => simp
  | cons x l ih =>
    rw [List.cons_append, lastIdx?_cons, lastIdx?_cons, ih]
    cases lastIdx? p l₂ <;> cases lastIdx? p l <;> simp [Nat.add_assoc]

theorem lastIdx?_eq_some {p : ℕ → Bool} {l : List ℕ} {i : ℕ} (h : lastIdx? p l = some i) :
    ∃ hi : i < l.length, p l[i] = true := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    rw [lastIdx?_cons] at h
    cases hl : lastIdx? p l with
    | none =>
      rw [hl] at h
      split_ifs at h with hx <;> simp only [Option.map_none, Option.none_or,
        Option.some.injEq, reduceCtorEq] at h
      exact ⟨by simp [← h], by simpa [← h] using hx⟩
    | some j =>
      rw [hl] at h
      obtain ⟨hj, hpj⟩ := ih hl
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at h
      exact ⟨by simp; omega, by simpa [← h] using hpj⟩

theorem lastIdx?_eq_none {p : ℕ → Bool} {l : List ℕ} :
    lastIdx? p l = none ↔ ∀ x ∈ l, p x = false := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [lastIdx?_cons, Option.or_eq_none_iff, Option.map_eq_none_iff, ih]
    split_ifs with hx <;> simp [hx]

theorem lastIdx?_eq_findIdx?_reverse (p : ℕ → Bool) (l : List ℕ) :
    lastIdx? p l = (l.reverse.findIdx? p).map (l.length - 1 - ·) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [lastIdx?_cons, ih, List.reverse_cons, List.findIdx?_append]
    cases h : l.reverse.findIdx? p with
    | none => cases hx : p x <;> simp [List.findIdx?_cons, hx]
    | some j =>
      have := (List.findIdx?_eq_some_iff_getElem.1 h).1
      simp only [List.length_reverse] at this
      simp only [Option.map_some, Option.some_or, Option.some.injEq, List.length_cons]
      omega

private theorem reverse_set_reverse {l : List ℕ} {i : ℕ} (hi : i < l.length) (x : ℕ) :
    (l.reverse.set (l.length - 1 - i) x).reverse = l.set i x := by
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [List.length_reverse, List.length_set] at h1 h2
  simp only [List.getElem_reverse, List.getElem_set, List.length_reverse, List.length_set]
  split_ifs <;> first | omega | (congr 1; omega)

/-! #### The End Rule -/

/-- The edge-most column reaching level `n`. -/
def edgeIdx? : Edge → ℕ → Grid → Option ℕ
  | .left, n, g => g.findIdx? (n ≤ ·)
  | .right, n, g => lastIdx? (n ≤ ·) g

/-- A rule applied at an edge runs as it is from the left and as its mirror image from the
right. -/
def fromEdge : Edge → (Grid → Grid) → Grid → Grid
  | .left, f => f
  | .right, f => List.revConj f

/-- The End Rule ER(E;L;FCO) of (16), (97) and (119a) promotes the edge-most entry at the
highest level present below `L` by one level, so that the edge-most stress of a constituent
becomes its main stress and, absent stresses, its edge syllable is stressed. Without Forward Clash
Override the promotion is withheld when it would clash. -/
def endRule (e : Edge) (L : ℕ) (fco : Bool) : Grid → Grid :=
  fromEdge e fun g ↦
    let n := min (L - 1) (peak g)
    match g.findIdx? (n ≤ ·) with
    | none => g
    | some i =>
      let g' := g.set i (max (g.getD i 0) (n + 1))
      if fco ∨ ∀ j < g.length, ¬ Clash g' (n + 1) i j ∧ ¬ Clash g' (n + 1) j i then g' else g

theorem endRule_right (L : ℕ) (fco : Bool) (g : Grid) :
    endRule .right L fco g = (endRule .left L fco g.reverse).reverse := rfl

/-- Extrametricality elm(E) of (119c) hides the edge column from the rule applied inside. -/
def elm : Edge → (Grid → Grid) → Grid → Grid
  | .left, f, [] => f []
  | .left, f, x :: t => x :: f t
  | .right, f, g => f g.dropLast ++ g.drop (g.length - 1)

/-- One sweep of Perfect Grid Construction raises a column to the stress level when neither
neighbour reaches it, `prev` being the height of the column just passed. -/
def sweep : ℕ → Grid → Grid
  | _, [] => []
  | prev, x :: t =>
    let x' := if x < 2 ∧ prev < 2 ∧ t.headD 0 < 2 then 2 else x
    x' :: sweep x' t

theorem sweep_cons_of_two_le {x : ℕ} (hx : 2 ≤ x) (p : ℕ) (t : Grid) :
    sweep p (x :: t) = x :: sweep x t := by
  simp [sweep, show ¬ x < 2 by omega]

/-- Whether a sweep starts at a peak or a trough, `A` of (119b). -/
inductive Altitude
  | peak
  | trough
  deriving DecidableEq, Repr

namespace Altitude

/-- The other altitude. -/
def flip : Altitude → Altitude
  | peak => trough
  | trough => peak

/-- The height of a column at a peak, stressed, or at a trough, unstressed. -/
def height : Altitude → ℕ
  | peak => 2
  | trough => 1

/-- A sweep behaves as if it had passed a column of this height before its first column, an
unstressed one before a peak and a stress before a trough. -/
def start (a : Altitude) : ℕ := a.flip.height

end Altitude

/-- Perfect Grid Construction PG(D;A) of (61), (62) and (119b) lays down a clash-free, maximally
alternating stress level by a sweep in direction `D` starting from a peak or a trough. -/
def pg (d : Edge) (a : Altitude) : Grid → Grid :=
  match d with
  | .left => sweep a.start
  | .right => List.revConj (sweep a.start)

/-- The alternating stress level is `2, 1, 2, …` from a peak and `1, 2, 1, …` from a trough. -/
def alt : Altitude → ℕ → Grid
  | _, 0 => []
  | a, n + 1 => a.height :: alt a.flip n

@[simp] theorem alt_length (a : Altitude) (n : ℕ) : (alt a n).length = n := by
  induction n generalizing a <;> simp [alt, *]

theorem alt_getD (a : Altitude) (n i : ℕ) :
    (alt a n).getD i 0 = if i < n then (if (i % 2 = 0 ↔ a = .peak) then 2 else 1) else 0 := by
  induction n generalizing a i with
  | zero => simp [alt]
  | succ n ih =>
    cases i with
    | zero => cases a <;> simp [alt, Altitude.height]
    | succ i =>
      rw [alt, List.getD_cons_succ, ih]
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;> cases a <;>
        simp [h, Nat.succ_mod_two_eq_zero_iff, Altitude.flip]

theorem mem_alt {a : Altitude} {n x : ℕ} (hx : x ∈ alt a n) : 1 ≤ x ∧ x ≤ 2 := by
  induction n generalizing a with
  | zero => simp [alt] at hx
  | succ n ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · cases a <;> simp [Altitude.height]
    · exact ih hx

theorem sweep_replicate (a : Altitude) (n : ℕ) :
    sweep a.start (List.replicate n 1) = alt a n := by
  induction n generalizing a with
  | zero => simp [sweep, alt]
  | succ n ih =>
    have hd : (List.replicate n 1).head?.getD 0 < 2 := by cases n <;> simp [List.replicate_succ]
    rw [List.replicate_succ, sweep, alt, ← ih a.flip]
    cases a <;> simp [hd, Altitude.start, Altitude.flip, Altitude.height]

theorem sweep_replicate_append (a : Altitude) (m : ℕ) :
    sweep a.start (List.replicate (m + 1) 1 ++ [2]) = alt a m ++ [1, 2] := by
  induction m generalizing a with
  | zero => cases a <;> simp [sweep, alt, Altitude.start, Altitude.flip, Altitude.height]
  | succ m ih =>
    have := ih a.flip
    rw [List.replicate_succ, List.cons_append] at this ⊢
    rw [sweep, alt]
    cases a <;> simp_all [List.replicate_succ, Altitude.start, Altitude.flip, Altitude.height]

/-- The distance of column `i` of `n` from the edge a sweep in direction `d` starts at. -/
def startDist : Edge → ℕ → ℕ → ℕ
  | .left, _, i => i
  | .right, n, i => n - 1 - i

-- (62), (62a), (62b), (62c), (62d)
theorem pg_replicate_getD (d : Edge) (a : Altitude) {n i : ℕ} (hi : i < n) :
    (pg d a (List.replicate n 1)).getD i 0 =
      if (startDist d n i % 2 = 0 ↔ a = .peak) then 2 else 1 := by
  cases d with
  | left => cases a <;> simp only [pg, sweep_replicate] <;> rw [alt_getD] <;> simp [hi, startDist]
  | right =>
    cases a <;> simp only [pg, List.revConj, List.reverse_replicate, sweep_replicate] <;>
      rw [List.getD_reverse _ (by simpa using hi), alt_getD] <;>
      simp [startDist, show n - 1 - i < n by omega]

theorem noClash_pg_replicate (d : Edge) (a : Altitude) (n : ℕ) :
    NoClash (pg d a (List.replicate n 1)) := by
  have hlen : (pg d a (List.replicate n 1)).length = n := by
    cases d <;> simp [pg, List.revConj, sweep_replicate]
  refine noClash_of_alternating (fun x hx ↦ ?_) (List.isChain_iff_getElem.2 fun i hi ↦ ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have := pg_replicate_getD d a (hlen ▸ hi)
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this]
    split_ifs <;> omega
  · have h1 := pg_replicate_getD d a (show i < n by omega)
    have h2 := pg_replicate_getD d a (show i + 1 < n by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at h1 h2
    rw [h1, h2]
    cases d <;> cases a <;> simp [startDist] <;> (try split_ifs) <;> omega

private theorem edgeIdx?_getD {e : Edge} {n : ℕ} {g : Grid} {i : ℕ} (h : edgeIdx? e n g = some i) :
    i < g.length ∧ n ≤ g.getD i 0 := by
  cases e with
  | left =>
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    exact ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; simpa using hp⟩
  | right =>
    obtain ⟨hi, hp⟩ := lastIdx?_eq_some h
    exact ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; simpa using hp⟩

private theorem endRule_left_of_peak {L : ℕ} {fco : Bool} {g : Grid} (hL : peak g ≤ L - 1)
    {i : ℕ} (hi : edgeIdx? .left (peak g) g = some i) :
    endRule .left L fco g = g.set i (peak g + 1) := by
  have hgi : g.getD i 0 = peak g := le_antisymm (getD_le_peak i) (edgeIdx?_getD hi).2
  have hj : ∀ j ≠ i, ¬ peak g + 1 ≤ (g.set i (peak g + 1)).getD j 0 := fun j hj h ↦ by
    have := getD_le_peak (g := g) j
    rw [getD_set_of_ne hj.symm] at h
    omega
  have hi' : g.findIdx? (peak g ≤ ·) = some i := hi
  simp only [endRule, fromEdge, min_eq_right hL, hi', hgi, Nat.max_eq_right (Nat.le_succ _)]
  exact ite_eq_left (Or.inr fun j _ ↦ ⟨fun h ↦ hj j h.1.ne' h.2.2.1, fun h ↦ hj j h.1.ne h.2.1⟩)

theorem endRule_of_peak {e : Edge} {L : ℕ} {fco : Bool} {g : Grid} (hL : peak g ≤ L - 1)
    {i : ℕ} (hi : edgeIdx? e (peak g) g = some i) :
    endRule e L fco g = g.set i (peak g + 1) := by
  cases e with
  | left => exact endRule_left_of_peak hL hi
  | right =>
    have hil := (edgeIdx?_getD hi).1
    rw [edgeIdx?, lastIdx?_eq_findIdx?_reverse, Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hjl : j < g.length := by simpa using (List.findIdx?_eq_some_iff_getElem.1 hj).1
    rw [endRule_right, endRule_left_of_peak (by simpa) (by simpa [edgeIdx?] using hj), peak_reverse]
    have := reverse_set_reverse (l := g) (i := g.length - 1 - j) (by omega) (peak g + 1)
    rwa [show g.length - 1 - (g.length - 1 - j) = j by omega] at this

theorem peak_replicate_one {n : ℕ} (hn : 0 < n) : peak (List.replicate n 1) = 1 :=
  le_antisymm (peak_le fun x hx ↦ by simp [List.eq_of_mem_replicate hx])
    (le_peak (List.mem_replicate.2 ⟨hn.ne', rfl⟩))

theorem endRule_left_replicate {n : ℕ} (hn : 0 < n) (fco : Bool) :
    endRule .left 2 fco (List.replicate n 1) = 2 :: List.replicate (n - 1) 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hp := peak_replicate_one hn
  rw [endRule_of_peak (by rw [hp]) (i := 0) (by rw [hp]; rfl), hp]
  rfl

/-! #### The End Rule at the stress level -/

private theorem min_one_peak {g : Grid} {x : ℕ} (hx : x ∈ g) (h1 : 1 ≤ x) :
    min (2 - 1) (peak g) = 1 :=
  Nat.min_eq_left (h1.trans (le_peak hx))

theorem endRule_le_two {e : Edge} {fco : Bool} {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2) :
    ∀ x ∈ endRule e 2 fco g, x ≤ 2 := by
  have key (g : Grid) (h2 : ∀ x ∈ g, x ≤ 2) : ∀ x ∈ endRule .left 2 fco g, x ≤ 2 := by
    intro x hx
    simp only [endRule, fromEdge] at hx
    split at hx
    · exact h2 x hx
    next i _ =>
      have := (getD_le_peak (g := g) i).trans (peak_le h2)
      split_ifs at hx
      · rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact h2 x hx
        · omega
      · exact h2 x hx
  cases e with
  | left => exact key g h2
  | right =>
    simp only [endRule_right, List.mem_reverse]
    exact key _ fun x hx ↦ h2 x (List.mem_reverse.1 hx)

theorem endRule_left_of_two_le {x : ℕ} (hx : 2 ≤ x) (t : Grid) (fco : Bool) :
    endRule .left 2 fco (x :: t) = x :: t := by
  simp only [endRule, fromEdge, min_one_peak (List.mem_cons_self ..) (by omega : 1 ≤ x),
    List.findIdx?_cons, decide_eq_true (by omega : 1 ≤ x), ↓reduceIte, List.set_cons_zero,
    List.getD_cons_zero, Nat.max_eq_left hx, ite_self]

theorem endRule_left_singleton {x : ℕ} (hx : 1 ≤ x) (fco : Bool) :
    endRule .left 2 fco [x] = [max x 2] := by
  simp only [endRule, fromEdge, min_one_peak (List.mem_cons_self ..) hx, List.findIdx?_cons,
    decide_eq_true hx, ↓reduceIte, List.set_cons_zero, List.getD_cons_zero]
  rw [ite_eq_left (Or.inr fun j hj ↦ ?_)]
  simp only [List.length_singleton] at hj
  obtain rfl : j = 0 := by omega
  simp [Clash]

theorem endRule_left_two {y : ℕ} (hy : 1 ≤ y) (t : Grid) (fco : Bool) :
    endRule .left 2 fco (1 :: y :: t) = if fco ∨ y < 2 then 2 :: y :: t else 1 :: y :: t := by
  have key : (∀ j < (1 :: y :: t).length,
      ¬ Clash (2 :: y :: t) (1 + 1) 0 j ∧ ¬ Clash (2 :: y :: t) (1 + 1) j 0) ↔ y < 2 := by
    constructor
    · intro h
      have := (h 1 (by simp)).1
      simp [Clash] at this
      omega
    · intro hy2 j _
      constructor
      · rintro ⟨hij, -, h2, hk⟩
        rcases j with _ | _ | j
        · omega
        · simp at h2; omega
        · have := hk 1 (by omega) (by omega)
          simp at this
          omega
      · rintro ⟨hji, -⟩
        omega
  have hidx : (1 :: y :: t).findIdx? (1 ≤ ·) = some 0 := by simp [List.findIdx?_cons]
  simp only [endRule, fromEdge, min_one_peak (List.mem_cons_self ..) le_rfl, hidx,
    List.set_cons_zero,
    List.getD_cons_zero, Nat.max_eq_right (Nat.le_succ 1), key]

theorem endRule_right_singleton {x : ℕ} (hx : 1 ≤ x) (fco : Bool) :
    endRule .right 2 fco [x] = [max x 2] := by
  rw [endRule_right, List.reverse_singleton, endRule_left_singleton hx]; rfl

theorem endRule_right_two {y : ℕ} (hy : 1 ≤ y) (t : Grid) (fco : Bool) :
    endRule .right 2 fco (t ++ [y, 1]) = if fco ∨ y < 2 then t ++ [y, 2] else t ++ [y, 1] := by
  rw [endRule_right, show (t ++ [y, 1]).reverse = 1 :: y :: t.reverse by simp, endRule_left_two hy]
  split_ifs <;> simp

theorem endRule_right_replicate {n : ℕ} (hn : 0 < n) (fco : Bool) :
    endRule .right 2 fco (List.replicate n 1) = List.replicate (n - 1) 1 ++ [2] := by
  rw [endRule_right, List.reverse_replicate, endRule_left_replicate hn]; simp

/-! #### Main stress -/

/-- Column `i` carries the main stress when it is strictly taller than every other column. -/
def MainStressAt (g : Grid) (i : ℕ) : Prop :=
  i < g.length ∧ ∀ j < g.length, j ≠ i → g.getD j 0 < g.getD i 0

instance (g : Grid) (i : ℕ) : Decidable (MainStressAt g i) := by
  unfold MainStressAt; infer_instance

theorem MainStressAt.isCulminative {g : Grid} {i : ℕ} (h : MainStressAt g i) :
    IsCulminative g :=
  isCulminative_of_forall_lt h.1 fun j hj hne ↦ by
    have := h.2 j hj hne
    rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ h.1] at this

theorem mainStressAt_set {g : Grid} {m i : ℕ} (h2 : ∀ x ∈ g, x ≤ m) (hi : i < g.length) :
    MainStressAt (g.set i (m + 1)) i := by
  refine ⟨by simpa using hi, fun j _ hne ↦ ?_⟩
  rw [getD_set_of_ne hne.symm, List.getD_eq_getElem (g.set i _) 0 (by simpa using hi),
    List.getElem_set_self]
  exact Nat.lt_succ_of_le ((getD_le_peak j).trans (peak_le h2))

theorem mainStressAt_append_cons {t u : Grid} {y : ℕ} (ht : ∀ x ∈ t, x < y)
    (hu : ∀ x ∈ u, x < y) : MainStressAt (t ++ y :: u) t.length := by
  refine ⟨by simp, fun j hj hne ↦ ?_⟩
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h]; exact ht _ (List.getElem_mem h)
  · obtain ⟨k, rfl⟩ : ∃ k, j = t.length + 1 + k := ⟨j - t.length - 1, by omega⟩
    simp only [List.length_append, List.length_cons] at hj
    rw [List.getD_append_right _ _ _ _ (by omega),
      show t.length + 1 + k - t.length = k + 1 by omega,
      List.getD_cons_succ, List.getD_eq_getElem _ _ (by omega)]
    exact hu _ (List.getElem_mem _)

theorem mainStressAt_endRule {e : Edge} {L : ℕ} {fco : Bool} {g : Grid} (hL : peak g ≤ L - 1)
    {i : ℕ} (hi : edgeIdx? e (peak g) g = some i) : MainStressAt (endRule e L fco g) i := by
  rw [endRule_of_peak hL hi]
  exact mainStressAt_set (fun x hx ↦ le_peak hx) (edgeIdx?_getD hi).1

theorem endRule_three_of_edgeIdx? {e : Edge} {fco : Bool} {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2)
    {i : ℕ} (hi : edgeIdx? e 2 g = some i) : endRule e 3 fco g = g.set i 3 := by
  have hp : peak g = 2 := le_antisymm (peak_le h2) ((edgeIdx?_getD hi).2.trans (getD_le_peak i))
  rw [endRule_of_peak (by rw [hp]) (by rwa [hp]), hp]

theorem mainStressAt_of_edgeIdx? {e : Edge} {fco : Bool} {g : Grid} (h2 : ∀ x ∈ g, x ≤ 2)
    {i : ℕ} (hi : edgeIdx? e 2 g = some i) : MainStressAt (endRule e 3 fco g) i := by
  rw [endRule_three_of_edgeIdx? h2 hi]
  exact mainStressAt_set h2 (edgeIdx?_getD hi).1

/-! ### Garawa and Winnebago (63), (65) -/

/-- In Garawa (63) the End Rule stresses the initial syllable, Perfect Grid Construction sweeps
right to left from a trough, and the End Rule at word level makes the initial stress the main
stress. -/
def garawa (n : ℕ) : Grid :=
  endRule .left 3 false (pg .right .trough (endRule .left 2 false (List.replicate n 1)))

theorem garawa_eq {n : ℕ} (hn : 2 ≤ n) :
    garawa n = 3 :: 1 :: (alt .trough (n - 2)).reverse := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : endRule .left 2 false (List.replicate (m + 2) 1) = 2 :: List.replicate (m + 1) 1 :=
    endRule_left_replicate (by omega) false
  have h2 : pg .right .trough (2 :: List.replicate (m + 1) 1) =
      2 :: 1 :: (alt .trough m).reverse := by
    simp [pg, List.revConj, List.reverse_replicate, sweep_replicate_append]
  have hle : ∀ x ∈ 2 :: 1 :: (alt .trough m).reverse, x ≤ 2 := by
    simpa using fun x hx ↦ (mem_alt hx).2
  rw [garawa, h1, h2,
    endRule_three_of_edgeIdx? hle (i := 0) (by simp [edgeIdx?, List.findIdx?_cons])]
  rfl

theorem garawa_initial {n : ℕ} (hn : 2 ≤ n) : (garawa n).getD 0 0 = 3 := by
  rw [garawa_eq hn]; rfl

theorem garawa_second {n : ℕ} (hn : 2 ≤ n) : (garawa n).getD 1 0 = 1 := by
  rw [garawa_eq hn]; rfl

theorem garawa_getD {n i : ℕ} (hi : 2 ≤ i) (hin : i < n) :
    (garawa n).getD i 0 = if (n - 1 - i) % 2 = 1 then 2 else 1 := by
  obtain ⟨i, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [garawa_eq (by omega), List.getD_cons_succ, List.getD_cons_succ,
    List.getD_reverse _ (by simp; omega), alt_getD, alt_length]
  have h1 : n - 2 - 1 - i < n - 2 := by omega
  have h2 : n - 2 - 1 - i = n - 1 - (i + 2) := by omega
  rw [ite_eq_left h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (n - 1 - (i + 2)) with h | h <;> simp [h]

/-- In Winnebago (65), with the initial syllable extrametrical, a trough-first sweep from the left
and the End Rule at word level put main stress on the third syllable. -/
def winnebago (n : ℕ) : Grid :=
  endRule .left 3 false (elm .left (pg .left .trough) (List.replicate n 1))

theorem winnebago_eq {n : ℕ} (hn : 3 ≤ n) :
    winnebago n = 1 :: 1 :: 3 :: alt .trough (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : elm .left (pg .left .trough) (List.replicate (m + 3) 1) =
      1 :: 1 :: 2 :: alt .trough m := by
    rw [List.replicate_succ]
    simp only [elm, pg, sweep_replicate]
    rfl
  have hle : ∀ x ∈ 1 :: 1 :: 2 :: alt .trough m, x ≤ 2 := by
    simpa using fun x hx ↦ (mem_alt hx).2
  rw [winnebago, h1,
    endRule_three_of_edgeIdx? hle (i := 2) (by simp [edgeIdx?, List.findIdx?_cons])]
  rfl

/-! ### Stress three syllables from an edge (§3.2, §3.3) -/

/-- Perfect Grid Construction stresses an unstressed word, with or without an extrametrical
syllable at an edge, in the parameter space of §3.2. -/
def alternating (d : Edge) (a : Altitude) (x : Option Edge) (n : ℕ) : Grid :=
  x.elim (pg d a) (elm · (pg d a)) (List.replicate n 1)

/-- Stress three syllables in, in every word long enough, is the extrametricality variant of a
trough-first sweep from the left and arises from no other setting of the parameters, so grid
theory derives postpeninitial stress only as Winnebago has it. -/
theorem postpeninitial_iff (d : Edge) (a : Altitude) (x : Option Edge) :
    (∀ n, 4 ≤ n → (alternating d a x n).findIdx? (2 ≤ ·) = some 2) ↔
      d = .left ∧ a = .trough ∧ x = some .left := by
  constructor
  · intro h
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    revert h4 h5
    rcases x with _ | _ | _ <;> cases d <;> cases a <;> decide
  · rintro ⟨rfl, rfl, rfl⟩ n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [alternating, Option.elim_some, List.replicate_succ]
    simp only [elm, pg, sweep_replicate]
    simp [alt, Altitude.height, Altitude.flip, List.findIdx?_cons]

/-- Antepenultimate stress, the mirror image, is the extrametricality variant of a trough-first
sweep from the right and arises from no other setting of the parameters. -/
theorem antepenultimate_iff (d : Edge) (a : Altitude) (x : Option Edge) :
    (∀ n, 4 ≤ n → lastIdx? (2 ≤ ·) (alternating d a x n) = some (n - 3)) ↔
      d = .right ∧ a = .trough ∧ x = some .right := by
  constructor
  · intro h
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    revert h4 h5
    rcases x with _ | _ | _ <;> cases d <;> cases a <;> decide
  · rintro ⟨rfl, rfl, rfl⟩ n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h : alternating .right .trough (some .right) (m + 4) =
        (alt .trough (m + 1)).reverse ++ [2, 1, 1] := by
      simp only [alternating, Option.elim_some, elm, pg, List.revConj, List.dropLast_replicate,
        List.drop_replicate, List.length_replicate, List.reverse_replicate, sweep_replicate]
      simp [alt, Altitude.height, Altitude.flip]
    rw [h, lastIdx?_append]
    simp [lastIdx?_cons]

/-! ### Hawaiian (64) -/

/-- In simplified Hawaiian (64), long vowels aside, the final syllable is extrametrical, the End
Rule applies finally and then initially at the stress level, Perfect Grid Construction sweeps
right to left from the final stress, and the End Rule applies finally at word level. -/
def hawaiian (n : ℕ) : Grid :=
  elm .right (endRule .right 3 false ∘ pg .right .peak ∘ endRule .left 2 false ∘
    endRule .right 2 false) (List.replicate n 1)

-- (64a)
theorem hawaiian_three : hawaiian 3 = [1, 3, 1] := by decide

/-- After the End Rule stresses both edges, the sweep back from the penult leaves an initial dactyl
((64b), (64c)). -/
theorem hawaiian_eq {n : ℕ} (hn : 4 ≤ n) :
    hawaiian n = 2 :: 1 :: (alt .trough (n - 4)).reverse ++ [3, 1] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h1 : endRule .right 2 false (List.replicate (m + 3) 1) =
      1 :: 1 :: (List.replicate m 1 ++ [2]) := by
    rw [endRule_right_replicate (by omega)]; rfl
  have h2 : endRule .left 2 false (1 :: 1 :: (List.replicate m 1 ++ [2])) =
      2 :: 1 :: (List.replicate m 1 ++ [2]) := by
    rw [endRule_left_two le_rfl]; rfl
  have h3 : pg .right .peak (2 :: 1 :: (List.replicate m 1 ++ [2])) =
      2 :: 1 :: ((alt .trough m).reverse ++ [2]) := by
    have : (2 :: 1 :: (List.replicate m 1 ++ [2])).reverse =
        2 :: (List.replicate (m + 1) 1 ++ [2]) := by
      simp [List.replicate_succ', List.reverse_replicate]
    have key := sweep_replicate_append .trough m
    simp only [Altitude.start, Altitude.flip, Altitude.height] at key
    simp [pg, List.revConj, this, sweep_cons_of_two_le le_rfl, key]
  have hle : ∀ x ∈ 2 :: 1 :: ((alt .trough m).reverse ++ [2]), x ≤ 2 := by
    simpa using fun x hx ↦ hx.elim (fun h ↦ (mem_alt h).2) Eq.le
  have h4 : endRule .right 3 false (2 :: 1 :: ((alt .trough m).reverse ++ [2])) =
      2 :: 1 :: ((alt .trough m).reverse ++ [3]) := by
    rw [endRule_three_of_edgeIdx? hle (i := m + 2)]
    · simp
    · rw [edgeIdx?, show 2 :: 1 :: ((alt .trough m).reverse ++ [2]) =
        (2 :: 1 :: (alt .trough m).reverse) ++ [2] by simp, lastIdx?_append]
      simp [lastIdx?_cons]
  simp only [hawaiian, elm, Function.comp_apply, List.dropLast_replicate, List.drop_replicate,
    List.length_replicate]
  rw [show m + 4 - 1 = m + 3 from rfl, h1, h2, h3, h4]
  simp

theorem hawaiian_initial {n : ℕ} (hn : 4 ≤ n) : (hawaiian n).getD 0 0 = 2 := by
  rw [hawaiian_eq hn]; rfl

theorem hawaiian_mainStressAt {n : ℕ} (hn : 2 ≤ n) : MainStressAt (hawaiian n) (n - 2) := by
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn
  · decide
  · decide
  · have ht : ∀ x ∈ 2 :: 1 :: (alt .trough (n - 4)).reverse, x < 3 := by
      simpa using fun x hx ↦ Nat.lt_succ_of_le (mem_alt hx).2
    have h := mainStressAt_append_cons (u := [1]) ht (by simp)
    rw [hawaiian_eq hn]
    simpa [show n - 4 + 2 = n - 2 by omega] using h

/-- No perfect grid gives Hawaiian's initial dactyl, whatever its direction, starting altitude and
extrametricality, so the End Rule must stress both edges before the sweep. -/
theorem hawaiian_ne_alternating (d : Edge) (a : Altitude) (x : Option Edge) :
    endRule .right 3 false (alternating d a x 5) ≠ hawaiian 5 := by
  rcases x with _ | _ | _ <;> cases d <;> cases a <;> decide

/-! ### The End Rule at the phrase and Move x (28) to (31) -/

/-- The citation grids of *achromatic*, *lens*, *Dundee*, *marmalade* (28), *antique*, *dealer*,
and *chair* (31). -/
def achromatic : Grid := [2, 1, 3, 1]
def lens : Grid := [3]
def dundee : Grid := [2, 3]
def marmalade : Grid := [3, 1, 2]
def antique : Grid := [2, 3]
def dealer : Grid := [3, 1]
def chair : Grid := [3]

-- (29a), (30a)
theorem achromatic_lens :
    moveX .right 3 (endRule .right 4 false (achromatic ++ lens)) = [3, 1, 2, 1, 4] := by decide

-- (29b), (30b)
theorem dundee_marmalade :
    moveX .right 3 (endRule .right 4 false (dundee ++ marmalade)) = [3, 2, 4, 1, 2] := by decide

-- (31a)
theorem antique_dealer :
    moveX .right 3 (endRule .left 4 false (antique ++ dealer)) = [2, 4, 3, 1] := by decide

-- (31b)
theorem antique_chair :
    moveX .right 3 (endRule .right 4 false (antique ++ chair)) = [3, 2, 4] := by decide

/-! ### Quantity: bipositional heavy syllables (§3.5, §3.7) -/

/-- A heavy syllable, one of two or more moras, occupies two grid positions with its nucleus above
the second, so it is intrinsically stressed (74); a light syllable occupies one. -/
def mora (m : Syllable.Weight) : Grid := if 2 ≤ m then [2, 1] else [1]

/-- Quantity Sensitivity QS of (119d) maps a syllable string to its grid. -/
def qs (w : List Syllable.Weight) : Grid := w.flatMap mora

/-- The grid position of the nucleus of syllable `k`. -/
def nucleus (w : List Syllable.Weight) (k : ℕ) : ℕ := (qs (w.take k)).length

theorem mora_of_two_le {m : Syllable.Weight} (h : 2 ≤ m) : mora m = [2, 1] := ite_eq_left h

theorem mora_of_lt {m : Syllable.Weight} (h : m < 2) : mora m = [1] := ite_eq_right (Nat.not_le.2 h)

theorem qs_cons (m : Syllable.Weight) (w : List Syllable.Weight) :
    qs (m :: w) = mora m ++ qs w :=
  List.flatMap_cons ..

theorem qs_append (w v : List Syllable.Weight) : qs (w ++ v) = qs w ++ qs v :=
  List.flatMap_append ..

theorem mem_mora {m x : ℕ} (hx : x ∈ mora m) : 1 ≤ x ∧ x ≤ 2 := by
  unfold mora at hx
  split_ifs at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> omega

theorem mem_qs {w : List Syllable.Weight} {x : ℕ} (hx : x ∈ qs w) : 1 ≤ x ∧ x ≤ 2 := by
  obtain ⟨m, -, hm⟩ := List.mem_flatMap.1 hx
  exact mem_mora hm

theorem qs_le_two (w : List Syllable.Weight) : ∀ x ∈ qs w, x ≤ 2 := fun _ hx ↦ (mem_qs hx).2

theorem qs_singleton (m : Syllable.Weight) : qs [m] = mora m := by simp [qs]

-- (74)
theorem qs_isChain (w : List Syllable.Weight) : (qs w).IsChain (fun a b ↦ a < 2 ∨ b < 2) := by
  induction w with
  | nil => simp [qs]
  | cons m w ih =>
    rw [qs_cons, List.isChain_append]
    refine ⟨?_, ih, ?_⟩ <;> unfold mora <;> split_ifs <;> simp

theorem noClash_qs (w : List Syllable.Weight) : NoClash (qs w) :=
  noClash_of_alternating (fun _ ↦ mem_qs) (qs_isChain w)

theorem qs_eq_nil_iff {w : List Syllable.Weight} : qs w = [] ↔ w = [] := by
  cases w with
  | nil => simp [qs]
  | cons m w => rw [qs_cons, mora]; split_ifs <;> simp

private theorem exists_append_singleton {v : List Syllable.Weight} (hv : v ≠ []) :
    ∃ t m, v = t ++ [m] := by
  obtain ⟨t, m, h⟩ := (List.eq_nil_or_concat v).resolve_left hv
  exact ⟨t, m, by rw [h, List.concat_eq_append]⟩

theorem exists_qs_eq_append_one {v : List Syllable.Weight} (hv : v ≠ []) :
    ∃ t, qs v = t ++ [1] := by
  obtain ⟨v, m, rfl⟩ := exists_append_singleton hv
  rw [qs_append, qs_singleton]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact ⟨qs v, by rw [mora_of_lt hm]⟩
  · exact ⟨qs v ++ [2], by rw [mora_of_two_le hm, List.append_assoc]; rfl⟩

@[simp] theorem nucleus_zero (w : List Syllable.Weight) : nucleus w 0 = 0 := rfl

theorem nucleus_cons_succ (m : Syllable.Weight) (w : List Syllable.Weight) (k : ℕ) :
    nucleus (m :: w) (k + 1) = (mora m).length + nucleus w k := by
  simp [nucleus, qs_cons]

theorem nucleus_append_length (v : List Syllable.Weight) (m : Syllable.Weight) :
    nucleus (v ++ [m]) v.length = (qs v).length := by
  simp [nucleus]

theorem findIdx?_qs (w : List Syllable.Weight) :
    (qs w).findIdx? (2 ≤ ·) = (w.findIdx? (2 ≤ ·)).map (nucleus w) := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, List.findIdx?_append, List.findIdx?_cons, ih]
    by_cases hm : 2 ≤ m
    · simp [mora_of_two_le hm, hm, List.findIdx?_cons]
    · simp [mora_of_lt (Nat.not_le.1 hm), hm, List.findIdx?_cons, nucleus_cons_succ,
        Option.map_map, Function.comp_def, Nat.add_comm]

theorem lastIdx?_qs (w : List Syllable.Weight) :
    lastIdx? (2 ≤ ·) (qs w) = (lastIdx? (2 ≤ ·) w).map (nucleus w) := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, lastIdx?_append, lastIdx?_cons, ih]
    by_cases hm : 2 ≤ m
    · cases lastIdx? (2 ≤ ·) w <;>
        simp [mora_of_two_le hm, hm, lastIdx?_cons, nucleus_cons_succ, Nat.add_comm]
    · cases lastIdx? (2 ≤ ·) w <;>
        simp [mora_of_lt (Nat.not_le.1 hm), hm, lastIdx?_cons, nucleus_cons_succ, Nat.add_comm]

theorem qs_eq_replicate {w : List Syllable.Weight} (h : ∀ m ∈ w, m < 2) :
    qs w = List.replicate w.length 1 := by
  induction w with
  | nil => rfl
  | cons m w ih =>
    rw [qs_cons, mora_of_lt (h m (List.mem_cons_self ..)),
      ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx), List.length_cons, List.replicate_succ]
    rfl

theorem nucleus_of_light {w : List Syllable.Weight} (h : ∀ m ∈ w, m < 2) (k : ℕ) :
    nucleus w k = min k w.length := by
  rw [nucleus, qs_eq_replicate fun x hx ↦ h x (List.mem_of_mem_take hx), List.length_replicate,
    List.length_take]

theorem lastIdx?_replicate_one (n : ℕ) : lastIdx? (2 ≤ ·) (List.replicate n 1) = none :=
  lastIdx?_eq_none.2 fun x hx ↦ by simp [List.eq_of_mem_replicate hx]

theorem lastIdx?_replicate_one_pos (n : ℕ) :
    lastIdx? (1 ≤ ·) (List.replicate (n + 1) 1) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, lastIdx?_cons_of_some ih]

/-! #### The three kinds of quantity-sensitive system without alternation (97), (98) -/

/-- The opposite edge, `Ē` of (97). -/
def opposite : Edge → Edge
  | .left => .right
  | .right => .left

/-- Fixed stress, (97) I, applies QS, ER(E;Σ) and ER(E;Wd), so the edge syllable and every heavy
syllable are stressed and the edge-most stress is the main stress. -/
def fixedStress (e : Edge) (fco : Bool) (w : List Syllable.Weight) : Grid :=
  endRule e 3 fco (endRule e 2 fco (qs w))

/-- The system of (97) II, `E` defaulting to `Ē`, applies QS, ER(Ē;Σ) and ER(E;Wd), putting main
stress on the `E`-most heavy syllable or, lacking heavies, on the `Ē` syllable. -/
def defaultOpposite (e : Edge) (w : List Syllable.Weight) : Grid :=
  endRule e 3 false (endRule (opposite e) 2 false (qs w))

/-- The system of (97) III, `E` defaulting to `E`, applies QS and then ER(E;Wd) to the highest
level present, putting main stress on the `E`-most heavy syllable or, lacking heavies, on the `E`
syllable. -/
def defaultSame (e : Edge) (w : List Syllable.Weight) : Grid :=
  endRule e 3 false (qs w)

private theorem mainStressAt_light {e : Edge} {w : List Syllable.Weight} (hw : w ≠ [])
    (hl : ∀ m ∈ w, m < 2) {i : ℕ} (hi : edgeIdx? e 1 (List.replicate w.length 1) = some i) :
    MainStressAt (defaultSame e w) i := by
  have hq := qs_eq_replicate hl
  have hp : peak (qs w) = 1 := by rw [hq]; exact peak_replicate_one (List.length_pos_of_ne_nil hw)
  exact mainStressAt_endRule (by rw [hp]; decide) (by rwa [hp, hq])

-- (98)
theorem khalkha_heavy {w : List Syllable.Weight} {k : ℕ} (hk : w.findIdx? (2 ≤ ·) = some k) :
    MainStressAt (defaultSame .left w) (nucleus w k) :=
  mainStressAt_of_edgeIdx? (qs_le_two w) (e := .left) (by rw [edgeIdx?, findIdx?_qs, hk]; rfl)

-- (98)
theorem khalkha_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultSame .left w) 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  exact mainStressAt_light hw hl (by rw [hn]; rfl)

-- (98)
theorem aguacatec_heavy {w : List Syllable.Weight} {k : ℕ} (hk : lastIdx? (2 ≤ ·) w = some k) :
    MainStressAt (defaultSame .right w) (nucleus w k) :=
  mainStressAt_of_edgeIdx? (qs_le_two w) (e := .right) (by rw [edgeIdx?, lastIdx?_qs, hk]; rfl)

-- (98)
theorem aguacatec_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultSame .right w) (nucleus w (w.length - 1)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  rw [nucleus_of_light hl, hn, Nat.add_sub_cancel, Nat.min_eq_left (Nat.le_succ n)]
  exact mainStressAt_light hw hl (by rw [hn, edgeIdx?, lastIdx?_replicate_one_pos])

theorem lastIdx?_endRule_left {g : Grid} (hg : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2) (hne : g ≠ []) :
    lastIdx? (2 ≤ ·) (endRule .left 2 false g) =
      ((lastIdx? (2 ≤ ·) g.tail).map (· + 1)).or (some 0) := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hx1, hx2⟩ := hg x (List.mem_cons_self ..)
  rcases Nat.lt_or_ge x 2 with hx | hx
  · obtain rfl : x = 1 := by omega
    cases t with
    | nil => simp [endRule_left_singleton le_rfl, lastIdx?_cons]
    | cons y t =>
      obtain ⟨hy1, -⟩ := hg y (by simp)
      rw [endRule_left_two hy1]
      by_cases hy2 : y < 2
      · rw [ite_eq_left (Or.inr hy2)]
        simp [lastIdx?_cons]
      · rw [ite_eq_right (by simpa using hy2)]
        simp [lastIdx?_cons, Nat.not_lt.1 hy2]
  · rw [endRule_left_of_two_le hx]
    simp [lastIdx?_cons, hx]

theorem lastIdx?_endRule_left_of_some {g : Grid} (hg : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2) {p : ℕ}
    (hp : lastIdx? (2 ≤ ·) g = some p) : lastIdx? (2 ≤ ·) (endRule .left 2 false g) = some p := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil (show g ≠ [] by rintro rfl; simp at hp)
  rw [lastIdx?_endRule_left hg (List.cons_ne_nil _ _), List.tail_cons]
  rw [lastIdx?_cons] at hp
  cases h : lastIdx? (2 ≤ ·) t <;> simp_all

-- (98)
theorem cheremis_heavy {w : List Syllable.Weight} {k : ℕ} (hk : lastIdx? (2 ≤ ·) w = some k) :
    MainStressAt (defaultOpposite .right w) (nucleus w k) :=
  mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two w)) (e := .right)
    (lastIdx?_endRule_left_of_some (fun _ ↦ mem_qs) (by rw [lastIdx?_qs, hk]; rfl))

-- (98)
theorem cheremis_light {w : List Syllable.Weight} (hw : w ≠ []) (hl : ∀ m ∈ w, m < 2) :
    MainStressAt (defaultOpposite .right w) 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (List.length_pos_of_ne_nil hw).ne'
  have hq : qs w = List.replicate (n + 1) 1 := by rw [qs_eq_replicate hl, hn]
  have h1 : endRule .left 2 false (qs w) = 2 :: List.replicate n 1 := by
    rw [hq, endRule_left_replicate (Nat.succ_pos n), Nat.succ_sub_one]
  rw [defaultOpposite, opposite, h1]
  refine mainStressAt_of_edgeIdx? (fun x hx ↦ ?_) (e := .right) ?_
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · simp [List.eq_of_mem_replicate hx]
  · rw [edgeIdx?, lastIdx?_cons, lastIdx?_replicate_one]
    rfl

theorem endRule_right_qs (v : List Syllable.Weight) (m : Syllable.Weight) :
    endRule .right 2 false (qs (v ++ [m])) = if 2 ≤ m then qs (v ++ [m]) else qs v ++ [2] := by
  rw [qs_append, qs_singleton]
  split_ifs with hm
  · rw [mora_of_two_le hm, endRule_right_two (Nat.le_succ 1)]
    simp
  · rw [mora_of_lt (Nat.not_le.1 hm)]
    rcases eq_or_ne v [] with rfl | hv
    · simp [qs, endRule_right_singleton]
    · obtain ⟨t, ht⟩ := exists_qs_eq_append_one hv
      rw [ht, List.append_assoc, List.singleton_append, endRule_right_two le_rfl]
      simp

-- (98)
theorem komi_heavy {w : List Syllable.Weight} {k : ℕ} (hk : w.findIdx? (2 ≤ ·) = some k) :
    MainStressAt (defaultOpposite .left w) (nucleus w k) := by
  have h1 : (qs w).findIdx? (2 ≤ ·) = some (nucleus w k) := by rw [findIdx?_qs, hk]; rfl
  have hne : w ≠ [] := by rintro rfl; simp at hk
  obtain ⟨v, m, rfl⟩ := exists_append_singleton hne
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .left) ?_
  rw [edgeIdx?, opposite, endRule_right_qs]
  split_ifs with hm
  · exact h1
  · rw [qs_append, qs_singleton, mora_of_lt (Nat.not_le.1 hm), List.findIdx?_append] at h1
    simp_all [List.findIdx?_append, List.findIdx?_cons]

-- (98)
theorem komi_light {v : List Syllable.Weight} {m : Syllable.Weight}
    (hl : ∀ x ∈ v ++ [m], x < 2) :
    MainStressAt (defaultOpposite .left (v ++ [m])) (nucleus (v ++ [m]) v.length) := by
  have hm : m < 2 := hl m (by simp)
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .left) ?_
  rw [edgeIdx?, opposite, endRule_right_qs, ite_eq_right (Nat.not_le.2 hm), nucleus_append_length,
    qs_eq_replicate fun x hx ↦ hl x (List.mem_append_left _ hx), List.findIdx?_append]
  simp [List.findIdx?_cons, List.findIdx?_replicate]

-- (98)
theorem westGreenlandic (v : List Syllable.Weight) (m : Syllable.Weight) :
    MainStressAt (fixedStress .right false (v ++ [m])) (nucleus (v ++ [m]) v.length) := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .right) ?_
  rw [edgeIdx?, endRule_right_qs, nucleus_append_length]
  split_ifs with hm
  · rw [qs_append, qs_singleton, mora_of_two_le hm, lastIdx?_append]
    simp [lastIdx?_cons]
  · rw [lastIdx?_append]
    simp [lastIdx?_cons]

theorem findIdx?_endRule_left_fco {g : Grid} (hg : ∀ x ∈ g, 1 ≤ x ∧ x ≤ 2) (hne : g ≠ []) :
    (endRule .left 2 true g).findIdx? (2 ≤ ·) = some 0 := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hx1, hx2⟩ := hg x (List.mem_cons_self ..)
  rcases Nat.lt_or_ge x 2 with hx | hx
  · obtain rfl : x = 1 := by omega
    cases t with
    | nil => simp [endRule_left_singleton le_rfl, List.findIdx?_cons]
    | cons y t =>
      rw [endRule_left_two (hg y (by simp)).1, ite_eq_left (Or.inl rfl)]
      simp [List.findIdx?_cons]
  · rw [endRule_left_of_two_le hx]
    simp [List.findIdx?_cons, hx]

-- (98)
theorem koya {w : List Syllable.Weight} (hw : w ≠ []) :
    MainStressAt (fixedStress .left true w) 0 :=
  mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two w))
    (findIdx?_endRule_left_fco (fun _ ↦ mem_qs) (by rwa [Ne, qs_eq_nil_iff]))

-- §3.7
theorem malayalam_first {m : Syllable.Weight} {w : List Syllable.Weight}
    (h : ¬ (m < 2 ∧ ∃ m₁ ∈ w.head?, 2 ≤ m₁)) :
    MainStressAt (fixedStress .left false (m :: w)) 0 := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .left) ?_
  rw [edgeIdx?, qs_cons]
  by_cases hm : 2 ≤ m
  · rw [mora_of_two_le hm, List.cons_append, endRule_left_of_two_le le_rfl]
    simp [List.findIdx?_cons]
  · have hm' : m < 2 := Nat.not_le.1 hm
    rw [mora_of_lt hm', List.singleton_append]
    cases w with
    | nil => simp [qs, endRule_left_singleton le_rfl, List.findIdx?_cons]
    | cons m₁ w =>
      have hm₁ : m₁ < 2 := Nat.not_le.1 fun h₁ ↦ h ⟨hm', m₁, rfl, h₁⟩
      rw [qs_cons, mora_of_lt hm₁, List.singleton_append, endRule_left_two le_rfl,
        ite_eq_left (Or.inr Nat.one_lt_two)]
      simp [List.findIdx?_cons]

theorem malayalam_second {m₀ m₁ : Syllable.Weight} {w : List Syllable.Weight} (h₀ : m₀ < 2)
    (h₁ : 2 ≤ m₁) : MainStressAt (fixedStress .left false (m₀ :: m₁ :: w)) 1 := by
  refine mainStressAt_of_edgeIdx? (endRule_le_two (qs_le_two _)) (e := .left) ?_
  rw [edgeIdx?, qs_cons, qs_cons, mora_of_lt h₀, mora_of_two_le h₁, List.singleton_append,
    List.cons_append, List.cons_append, List.nil_append, endRule_left_two (Nat.le_succ 1),
    ite_eq_right (by simp)]
  simp [List.findIdx?_cons]

end Prince1983
