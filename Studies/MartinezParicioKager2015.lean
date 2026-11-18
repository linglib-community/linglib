module

public import Linglib.Core.Computability.Edge
public import Linglib.Phonology.Prosody.Foot
public import Linglib.Phonology.Prosody.Word
public import Linglib.Phonology.OptimalityTheory.Filtration

/-!
# Martínez-Paricio and Kager (2015): The Binary-to-Ternary Rhythmic Continuum

[martinez-paricio-kager-2015] derive ternary rhythm from a foot with one layer of recursion: a
weak syllable adjoined to a binary foot. A candidate is a metrical tree whose word node dominates
maximal feet and unfooted syllables, and every constraint on the distribution of feet is a
categorical alignment in the non-intervention format of [mccarthy-2003], which a candidate
violates [at most once for each locus](##MartinezParicioKager2015.intervened_le_countP). Over
every parsing of an eight-syllable word, the ranking for Cayuvava selects
[two ternary feet and two unfooted syllables](##MartinezParicioKager2015.cayuvava_optimum), the
ranking for Chugach and Estonian [closes the word with a binary
foot](##MartinezParicioKager2015.chugach_optimum), and the ranking for Garawa gives [binary feet,
with one ternary foot in odd parity](##MartinezParicioKager2015.garawa_optimum).

## Implementation notes

* Candidates are `Prosody.MetricalTree`s with every weight zero, since the systems are
  quantity-insensitive. A strong syllable is a foot head; a strong foot under a foot is the
  minimal foot of a layered one, and a strong foot under the word carries primary stress.
* A layered foot is a foot node over a foot and a syllable, well formed under
  `Prosody.IsFoot`, which admits a foot under a foot as `Prosody.IsWord` admits the recursive
  word of [ito-mester-2009].
* The projections are read as the paper defines them, from a node's mother and daughters: a foot
  is non-minimal when a daughter of it is a foot, and the feet the word immediately dominates
  are the maximal ones.
* `gen` lists the parsings of a word into unfooted syllables and unary, binary and ternary feet
  with heads foot-initial and the adjunct on the right, the abstraction over headedness and
  primary stress under which the paper prints its tableaux. The rankings accordingly leave out
  the constraints on foot form and on the head foot. A candidate has at least one foot, as the
  paper's candidates have exactly one head foot; a word without feet
  [violates no constraint on the word](##MartinezParicioKager2015.alignWord_of_forall_not_isFt).

## TODO

* The paper's count of seven maximal feet under its three restrictions on GEN is not derived;
  `feet` lists the seven.
* The factorial typology over all sixteen constraints, 316 patterns in the paper's computation,
  is not reproduced.

## References

* [martinez-paricio-kager-2015]
* [mccarthy-2003]
* [ito-mester-2009]
-/

@[expose] public section

namespace MartinezParicioKager2015

open Prosody OptimalityTheory

/-! ### Non-intervention alignment -/

section Intervention

variable {α : Type*} (locus sep : α → Prop) [DecidablePred locus] [DecidablePred sep]

/-- The members of a list that are loci with a separator somewhere after them. -/
def intervenedAfter : List α → ℕ
  | [] => 0
  | x :: l => (if locus x ∧ ∃ y ∈ l, sep y then 1 else 0) + intervenedAfter l

/-- (7): the non-intervention schema Align-L/R(Cat₁, Cat₂, Cat₃) over the daughters of a Cat₃
node, one violation for each locus that some separator lies between it and the edge `e`. -/
def intervened (e : Edge) (l : List α) : ℕ := intervenedAfter locus sep (e.swap.orient l)

variable {locus sep} in
theorem intervenedAfter_eq_zero {l : List α} (h : ∀ y ∈ l, ¬sep y) :
    intervenedAfter locus sep l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [intervenedAfter, ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy), ite_eq_right]
    exact fun ⟨_, y, hy, hs⟩ ↦ h y (List.mem_cons_of_mem _ hy) hs

theorem intervenedAfter_le_countP (l : List α) :
    intervenedAfter locus sep l ≤ l.countP fun x ↦ locus x := by
  induction l with
  | nil => simp [intervenedAfter]
  | cons x l ih =>
    rw [intervenedAfter, List.countP_cons]
    split_ifs with h h' <;> simp_all <;> omega

/-- A non-intervention constraint assigns no more violations than there are loci, whatever the
number of separators. -/
theorem intervened_le_countP (e : Edge) (l : List α) :
    intervened locus sep e l ≤ l.countP fun x ↦ locus x := by
  cases e
  · simpa [intervened, Edge.swap] using intervenedAfter_le_countP locus sep l.reverse
  · simpa [intervened, Edge.swap] using intervenedAfter_le_countP locus sep l

end Intervention

/-! ### Foot projections -/

/-- A foot node. -/
abbrev IsFt (t : MetricalTree) : Prop := t.value.level = .ft

/-- A syllable node. -/
abbrev IsSyl (t : MetricalTree) : Prop := t.value.level = .syl

/-- (3): a non-minimal foot dominates a foot. -/
abbrev IsNonMinimal (t : MetricalTree) : Prop := IsFt t ∧ ∃ c ∈ t.children, IsFt c

/-- (3): a minimal foot dominates no foot. -/
abbrev IsMinimal (t : MetricalTree) : Prop := IsFt t ∧ ∀ c ∈ t.children, ¬IsFt c

/-- A unary foot. -/
abbrev IsUnary (t : MetricalTree) : Prop := IsFt t ∧ t.children.length = 1

/-- The head foot of its word. -/
abbrev IsMain (t : MetricalTree) : Prop := IsFt t ∧ t.value.isHead

/-- A foot head, a strong syllable. -/
abbrev IsFootHead (t : MetricalTree) : Prop := IsSyl t ∧ t.value.isHead

/-! ### The constraints -/

/-- The constraints of (11) share the word as domain and the foot as separator: the locus is a
kind of daughter of the word. -/
def alignWord (locus : MetricalTree → Prop) [DecidablePred locus] (e : Edge) :
    Constraint MetricalTree := fun t ↦ intervened locus IsFt e t.children

-- A word without feet has no separators, so it satisfies every constraint of (11).
theorem alignWord_of_forall_not_isFt (locus : MetricalTree → Prop) [DecidablePred locus]
    (e : Edge) {t : MetricalTree} (h : ∀ c ∈ t.children, ¬IsFt c) : alignWord locus e t = 0 :=
  intervenedAfter_eq_zero fun y hy ↦ h y (by cases e <;> simpa [Edge.swap] using hy)

/-- (11a): Align-L/R([Ft-max]ω, Ft, ω). -/
def alignMax : Edge → Constraint MetricalTree := alignWord IsFt

/-- (11b): Align-L/R([Ft-min]ω, Ft, ω), whose locus is a foot both minimal and maximal. -/
def alignMin : Edge → Constraint MetricalTree := alignWord IsMinimal

/-- (11c): Align-L/R([Ft-non-min]ω, Ft, ω). -/
def alignNonMin : Edge → Constraint MetricalTree := alignWord IsNonMinimal

/-- (11d): Align-L/R([Ft-unary]ω, Ft, ω). -/
def alignUnary : Edge → Constraint MetricalTree := alignWord IsUnary

/-- (11e): Align-L/R([Ft-main]ω, Ft, ω). -/
def alignMain : Edge → Constraint MetricalTree := alignWord IsMain

/-- (11f): Chain-L/R, Align-L/R([σ]ω, Ft, ω), whose locus is an unfooted syllable. -/
def chain : Edge → Constraint MetricalTree := alignWord IsSyl

/-- The feet of a tree at every depth. -/
def footNodes (t : MetricalTree) : List MetricalTree := t.subtrees.filter fun s ↦ IsFt s

/-- (18a): Trochee, one violation for each foot head that is not initial in its foot. -/
def trochee : Constraint MetricalTree := fun t ↦
  ((footNodes t).map fun f ↦ f.children.tail.countP fun c ↦ IsFootHead c).sum

/-- (18b): Iamb, one violation for each foot head that is initial in its foot. -/
def iamb : Constraint MetricalTree := fun t ↦
  ((footNodes t).map fun f ↦ (f.children.take 1).countP fun c ↦ IsFootHead c).sum

/-- (18c): Align-L/R(Ft-min, σ, Ft-non-min), Trochee-non-min on the left and Iamb-non-min on the
right: one violation for each minimal foot that a syllable separates from the edge of the foot
containing it. -/
def alignAdjunct (e : Edge) : Constraint MetricalTree := fun t ↦
  ((footNodes t).map fun f ↦ intervened IsMinimal IsSyl e f.children).sum

/-! ### Feet -/

/-- A layered foot: a weak syllable adjoined at the edge `e` of a foot, which heads the result. -/
def adjoin (e : Edge) (f : Foot ℕ) (main : Bool := false) : MetricalTree :=
  .ft main (e.orient [.σ, f.toProsTree id true])

/-- (6): the seven maximal feet, four layered, two binary and one unary. -/
def feet : List MetricalTree :=
  [adjoin .right (.trochee 0 0), adjoin .right (.iamb 0 0), adjoin .left (.trochee 0 0),
    adjoin .left (.iamb 0 0), (Foot.trochee 0 0).toProsTree id, (Foot.iamb 0 0).toProsTree id,
    (Foot.monosyllable 0).toProsTree id]

-- (5b): each of the seven is a well-formed foot with at most one layer of recursion.
theorem isFoot_feet : ∀ f ∈ feet,
    IsFoot f ∧ nonrecursivity .ft f = if IsNonMinimal f then 1 else 0 := by
  decide

-- (19)
theorem trochee_add_iamb : ∀ f ∈ feet, trochee f + iamb f = 1 := by decide

-- (19)
theorem footForm_marks (e : Edge) :
    trochee (adjoin e (.trochee 0 0)) = 0 ∧ trochee (adjoin e (.iamb 0 0)) = 1 ∧
      iamb ((Foot.monosyllable 0).toProsTree id) = 1 := by
  cases e <;> decide

-- (19)
theorem alignAdjunct_adjoin (e : Edge) (f : Foot ℕ) (hf : f = .trochee 0 0 ∨ f = .iamb 0 0) :
    alignAdjunct e (adjoin e f) = 1 ∧ alignAdjunct e.swap (adjoin e f) = 0 := by
  rcases hf with rfl | rfl <;> cases e <;> decide

-- (19)
theorem alignAdjunct_minimal : ∀ f ∈ feet, IsMinimal f → ∀ e, alignAdjunct e f = 0 := by
  decide

/-! ### Words -/

/-- A unary foot `(σ́)`. -/
def una : MetricalTree := (Foot.monosyllable 0).toProsTree id

/-- A binary foot `(σ́σ)`. -/
def bin : MetricalTree := (Foot.trochee 0 0).toProsTree id

/-- A ternary foot `((σ́σ)σ)`. -/
def ter : MetricalTree := adjoin .right (.trochee 0 0)

/-- A word over feet and unfooted syllables. -/
def word (ds : List MetricalTree) : MetricalTree := .om false ds

/-- The parsings of `n` syllables into unfooted syllables and unary, binary and ternary feet. -/
def gen : ℕ → List (List MetricalTree)
  | 0 => [[]]
  | 1 => [[.σ], [una]]
  | 2 => [[.σ, .σ], [.σ, una], [una, .σ], [una, una], [bin]]
  | n + 3 => (gen (n + 2)).flatMap (fun w ↦ [.σ :: w, una :: w]) ++
      (gen (n + 1)).map (bin :: ·) ++ (gen n).map (ter :: ·)

example : IsWord (word [ter, ter, .σ, .σ]) ∧ noRec (word [ter, ter, .σ, .σ]) = 2 := by decide

-- (9)
theorem alignMax_left :
    [word [bin, bin, bin], word [ter, ter], word [bin, .σ, .σ, .σ, .σ]].map (alignMax .left) =
      [2, 1, 0] := by
  decide

-- (17)
theorem alignUnary_marks :
    [word [bin, bin, bin, una], word [bin, una, bin, bin], word [una, bin, bin, bin],
        word [una, .σ, una, bin, bin]].map (fun w ↦ (alignUnary .right w, alignUnary .left w)) =
      [(0, 1), (1, 1), (1, 0), (2, 1)] := by
  decide

-- (16a.ii)
theorem alignNonMin_marks :
    (alignNonMin .left (word [ter, ter, bin]), alignNonMin .right (word [ter, ter, bin]),
        alignMin .left (word [ter, ter, bin]), alignMin .right (word [ter, ter, bin])) =
      (1, 2, 1, 0) := by
  decide

/-! ### Optima over every parsing -/

/-- The candidates for a word of `n` syllables: its parsings with at least one foot. -/
def candidates (n : ℕ) : Finset MetricalTree :=
  (((gen n).filter fun w ↦ ∃ f ∈ w, IsFt f).map word).toFinset

private theorem eval_candidates {n : ℕ} {Fs : List (Constraint MetricalTree)}
    {w : List MetricalTree} (hw : w ∈ (gen n).filter fun w ↦ ∃ f ∈ w, IsFt f)
    (h : ∀ v ∈ gen n, (∃ f ∈ v, IsFt f) → v ≠ w →
      Fs.map (· (word w)) < Fs.map (· (word v))) :
    Constraint.eval (candidates n) Fs = {word w} := by
  refine Constraint.eval_eq_singleton_iff.2
    ⟨List.mem_toFinset.2 (List.mem_map.2 ⟨w, hw, rfl⟩), fun d hd hne ↦ ?_⟩
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hd)
  obtain ⟨hv, hf⟩ := List.mem_filter.1 hv
  exact h v hv (of_decide_eq_true hf) fun e ↦ hne (e ▸ rfl)

/-- (32): the ranking for Cayuvava, Chain-R and the alignment of non-recursive and unary feet
over Chain-L. -/
def cayuvava : List (Constraint MetricalTree) :=
  [chain .right, alignMin .left, alignMin .right, alignUnary .left, alignUnary .right,
    chain .left, alignMax .left, alignMax .right, alignNonMin .left, alignNonMin .right]

/-- (30a): the ranking for Chugach and Estonian, both Chain constraints on top and Align-R-min
over Align-L-min. -/
def chugach : List (Constraint MetricalTree) :=
  [chain .left, chain .right, alignUnary .left, alignUnary .right, alignMax .left,
    alignMax .right, alignMin .right, alignNonMin .left, alignNonMin .right, alignMin .left]

/-- (27a): the ranking for Garawa, both Chain constraints and Align-L-non-min on top. -/
def garawa : List (Constraint MetricalTree) :=
  [chain .left, chain .right, alignNonMin .left, alignUnary .left, alignUnary .right,
    alignMax .left, alignMax .right, alignNonMin .right, alignMin .left, alignMin .right]

/-- (14): under the ranking for Cayuvava an eight-syllable word is parsed into two ternary feet
and two unfooted syllables at the right edge, strict ternarity at the cost of exhaustivity. -/
theorem cayuvava_optimum :
    Constraint.eval (candidates 8) cayuvava = {word [ter, ter, .σ, .σ]} :=
  eval_candidates (by decide +kernel) (by decide +kernel)

/-- (15): under the ranking for Chugach and Estonian the parse is exhaustive, and the two
syllables that ternary feet leave over form a binary foot. -/
theorem chugach_optimum :
    Constraint.eval (candidates 8) chugach = {word [ter, ter, bin]} :=
  eval_candidates (by decide +kernel) (by decide +kernel)

/-- (16): under the ranking for Garawa an even-parity word is parsed into binary feet, and an
odd-parity word takes a single ternary foot at the left edge. -/
theorem garawa_optimum :
    Constraint.eval (candidates 8) garawa = {word [bin, bin, bin, bin]} ∧
      Constraint.eval (candidates 7) garawa = {word [ter, bin, bin]} :=
  ⟨eval_candidates (by decide +kernel) (by decide +kernel),
    eval_candidates (by decide +kernel) (by decide +kernel)⟩

end MartinezParicioKager2015
