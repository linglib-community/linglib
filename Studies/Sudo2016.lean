module

public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Fragments.Japanese.Classifiers
public import Studies.Chierchia1998
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Card

/-!
# Sudo (2016): The Semantic Role of Classifiers in Japanese

This file formalizes Sudo's account of why Japanese numerals require classifiers: not the
semantics of nouns, as for Chierchia and Krifka, but the semantics of numerals. Numerals in every
language denote singular terms of type `n`, constant intensions (`numeral`, `numeral_isRigid`),
which cannot modify or predicate on their own. A classifier
turns such a term into a property: a sortal classifier presupposes the plural closure of its
sortal predicate and counts the sortal atoms of its argument (`Sortal.apply`), the paper's
(4) and (8), and a non-atomic classifier such as *-kumi* 'pair' counts non-overlapping
groups of a fixed size (`groupApply`), so that four books form two pairs and never six
(`groupApply_card`, `four_books_two_pairs`, `four_books_not_six_pairs`). Non-classifier
languages reach the same properties through the silent ∪-operator, which maps a numeral to
the property of having that many atomic parts (`up`); by the Blocking Principle its use is
unavailable in a language whose lexicon has overt items with the same function, the
classifiers. The ways a numeral becomes a predicate are therefore the ∪-operator where no
classifier blocks it and an overt classifier otherwise (`PredicateOf`): with classifiers in
the lexicon, as the Japanese fragment has (`japanese_has_classifiers`), every predicate use
of a numeral goes through a classifier and carries its sortal presupposition
(`predicateOf_iff_of_hasClassifiers`), the paper's contrast between the ungrammatical bare
predicative numeral of (15) and its classifier-suffixed counterpart (16). The inverse
∩-operator maps a property of having a fixed number of atoms back to its numeral (`IsDown`,
`isDown_up`), has no overt counterpart and so is available in Japanese, where it returns
the type-`n` correlate of a numeral-plus-classifier phrase (`isDown_sortal`), the paper's
(22) to (25). The blocking premise, that the Japanese lexicon has classifiers, is the fact
Chierchia's typology records for Japanese, so the two accounts share their premise and
part over what the classifier serves, the kind-denoting noun there and the type-`n` numeral
here (`predicateOf_iff_japanese`).

## Implementation notes

Type `n` is `ℕ`, and the paper's extension of the type-`n` domain to the correlates of
classifier phrases is represented by stating ∩ relative to the classifier's sortal. The
∪-shifted composition rules (11), (19) and (26) are represented by the derivation relation
`PredicateOf` rather than as rules with domain conditions, and the paper's observation that
English numerals fail in some predicative constructions is not modelled. The witnesses use
the set-based ontology of the plural algebra, an individual being its singleton and sum
union, on which the atom count of a plurality is its cardinality (`atomCount_finset`).

## References

* [sudo-2016]
* [chierchia-1998]
* [rothstein-2013]
* [link-1983]
* [heim-kratzer-1998]
* [krifka-2008]
-/

@[expose] public section

namespace Sudo2016

open Mereology

section General

variable {W E : Type*} [SemilatticeSup E]

/-! ### Numerals and classifiers -/

/-- A numeral denotes a singular term of type `n`, the constant intension of the paper's (2). -/
def numeral (n : ℕ) : W → ℕ := fun _ ↦ n

theorem numeral_isRigid (n : ℕ) : IsRigid (numeral (W := W) n) :=
  isRigid_const n

/-- The number of atomic `P`-parts of `x` at a world. -/
noncomputable def atomCount (P : W → E → Prop) (w : W) (x : E) : ℕ := {y | y ≤ x ∧ P w y}.ncard

/-- A sortal predicate of atoms, indexed by worlds, such as the metalanguage predicates *flower*
and *human* of the paper's (4) and (8). -/
abbrev Sortal (W E : Type*) := W → E → Prop

/-- A sortal classifier applied to a numeral, the paper's (4) and (7b), is at each world a
trivalent property presupposing the plural closure of the sortal and asserting that the
argument has the numeral's number of sortal atoms. -/
noncomputable def Sortal.apply (c : Sortal W E) (n : W → ℕ) (w : W) : E → SignType :=
  {x | AlgClosure (c w) x}.indicator fun x ↦ SignType.ofProp (atomCount c w x = n w)

/-- The ∪-operator of the paper's (10) maps a numeral to its property correlate, having that
many atomic parts. -/
def up (atomic : Sortal W E) (n : W → ℕ) : W → E → Prop := fun w x ↦ atomCount atomic w x = n w

@[simp] theorem Sortal.apply_eq_zero_iff {c : Sortal W E} {n : W → ℕ} {w : W} {x : E} :
    c.apply n w x = 0 ↔ ¬ AlgClosure (c w) x := by
  simp [Sortal.apply]

@[simp] theorem Sortal.apply_eq_one_iff {c : Sortal W E} {n : W → ℕ} {w : W} {x : E} :
    c.apply n w x = 1 ↔ AlgClosure (c w) x ∧ up c n w x := by
  simp [Sortal.apply, up]

@[simp] theorem Sortal.apply_eq_neg_one_iff {c : Sortal W E} {n : W → ℕ} {w : W} {x : E} :
    c.apply n w x = -1 ↔ AlgClosure (c w) x ∧ ¬ up c n w x := by
  simp [Sortal.apply, up]

open Classical in
/-- Predicate Modification with a presupposed modifier, the paper's (6), conjoins the noun
with the assertion and projects the presupposition. -/
noncomputable def modify (P : E → SignType) (N : E → Prop) : E → SignType :=
  fun x ↦ (P x).meetWeak (SignType.ofProp (N x))

-- (7c)
theorem modify_sortal_ne_zero (c : Sortal W E) (n : W → ℕ) (w : W) {x : E}
    (h : AlgClosure (c w) x) : modify (c.apply n w) (AlgClosure (c w)) x ≠ 0 := by
  simp [modify, h]

/-! ### The ∩-operator -/

/-- The property `P` is the ∪-correlate of the numeral `n`, so that ∩ maps it back to `n`, the
paper's (24). -/
def IsDown (atomic : Sortal W E) (P : W → E → Prop) (n : W → ℕ) : Prop :=
  ∀ w x, P w x ↔ atomCount atomic w x = n w

theorem isDown_up (atomic : Sortal W E) (n : W → ℕ) : IsDown atomic (up atomic n) n :=
  fun _ _ ↦ Iff.rfl

theorem IsDown.unique {atomic : Sortal W E} {P : W → E → Prop} {n m : W → ℕ}
    (hn : IsDown atomic P n) (hm : IsDown atomic P m)
    (hsurj : ∀ w, ∃ x, atomCount atomic w x = n w) : n = m := by
  funext w
  obtain ⟨x, hx⟩ := hsurj w
  exact hx.symm.trans ((hm w x).mp ((hn w x).mpr hx))

/-- On the plural closure of its sortal, a numeral-classifier phrase holds of exactly the sums with
the numeral's number of atoms (25). -/
theorem isDown_sortal (c : Sortal W E) (n : W → ℕ) :
    ∀ w x, AlgClosure (c w) x → (c.apply n w x = 1 ↔ atomCount c w x = n w) :=
  fun _ _ hx ↦ by simp [hx, up]

/-! ### Blocking -/

/-- A numeral becomes a predicate by the silent ∪-operator, available only when no overt
classifier is in the lexicon, or by an overt classifier, which adds its sortal
presupposition. -/
inductive PredicateOf (hasClassifiers : Prop) (atomic : Sortal W E) (n : W → ℕ) :
    (W → E → Prop) → Prop
  | up (h : ¬ hasClassifiers) : PredicateOf hasClassifiers atomic n (up atomic n)
  | classifier (c : Sortal W E) :
      PredicateOf hasClassifiers atomic n
        fun w x ↦ c.apply n w x = 1

/-- With classifiers in the lexicon, every predicate use of a numeral goes through a classifier and
its sortal presupposition ((15), (16)). -/
theorem predicateOf_iff_of_hasClassifiers {hasClassifiers : Prop} (h : hasClassifiers)
    (atomic : Sortal W E) (n : W → ℕ) (P : W → E → Prop) :
    PredicateOf hasClassifiers atomic n P ↔
      ∃ c : Sortal W E, P = fun w x ↦ c.apply n w x = 1 := by
  constructor
  · rintro (⟨hno⟩ | ⟨c⟩)
    · exact absurd h hno
    · exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact .classifier c

-- (18)
theorem predicateOf_up (atomic : Sortal W E) (n : W → ℕ) :
    PredicateOf False atomic n (up atomic n) :=
  .up id

end General

theorem japanese_has_classifiers : Chierchia1998.Language.HasClassifiers .japanese :=
  (Chierchia1998.hasClassifiers_iff .japanese).2 rfl

theorem predicateOf_iff_japanese {W E : Type*} [SemilatticeSup E] (atomic : Sortal W E)
    (n : W → ℕ) (P : W → E → Prop) :
    PredicateOf (Chierchia1998.Language.HasClassifiers .japanese) atomic n P ↔
      ∃ c : Sortal W E, P = fun w x ↦ c.apply n w x = 1 :=
  predicateOf_iff_of_hasClassifiers japanese_has_classifiers atomic n P

/-! ### Witnesses on the set-based ontology -/

section Model

variable {α : Type*} [DecidableEq α]

/-- The sortal predicate `P` of atoms lifted to pluralities, an individual being its singleton. -/
def singletonSortal (P : α → Prop) : Sortal Unit (Finset α) :=
  fun _ y ↦ ∃ a, y = {a} ∧ P a

theorem atomCount_finset (P : α → Prop) [DecidablePred P] (x : Finset α) :
    atomCount (singletonSortal P) () x = (x.filter P).card := by
  have : {y : Finset α | y ≤ x ∧ singletonSortal P () y} =
      ↑((x.filter P).image ({·} : α → Finset α)) := by
    ext y
    simp only [Set.mem_ofPred_eq, singletonSortal, Finset.coe_image, Finset.coe_filter,
      Set.mem_image]
    constructor
    · rintro ⟨hle, a, rfl, hP⟩
      exact ⟨a, ⟨Finset.singleton_subset_iff.mp hle, hP⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hP⟩, rfl⟩
      exact ⟨Finset.singleton_subset_iff.mpr ha, a, rfl, hP⟩
  rw [atomCount, this, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ Finset.singleton_injective]

theorem singletonSortal_apply_ne_zero_iff (P : α → Prop) (n : Unit → ℕ) (x : Finset α) :
    (singletonSortal P).apply n () x ≠ 0 ↔ x.Nonempty ∧ ∀ a ∈ x, P a := by
  rw [Ne, Sortal.apply_eq_zero_iff, not_not,
    algClosure_iff_of_subset_range_singleton fun y hy ↦ by
    obtain ⟨a, hy, _⟩ := hy; exact ⟨a, hy.symm⟩]
  simp [singletonSortal]

/-- A non-atomic classifier counting groups of `k` atoms, the paper's (9), holds when the
argument is the sum of `n` non-overlapping pluralities of `k` members each. -/
def groupApply (k n : ℕ) (x : Finset α) : Prop :=
  ∃ s : Finset (Finset α), s.card = n ∧ s.biUnion id = x ∧ (∀ y ∈ s, y.card = k) ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → Disjoint y z

theorem groupApply_card {k n : ℕ} {x : Finset α} (h : groupApply k n x) : x.card = n * k := by
  obtain ⟨s, hs, rfl, hk, hd⟩ := h
  rw [Finset.card_biUnion (t := id) hd]
  simp only [id_eq]
  rw [Finset.sum_congr rfl fun y hy ↦ hk y hy, Finset.sum_const, hs]
  rfl

/-- The individuals of the witnesses are three flowers, two humans, and four books. -/
inductive Ind
  | f1 | f2 | f3 | h1 | h2 | b1 | b2 | b3 | b4
  deriving DecidableEq, Repr

def Ind.flower : Ind → Prop
  | .f1 | .f2 | .f3 => True
  | _ => False

instance : DecidablePred Ind.flower := fun a ↦ by cases a <;> unfold Ind.flower <;> infer_instance

/-- *-rin* counts flowers. -/
def rin : Sortal Unit (Finset Ind) := singletonSortal Ind.flower

theorem rin_three :
    rin.apply (numeral 3) () {.f1, .f2, .f3} = 1 ∧ rin.apply (numeral 3) () {.f1, .f2} = -1 := by
  have h x := singletonSortal_apply_ne_zero_iff Ind.flower (numeral 3) x
  simp only [ne_eq, Sortal.apply_eq_zero_iff, not_not] at h
  refine ⟨Sortal.apply_eq_one_iff.2 ⟨(h _).2 (by decide), ?_⟩,
    Sortal.apply_eq_neg_one_iff.2 ⟨(h _).2 (by decide), ?_⟩⟩ <;>
    simp only [up, rin, atomCount_finset, numeral] <;> decide

theorem rin_not_human : rin.apply (numeral 1) () {.h1} = 0 := by
  rw [← not_ne_iff, rin, singletonSortal_apply_ne_zero_iff]; decide

/-- Four books form two pairs, the paper's remark on (9). -/
theorem four_books_two_pairs : groupApply 2 2 ({.b1, .b2, .b3, .b4} : Finset Ind) :=
  ⟨{{.b1, .b2}, {.b3, .b4}}, by decide, by decide, by decide, by decide⟩

theorem four_books_not_six_pairs (x : Finset Ind) (hx : x.card = 4) : ¬ groupApply 2 6 x :=
  fun h ↦ by have := groupApply_card h; omega

end Model

end Sudo2016
