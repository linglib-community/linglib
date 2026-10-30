module

public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Logic.Aristotelian.Square
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Data.Examples.Belnap1970

/-!
# Belnap (1970): Conditional Assertion and Restricted Quantification

Belnap reads "if p then q" as a *conditional assertion*, the assertion of q on the condition p,
which is assertive only where p is true and is as if never made elsewhere. At a world a sentence
is true, false or nonassertive (p. 3), and so has a trivalent value. Combining conditional
assertion (3) with universal quantification (10) derives restricted quantification (11): "All
crows are black" becomes "Consider the crows: each one is black", assertive only if there are
crows.

## Implementation notes

The conditional assertion `(A/B)` of (3) is the indicator
`{w | A w}.indicator fun w ↦ SignType.ofProp (B w)`, a categorical atom (6) is
`fun w ↦ SignType.ofProp (A w)`, negation (7) is `-`, which preserves assertiveness, conjunction
(8) and disjunction (9) are `SignType.meetBelnap` and `SignType.joinBelnap`, assertive iff some
operand is, and the quantifiers (10) are `Trivalent.forallHaug` and `Trivalent.existsHaug`. The
restricted forms are evaluated in a single model, where what a sentence asserts is represented by
its truth value, so the propositional implication between contents that Belnap appeals to is read
as implication between truth values.

## References

* [belnap-1970]
* [quine-1950]
* [strawson-1952]
-/

@[expose] public section

namespace Belnap1970

open Aristotelian (Square SquareRelations)
open Quantifier Quantifier.Det

variable {E : Type}

open Classical in
/-- Restricted universal quantification ∀x(Cx/Bx) (11) is the universal quantifier (10) over the
conditional assertions (Cx/Bx) (3), the A-form *All crows are black* read as a claim about each
crow. -/
noncomputable def restrictedForall (C B : Set E) : SignType :=
  Trivalent.forallHaug (C.indicator fun x ↦ SignType.ofProp (x ∈ B))

open Classical in
/-- Restricted existential quantification ∃x(Cx/Bx) (12) is the existential quantifier (10) over
the conditional assertions (Cx/Bx) (3). -/
noncomputable def restrictedExists (C B : Set E) : SignType :=
  Trivalent.existsHaug (C.indicator fun x ↦ SignType.ofProp (x ∈ B))

variable {C B : Set E}

/-! ### Assertiveness and content -/

/-- ∀x(Cx/Bx) is nonassertive exactly when nothing satisfies `C`. This is the existential
presupposition of universals, which Strawson stipulated and Belnap derives ((11), (12)). -/
@[simp] theorem restrictedForall_eq_zero_iff : restrictedForall C B = 0 ↔ ∀ x, x ∉ C := by
  simp [restrictedForall]

@[simp] theorem restrictedForall_eq_one_iff :
    restrictedForall C B = 1 ↔ (∃ x, x ∈ C) ∧ every C B := by
  simp [restrictedForall, every, Set.subset_def]

@[simp] theorem restrictedForall_eq_neg_one_iff : restrictedForall C B = -1 ↔ ¬ every C B := by
  simp [restrictedForall, every, Set.subset_def]

@[simp] theorem restrictedExists_eq_zero_iff : restrictedExists C B = 0 ↔ ∀ x, x ∉ C := by
  simp [restrictedExists]

/-- ∃x(Cx/Bx) is true exactly when something satisfies both `C` and `B`, so what (12) asserts,
when assertive, is exactly `Det.some`. -/
@[simp] theorem restrictedExists_eq_one_iff : restrictedExists C B = 1 ↔ Det.some C B := by
  simp [restrictedExists, Det.some, Set.Nonempty]

@[simp] theorem restrictedExists_eq_neg_one_iff :
    restrictedExists C B = -1 ↔ (∃ x, x ∈ C) ∧ ¬ Det.some C B := by
  simp [restrictedExists, Det.some, Set.Nonempty]

/-- What (11) asserts, when assertive, is exactly `every`. -/
theorem belnap_forall_content_eq_every (h : restrictedForall C B ≠ 0) :
    restrictedForall C B = 1 ↔ every C B := by
  simp_all

/-! ### The square of opposition -/

/-- The four Aristotelian forms as restricted quantifications make up a square, since "semantic
relations between these forms turn out ... to constitute what is pretty much a good old
fashioned square of opposition" (p. 8). -/
noncomputable def belnapSquare (C B : Set E) : Square SignType where
  A := restrictedForall C B
  E := restrictedForall C Bᶜ
  I := restrictedExists C B
  O := restrictedExists C Bᶜ

-- p. 8
theorem square_equiassertive :
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).E = 0) ∧
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).I = 0) ∧
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).O = 0) := by
  simp [belnapSquare]

/-- Abstracting over the scope, the truth conditions of the four forms make up a square in the
Boolean algebra `Quantifier E`. -/
def contentSquare (C : Set E) : Square (Quantifier E) where
  A B := (belnapSquare C B).A = 1
  E B := (belnapSquare C B).E = 1
  I B := (belnapSquare C B).I = 1
  O B := (belnapSquare C B).O = 1

/-- Where the forms are assertive, a form is true exactly when what it asserts is, and the
content square is the square of `every`, `no`, `some` and `not every` at the restrictor `C`. -/
theorem contentSquare_eq_square (hC : ∃ x, x ∈ C) : contentSquare C = Det.square C := by
  simp only [contentSquare, Det.square, Square.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext B <;>
    simp [belnapSquare, hC, every, no, Det.some, Set.Nonempty, Set.not_subset]

/-- The content square satisfies `SquareRelations` when the restrictor is non-empty, which is
Belnap's assertiveness condition, so the relations hold exactly where the forms are
assertive. -/
theorem content_square_relations (hR : ∃ x, x ∈ C) :
    SquareRelations (contentSquare C) :=
  contentSquare_eq_square hR ▸ Det.square_relations hR

/-! ### Obversion, I-conversion, Barbara -/

-- p. 8
theorem obversion : restrictedForall C Bᶜᶜ = restrictedForall C B := by
  rw [compl_compl]

/-- I-conversion is equitrue, in that "truth is preserved in passing from one to the other"
(p. 8), although "their propositional contents are unrelated". -/
theorem i_conversion_equitrue : restrictedExists C B = 1 ↔ restrictedExists B C = 1 := by
  rw [restrictedExists_eq_one_iff, restrictedExists_eq_one_iff, Det.some, Det.some, Set.inter_comm]

/-- I-conversion is not equi-assertive in any nonempty domain (p. 8). -/
theorem i_conversion_not_equiassertive [Nonempty E] :
    ∃ C B : Set E, restrictedExists C B ≠ 0 ∧ restrictedExists B C = 0 :=
  ⟨Set.univ, ∅, by simp, by simp⟩

-- p. 9
theorem barbara_assertive (A C B : Set E) (hMinor : restrictedForall A C = 1) :
    restrictedForall C B ≠ 0 ∧ restrictedForall A B ≠ 0 := by
  simp only [restrictedForall_eq_one_iff, every] at hMinor
  obtain ⟨⟨x, hAx⟩, hAC⟩ := hMinor
  simpa using ⟨⟨x, hAC hAx⟩, ⟨x, hAx⟩⟩

/-- When Barbara's minor is true, her major implies her conclusion (p. 9). -/
theorem barbara (A C B : Set E) (hMinor : restrictedForall A C = 1) :
    restrictedForall C B = 1 → restrictedForall A B = 1 := by
  simp only [restrictedForall_eq_one_iff, every] at hMinor ⊢
  exact fun ⟨_, hCB⟩ ↦ ⟨hMinor.1, hMinor.2.trans hCB⟩

/-! ### Contraposition and confirmation (§6) -/

-- p. 10
theorem contrapositive_different_assertiveness :
    (restrictedForall C B ≠ 0 ↔ ∃ x, x ∈ C) ∧ (restrictedForall Bᶜ Cᶜ ≠ 0 ↔ ∃ x, x ∉ B) := by
  simp

end Belnap1970
