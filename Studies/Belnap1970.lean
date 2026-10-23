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

## Main statements

* `restrictedForall_eq_zero_iff`: the restricted forms (11)–(12) are nonassertive exactly when
  nothing satisfies the restrictor, which is Strawson's existential presupposition, here derived
  rather than stipulated.
* `belnap_forall_content_eq_every`, `restrictedExists_eq_one_iff`: when assertive, the restricted
  forms assert `every` and `GQ.some`.
* `contentSquare_eq_square`, `content_square_relations`: where the forms are assertive their
  contents are the quantifier square at the restrictor, so they stand in all six relations of the
  square.
* `i_conversion_equitrue`, `i_conversion_not_equiassertive`, `barbara`: conversion preserves
  truth but not assertiveness, and Barbara's major does all the implying (pp. 8–9).

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
open Quantifier Quantifier.GQ Quantifier.NP

variable {E : Type}

open Classical in
/-- Restricted universal quantification ∀x(Cx/Bx) (11) is the universal quantifier (10) over the
conditional assertions (Cx/Bx) (3), the A-form *All crows are black* read as a claim about each
crow. -/
noncomputable def restrictedForall (C B : E → Prop) : SignType :=
  Trivalent.forallHaug ({x | C x}.indicator fun x ↦ SignType.ofProp (B x))

open Classical in
/-- Restricted existential quantification ∃x(Cx/Bx) (12) is the existential quantifier (10) over
the conditional assertions (Cx/Bx) (3). -/
noncomputable def restrictedExists (C B : E → Prop) : SignType :=
  Trivalent.existsHaug ({x | C x}.indicator fun x ↦ SignType.ofProp (B x))

variable {C B : E → Prop}

/-! ### Assertiveness and content -/

@[simp] theorem restrictedForall_eq_zero_iff : restrictedForall C B = 0 ↔ ∀ x, ¬ C x := by
  simp [restrictedForall]

@[simp] theorem restrictedForall_eq_one_iff :
    restrictedForall C B = 1 ↔ (∃ x, C x) ∧ every C B := by
  simp [restrictedForall, every]

@[simp] theorem restrictedForall_eq_neg_one_iff : restrictedForall C B = -1 ↔ ¬ every C B := by
  simp [restrictedForall, every]

@[simp] theorem restrictedExists_eq_zero_iff : restrictedExists C B = 0 ↔ ∀ x, ¬ C x := by
  simp [restrictedExists]

/-- ∃x(Cx/Bx) is true exactly when something satisfies both `C` and `B`, so what (12) asserts,
when assertive, is exactly `GQ.some`. -/
@[simp] theorem restrictedExists_eq_one_iff : restrictedExists C B = 1 ↔ GQ.some C B := by
  simp [restrictedExists, GQ.some]

@[simp] theorem restrictedExists_eq_neg_one_iff :
    restrictedExists C B = -1 ↔ (∃ x, C x) ∧ ¬ GQ.some C B := by
  simp [restrictedExists, GQ.some]

/-- What (11) asserts, when assertive, is exactly `every`. -/
theorem belnap_forall_content_eq_every (h : restrictedForall C B ≠ 0) :
    restrictedForall C B = 1 ↔ every C B := by
  simp_all

/-! ### The square of opposition -/

/-- The four Aristotelian forms as restricted quantifications make up a square, since "semantic
relations between these forms turn out ... to constitute what is pretty much a good old
fashioned square of opposition" (p. 8). -/
noncomputable def belnapSquare (C B : E → Prop) : Square SignType where
  A := restrictedForall C B
  E := restrictedForall C (fun x ↦ ¬B x)
  I := restrictedExists C B
  O := restrictedExists C (fun x ↦ ¬B x)

/-- All four forms share one assertiveness condition, ∃xCx, so the square's relations are as
strong as possible, with equi-assertiveness on top of the content relations (p. 8). -/
theorem square_equiassertive :
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).E = 0) ∧
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).I = 0) ∧
    ((belnapSquare C B).A = 0 ↔ (belnapSquare C B).O = 0) := by
  simp [belnapSquare]

/-- Abstracting over the scope, the truth conditions of the four forms make up a square in the
Boolean algebra `(E → Prop) → Prop`. -/
def contentSquare (C : E → Prop) : Square ((E → Prop) → Prop) where
  A B := (belnapSquare C B).A = 1
  E B := (belnapSquare C B).E = 1
  I B := (belnapSquare C B).I = 1
  O B := (belnapSquare C B).O = 1

theorem contentSquare_eq_square (hC : ∃ x, C x) : contentSquare C = GQ.square C := by
  simp only [contentSquare, GQ.square, Square.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext B <;> simp [belnapSquare, hC, every, no, GQ.some, compl_apply]

theorem content_square_relations (hR : ∃ x : E, C x) :
    SquareRelations (contentSquare C) :=
  contentSquare_eq_square hR ▸ GQ.square_relations hR

/-! ### Obversion, I-conversion, Barbara -/

/-- Obversion is a strong equivalence (p. 8), since ∀x(Cx/¬¬Bx) and ∀x(Cx/Bx) are equi-assertive
with identical content. -/
theorem obversion : restrictedForall C (fun x ↦ ¬¬B x) = restrictedForall C B :=
  SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp) (by simp [every])

/-- I-conversion is equitrue, in that "truth is preserved in passing from one to the other"
(p. 8), although "their propositional contents are unrelated". -/
theorem i_conversion_equitrue : restrictedExists C B = 1 ↔ restrictedExists B C = 1 := by
  simp [GQ.some, and_comm]

/-- I-conversion is not equi-assertive, since "'Some unicorns are animals' is nonassertive while
'Some animals are unicorns' is just plain false" (p. 8). In any nonempty domain, a restrictor true
of everything and one true of nothing separate the two conditions. -/
theorem i_conversion_not_equiassertive [Nonempty E] :
    ∃ C B : E → Prop, restrictedExists C B ≠ 0 ∧ restrictedExists B C = 0 :=
  ⟨fun _ ↦ True, fun _ ↦ False, by simp, by simp⟩

/-- Barbara's minor propagates assertiveness, in that "for every w in which Barbara's minor is
true_w, both her major and her conclusion are assertive_w" (p. 9). -/
theorem barbara_assertive (A C B : E → Prop) (hMinor : restrictedForall A C = 1) :
    restrictedForall C B ≠ 0 ∧ restrictedForall A B ≠ 0 := by
  simp only [restrictedForall_eq_one_iff, every] at hMinor
  obtain ⟨⟨x, hAx⟩, hAC⟩ := hMinor
  simpa using ⟨⟨x, hAC x hAx⟩, ⟨x, hAx⟩⟩

/-- When Barbara's minor is true her major implies her conclusion, and "it is her major alone
which does any implying of her conclusion, a feature of the situation which doubtless explains
the tradition according to which Barbara's major is major and her minor only minor" (p. 9). -/
theorem barbara (A C B : E → Prop) (hMinor : restrictedForall A C = 1) :
    restrictedForall C B = 1 → restrictedForall A B = 1 := by
  simp only [restrictedForall_eq_one_iff, every] at hMinor ⊢
  exact fun ⟨_, hCB⟩ ↦ ⟨hMinor.1, fun x hAx ↦ hCB x (hMinor.2 x hAx)⟩

/-! ### Contraposition and confirmation (§6) -/

/-- The contrapositive ∀x(¬Bx/¬Cx) is assertive when there are nonblack things, and ∀x(Cx/Bx)
when there are crows. Reports that something is not a crow support the contrapositive but are
"evidentially irrelevant" to the original (p. 10), so the confirmation paradox dissolves because
the two are not the same conditional assertion. -/
theorem contrapositive_different_assertiveness :
    (restrictedForall C B ≠ 0 ↔ ∃ x, C x) ∧
      (restrictedForall (fun x ↦ ¬B x) (fun x ↦ ¬C x) ≠ 0 ↔ ∃ x, ¬B x) := by
  simp

end Belnap1970
