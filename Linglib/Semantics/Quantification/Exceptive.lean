module

public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Order.Bounds.Basic

/-!
# Exceptive quantifiers

This file defines the semantics of exceptive constructions, *every student but John* and
*except for John, every student*, over generalized quantifiers. An exceptive subtracts an
exception set from the restrictor of a determiner, in the Boolean algebra of predicates on the
domain. A restrictive exceptive is one the quantification needs: it holds with the subtraction
and fails without it, which [von-fintel-1993] gives as the semantics of the free exceptive.
The exception set of a quantification is the least set whose subtraction makes it true, his
semantics of the *but*-phrase, so that the phrase names the set responsible for the falsehood
of the quantification.

## Main definitions

* `Restrictive`, `IsExceptionSet`: domain subtraction with restrictiveness, and the exception
  set as the least verifying subtraction.

## Main results

* `IsExceptionSet.unique`, `IsExceptionSet.le_restrictor`, `isExceptionSet_iff_disjoint`,
  `isExceptionSet_iff_sInf_eq`: the exception set is unique, lies within the restrictor, is
  disjoint from every verifying subset of the restrictor, and is the intersection of the
  verifying subtractions.
* `isExceptionSet_every_iff`, `isExceptionSet_no_iff`: with *every* the exception set is the
  restrictor minus the scope, with *no* their intersection.
* `IsExceptionSet.eq_bot_of_restrictorMonotone`, `Restrictive.not_of_restrictorMonotone`,
  `Restrictive.mono`: a left-upward-monotone determiner admits only the empty exception set and
  no restrictive exceptive; a left-downward-monotone one preserves restrictiveness under
  enlarging the exception.

## Implementation notes

Restrictor, scope and exception set are predicates, so subtraction is `\`, inclusion `≤` and
disjointness `Disjoint` of the pointwise Boolean algebra, and `every R S` is definitionally
`R ≤ S` (`every_iff_le`) and `no R S` definitionally `R ≤ Sᶜ` (`no_iff_le_compl`). The
disjointness formulation of the uniqueness condition is equivalent to the definition only for
an exception set within the restrictor, which the definition entails
(`IsExceptionSet.le_restrictor`) and the formulation does not.

## References

* [von-fintel-1993]
-/

@[expose] public section

namespace Quantifier.Exceptive

open Quantifier Quantifier.GQ

variable {α : Type*} {Q : GQ α} {A C B : α → Prop}

/-! ### Domain subtraction with restrictiveness and the exception set -/

/-- A restrictive exceptive subtracts the exception set `C` from the restrictor, so that the
quantification holds with the subtraction and fails without it, (17) of [von-fintel-1993] and
his semantics of the free exceptive (38). -/
def Restrictive (Q : GQ α) (A C B : α → Prop) : Prop :=
  Q (A \ C) B ∧ ¬ Q A B

/-- `C` is the exception set of the quantification when it is the least set whose subtraction
from the restrictor makes the quantification true, (20) and (21) of [von-fintel-1993] and his
semantics of the *but*-phrase. -/
def IsExceptionSet (Q : GQ α) (A C B : α → Prop) : Prop :=
  IsLeast {S | Q (A \ S) B} C

namespace Restrictive

/-- A left-upward-monotone determiner falsifies every restrictive exceptive. -/
theorem not_of_restrictorMonotone (hQ : RestrictorMonotone Q) : ¬ Restrictive Q A C B :=
  fun h ↦ h.2 (hQ B sdiff_le h.1)

/-- Under a left-downward-monotone determiner a restrictive exceptive survives enlarging the
exception set, the inference the exception set blocks. -/
theorem mono (hQ : RestrictorAntitone Q) (h : Restrictive Q A C B) {C' : α → Prop}
    (hC : C ≤ C') : Restrictive Q A C' B :=
  ⟨hQ B (sdiff_le_sdiff_left hC) h.1, h.2⟩

end Restrictive

namespace IsExceptionSet

/-- The exception set is unique. -/
theorem unique (h : IsExceptionSet Q A C B) {C' : α → Prop} (h' : IsExceptionSet Q A C' B) :
    C = C' :=
  IsLeast.unique h h'

/-- The exception set lies within the restrictor, since subtracting `C ⊓ A` subtracts as much
as `C`. -/
theorem le_restrictor (h : IsExceptionSet Q A C B) : C ≤ A :=
  (le_inf_iff.1 (h.2 (show Q (A \ (C ⊓ A)) B by rw [sdiff_inf_self_right]; exact h.1))).2

/-- A left-upward-monotone determiner has only the empty exception set, since once the
quantification holds with `C` subtracted it holds with nothing subtracted. -/
theorem eq_bot_of_restrictorMonotone (hQ : RestrictorMonotone Q) (h : IsExceptionSet Q A C B) :
    C = ⊥ :=
  le_bot_iff.1 (h.2 (show Q (A \ ⊥) B by rw [sdiff_bot]; exact hQ B sdiff_le h.1))

theorem restrictive (h : IsExceptionSet Q A C B) (hC : C ≠ ⊥) : Restrictive Q A C B :=
  ⟨h.1, fun hQA ↦ hC (le_bot_iff.1 (h.2 (show Q (A \ ⊥) B by rwa [sdiff_bot])))⟩

/-- When subtracting `S` rescues the quantification exactly when `S` covers `r`, the exception
set is `r`. This is the culprit reasoning of [von-fintel-1993]'s §1.6, which instantiates to
`A \ B` for *every* and `A ⊓ B` for *no*. -/
theorem of_iff_le {r : α → Prop} (h : ∀ S, Q (A \ S) B ↔ r ≤ S) : IsExceptionSet Q A r B :=
  ⟨(h r).2 le_rfl, fun S hS ↦ (h S).1 hS⟩

end IsExceptionSet

/-! ### The three formulations of the uniqueness condition -/

/-- In the second formulation of (21) the exception set is disjoint from every subset of the
restrictor that verifies the quantification. The hypothesis `C ≤ A` is what the definition
entails (`IsExceptionSet.le_restrictor`) and this formulation alone does not. -/
theorem isExceptionSet_iff_disjoint (hCA : C ≤ A) :
    IsExceptionSet Q A C B ↔ Q (A \ C) B ∧ ∀ D ≤ A, Q D B → Disjoint C D := by
  unfold IsExceptionSet IsLeast
  refine and_congr_right fun _ ↦ ⟨fun h D hDA hD ↦ ?_, fun h S hS ↦ ?_⟩
  · exact (le_sdiff.1 (h (show Q (A \ (A \ D)) B by rwa [sdiff_sdiff_eq_self hDA]))).2
  · exact (le_sdiff.2 ⟨hCA, h (A \ S) sdiff_le hS⟩).trans
      (sdiff_sdiff_right_self.le.trans inf_le_right)

/-- In the third formulation of (21) the exception set is the intersection of the sets whose
subtraction verifies the quantification. -/
theorem isExceptionSet_iff_sInf_eq :
    IsExceptionSet Q A C B ↔ Q (A \ C) B ∧ sInf {S | Q (A \ S) B} = C :=
  ⟨fun h ↦ ⟨h.1, h.isGLB.sInf_eq⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2 ▸ fun _ hS ↦ sInf_le hS⟩⟩

/-! ### The universal determiners -/

theorem isExceptionSet_every (A B : α → Prop) : IsExceptionSet every A (A \ B) B :=
  .of_iff_le fun _ ↦ every_iff_le.trans sdiff_le_comm

theorem isExceptionSet_no (A B : α → Prop) : IsExceptionSet no A (A ⊓ B) B :=
  .of_iff_le fun S ↦ by rw [no_iff_le_compl, sdiff_le_comm, sdiff_compl]

/-- (23) of [von-fintel-1993] for *every*. -/
theorem isExceptionSet_every_iff : IsExceptionSet every A C B ↔ A \ B = C :=
  IsLeast.isLeast_iff_eq (isExceptionSet_every A B)

/-- (23) of [von-fintel-1993] for *no*. -/
theorem isExceptionSet_no_iff : IsExceptionSet no A C B ↔ A ⊓ B = C :=
  IsLeast.isLeast_iff_eq (isExceptionSet_no A B)

theorem restrictive_every_iff : Restrictive every A C B ↔ A \ B ≤ C ∧ ¬ A ≤ B := by
  unfold Restrictive
  rw [every_iff_le, sdiff_le_comm, every_iff_le]

theorem restrictive_no_iff : Restrictive no A C B ↔ A ⊓ B ≤ C ∧ ¬ Disjoint A B := by
  unfold Restrictive
  rw [no_iff_le_compl, sdiff_le_comm, sdiff_compl, no_iff_disjoint]

end Quantifier.Exceptive
