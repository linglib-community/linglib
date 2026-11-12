/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Minimal
public import Mathlib.Order.SuccPred.Basic

/-!
# Pointwise exhaustification

Exhaustifying the member `A i` of a family of alternatives against a relation `r` asserts `A i` and
denies each `A j` with `r i j`. Against every other member it is pre-exhaustification, and [some
member is exhaustified exactly when one member holds](##exists_exhAgainst_ne_iff_existsUnique).
Against the larger indices of a scale it is [maximality](##exhAgainst_lt_iff_maximal). There a
closed property `· ≤ a` is exhaustified [at `a` alone](##exhAgainst_lt_le_iff) and an open property
`· < a` [at the indices `a` covers](##exhAgainst_lt_lt_iff_covBy), of which a dense scale has none,
while on an entailment chain exhaustification [denies just the next
alternative](##exhAgainst_lt_iff_of_isLeast_Ioi).

## References

* [horn-1972]
* [fox-2007]
* [fox-hackl-2006]
* [chierchia-2013]
-/

@[expose] public section

namespace Exhaustification

variable {ι W : Type*}

/-- Exhaustifying the member `A i` against the relation `r` asserts `A i` and denies every `A j`
with `r i j`. -/
def exhAgainst (r : ι → ι → Prop) (A : ι → Prop) (i : ι) : Prop :=
  A i ∧ ∀ j, r i j → ¬ A j

variable {r : ι → ι → Prop} {A : ι → Prop} {i s : ι}

instance [Fintype ι] [DecidableRel r] [DecidablePred A] : Decidable (exhAgainst r A i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _))

/-! ### Independent rivals -/

/-- Some member is exhaustified against all the others iff exactly one member holds. -/
theorem exists_exhAgainst_ne_iff_existsUnique : (∃ i, exhAgainst (· ≠ ·) A i) ↔ ∃! i, A i :=
  ⟨fun ⟨i, hi, h⟩ ↦ ⟨i, hi, fun j hj ↦ by_contra fun hne ↦ h j (Ne.symm hne) hj⟩,
    fun ⟨i, hi, h⟩ ↦ ⟨i, hi, fun j hne hj ↦ hne (h j hj).symm⟩⟩

theorem forall_not_exhAgainst_ne_iff : (∀ i, ¬ exhAgainst (· ≠ ·) A i) ↔ ¬ ∃! i, A i := by
  rw [← exists_exhAgainst_ne_iff_existsUnique, not_exists]

/-! ### Scales -/

section Scale

variable [Preorder ι]

/-- Exhaustifying against the larger indices is maximality: `A i` holds and no larger index
satisfies `A`. -/
theorem exhAgainst_lt_iff_maximal : exhAgainst (· < ·) A i ↔ Maximal A i :=
  maximal_iff_forall_gt.symm

/-- Exhaustifying against the smaller indices is minimality. -/
theorem exhAgainst_gt_iff_minimal : exhAgainst (· > ·) A i ↔ Minimal A i :=
  minimal_iff_forall_lt.symm

/-- At a maximal index there is nothing to deny. -/
theorem exhAgainst_lt_iff_of_isMax (hi : IsMax i) : exhAgainst (· < ·) A i ↔ A i :=
  and_iff_left fun _ hj ↦ (hi.not_lt hj).elim

/-- Exhaustified against the larger indices, the open property `· < a` holds of the indices that
`a` covers. A dense scale has none (`not_covBy`), so there the exhaustification is never
satisfied. -/
theorem exhAgainst_lt_lt_iff_covBy {a : ι} : exhAgainst (· < ·) (· < a) i ↔ i ⋖ a :=
  Iff.rfl

/-- On an entailment chain, exhaustifying `A i` against the stronger alternatives denies just the
next-stronger one `A s`. -/
theorem exhAgainst_lt_iff_of_isLeast_Ioi (hA : Antitone A) (hs : IsLeast (Set.Ioi i) s) :
    exhAgainst (· < ·) A i ↔ A i ∧ ¬ A s :=
  and_congr_right fun _ ↦ ⟨fun h ↦ h s hs.1, fun h _ hj hAj ↦ h (hA (hs.2 hj) hAj)⟩

theorem exhAgainst_lt_iff_succ [SuccOrder ι] [NoMaxOrder ι] (hA : Antitone A) :
    exhAgainst (· < ·) A i ↔ A i ∧ ¬ A (Order.succ i) :=
  exhAgainst_lt_iff_of_isLeast_Ioi hA ⟨Order.lt_succ i, fun _ ↦ Order.succ_le_of_lt⟩

/-- Exhaustified against the larger indices, the closed property `· ≤ a` holds of `a` alone. -/
theorem exhAgainst_lt_le_iff {ι : Type*} [PartialOrder ι] {i a : ι} :
    exhAgainst (· < ·) (· ≤ a) i ↔ i = a :=
  exhAgainst_lt_iff_maximal.trans maximal_le_iff

end Scale

end Exhaustification
