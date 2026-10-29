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
denies each `A j` with `r i j`. Against the members the prejacent does not entail it is `exh` read
at a world, in any model (`Exhaustification.mem_exh_range_iff_exhAgainst`); a theory that fixes
which alternatives count as stronger states that relation outright, and its results then hold in
every model. Against every other member it is pre-exhaustification against independent rivals, which
holds of some member exactly when one member holds. Against the larger indices of a scale it is
maximality (`exhAgainst_lt_iff_maximal`): it denies just the next-stronger alternative on an
entailment chain (`exhAgainst_lt_iff_succ`), and on a dense scale it cannot be satisfied, the crash
Fox and Hackl derive for *more than*.

## Main definitions

* `Exhaustification.exhAgainst`: assert a member of a family and deny its rivals.

## Main results

* `Exhaustification.exists_exhAgainst_ne_iff_existsUnique`: against independent rivals, some
  member is exhaustified iff exactly one member holds.
* `Exhaustification.exhAgainst_lt_iff_succ`: on an entailment chain, exhaustification denies the
  next-stronger alternative.

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

/-- On an entailment chain, exhaustifying `A i` against the stronger alternatives denies just the
next-stronger one `A s`. -/
theorem exhAgainst_lt_iff_succ (hA : Antitone A) (his : i < s) (hleast : ∀ j, i < j → s ≤ j) :
    exhAgainst (· < ·) A i ↔ A i ∧ ¬ A s :=
  ⟨fun ⟨hi, h⟩ ↦ ⟨hi, h s his⟩, fun ⟨hi, hs⟩ ↦ ⟨hi, fun j hj hAj ↦ hs (hA (hleast j hj) hAj)⟩⟩

theorem exhAgainst_lt_iff_succOrder [SuccOrder ι] [NoMaxOrder ι] (hA : Antitone A) :
    exhAgainst (· < ·) A i ↔ A i ∧ ¬ A (Order.succ i) :=
  exhAgainst_lt_iff_succ hA (Order.lt_succ i) fun _ ↦ Order.succ_le_of_lt

/-- Exhaustification cannot be satisfied when the prejacent always has a stronger true
alternative, as on a dense scale. -/
theorem not_exhAgainst_lt_of_dense (hdense : A i → ∃ j, i < j ∧ A j) :
    ¬ exhAgainst (· < ·) A i := fun ⟨hi, h⟩ ↦
  let ⟨j, hij, hj⟩ := hdense hi
  h j hij hj

end Scale

end Exhaustification
