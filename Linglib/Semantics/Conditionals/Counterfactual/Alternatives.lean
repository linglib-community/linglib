module

public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Semantics.Conditionals.Counterfactual

/-!
# Counterfactuals over sets of antecedent propositions

This file defines counterfactuals whose antecedent denotes a finite set of propositions, such as
the disjuncts of a disjunctive antecedent or the antecedent's truthmakers. Such a counterfactual
can be read collectively, quantifying over the closest worlds of the union of the propositions,
which is Lewis's treatment of a disjunctive antecedent and does not validate the simplification
of disjunctive antecedents, or distributively, requiring the counterfactual of each proposition,
which does. The homogeneous reading is super-truth over the propositions: true when every
proposition's counterfactual holds, false when none does, and indeterminate otherwise.

## Main definitions

* `Conditional.disjunctiveImp`: the counterfactual over the union of the propositions.
* `Conditional.distributiveImp`: the counterfactual of each proposition.
* `Conditional.homogeneousImp`: the all-or-nothing verdict over the propositions.

## References

* [L. Alonso-Ovalle, *Counterfactuals, correlatives, and disjunction* (2009)][alonso-ovalle-2009]
* [P. Santorio, *Alternatives and truthmakers in conditional semantics* (2018)][santorio-2018]
* [F. Cariani and S. Goldstein, *Conditional heresies* (2020)][cariani-goldstein-2020]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973b]
-/

@[expose] public section

namespace Conditional

variable {W : Type*} (ord : W → Preorder W) (S : Finset (Finset W)) (C : Set W)

/-- The distributive reading, on which the counterfactual holds of each proposition in `S`. -/
def distributiveImp : Set W := ⋂ A ∈ S, closestImp ord ↑A C

variable {ord S C} {w : W}

@[simp] theorem mem_distributiveImp :
    w ∈ distributiveImp ord S C ↔ ∀ A ∈ S, w ∈ closestImp ord ↑A C :=
  Set.mem_iInter₂

variable [DecidableEq W]

variable (ord S C) in
/-- The counterfactual over `S` quantifies over the closest worlds of the union of its
propositions. -/
def disjunctiveImp : Set W := closestImp ord ↑(S.sup id) C

theorem coe_sup_id : (↑(S.sup id) : Set W) = ⋃ A ∈ S, (↑A : Set W) := by
  ext; simp

theorem disjunctiveImp_eq_closestImp_iUnion :
    disjunctiveImp ord S C = closestImp ord (⋃ A ∈ S, (↑A : Set W)) C := by
  rw [disjunctiveImp, coe_sup_id]

theorem disjunctiveImp_singleton (A : Finset W) :
    disjunctiveImp ord {A} C = closestImp ord ↑A C := by
  simp [disjunctiveImp]

theorem disjunctiveImp_pair (A B : Finset W) :
    disjunctiveImp ord {A, B} C = closestImp ord (↑A ∪ ↑B) C := by
  simp [disjunctiveImp]

theorem mem_distributiveImp_pair {A B : Finset W} :
    w ∈ distributiveImp ord {A, B} C ↔ w ∈ closestImp ord ↑A C ∧ w ∈ closestImp ord ↑B C := by
  simp

theorem mem_disjunctiveImp_pair_of_mem_distributiveImp {A B : Finset W}
    (h : w ∈ distributiveImp ord {A, B} C) : w ∈ disjunctiveImp ord {A, B} C := by
  rw [disjunctiveImp_pair]
  exact mem_closestImp_union (mem_distributiveImp_pair.1 h).1 (mem_distributiveImp_pair.1 h).2

section Homogeneity

variable (ord S C) [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ C)] (w : W)

/-- The all-or-nothing verdict over `S`, super-truth over its propositions' counterfactuals. -/
def homogeneousImp : SignType := SignType.supervaluation S fun A ↦ w ∈ closestImp ord ↑A C

instance : Decidable (w ∈ disjunctiveImp ord S C) :=
  inferInstanceAs (Decidable (w ∈ closestImp ord ↑(S.sup id) C))

instance : Decidable (w ∈ distributiveImp ord S C) :=
  decidable_of_iff _ mem_distributiveImp.symm

variable {ord S C w}

theorem homogeneousImp_eq_one_iff :
    homogeneousImp ord S C w = 1 ↔ w ∈ distributiveImp ord S C := by
  rw [homogeneousImp, SignType.supervaluation_eq_one_iff, mem_distributiveImp]

theorem homogeneousImp_eq_neg_one_iff :
    homogeneousImp ord S C w = -1 ↔ S.Nonempty ∧ ∀ A ∈ S, w ∉ closestImp ord ↑A C :=
  SignType.supervaluation_eq_neg_one_iff ..

theorem homogeneousImp_eq_zero_iff :
    homogeneousImp ord S C w = 0 ↔
      (∃ A ∈ S, w ∈ closestImp ord ↑A C) ∧ ∃ A ∈ S, w ∉ closestImp ord ↑A C :=
  SignType.supervaluation_eq_zero_iff ..

end Homogeneity

end Conditional
