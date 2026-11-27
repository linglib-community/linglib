module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Logic.Trivalent.Proposition
public import Linglib.Logic.Trivalent.Supervaluation

/-!
# Counterfactuals over sets of antecedent propositions

This file defines counterfactuals whose antecedent denotes a set `S` of propositions, such as the
disjuncts of a disjunctive antecedent or the antecedent's truthmakers. The collective reading
`disjunctiveImp ord S C` is the counterfactual `closestImp ord (⋃₀ S) C` of the union of the
propositions, which is Lewis's treatment of a disjunctive antecedent. The distributive reading
`distributiveImp ord S C` is `⋂ A ∈ S, closestImp ord A C`, the counterfactual of each
proposition, which validates the simplification of disjunctive antecedents. The homogeneous
reading `homogeneousImp ord S C w` is the supervaluation of `w ∈ closestImp ord A C` over
`A ∈ S`: true when every proposition's counterfactual holds, false when none does, and undefined
otherwise.

## References

* [L. Alonso-Ovalle, *Counterfactuals, correlatives, and disjunction* (2009)][alonso-ovalle-2009]
* [P. Santorio, *Alternatives and truthmakers in conditional semantics* (2018)][santorio-2018]
* [F. Cariani and S. Goldstein, *Conditional heresies* (2020)][cariani-goldstein-2020]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973b]
-/

@[expose] public section

namespace Conditional

variable {W : Type*} (ord : W → Preorder W) (S : Set (Set W)) (C : Set W)

/-- The distributive reading, on which the counterfactual holds of each proposition in `S`. -/
def distributiveImp : Set W := ⋂ A ∈ S, closestImp ord A C

/-- The collective reading, the counterfactual of the union of the propositions in `S`. -/
def disjunctiveImp : Set W := closestImp ord (⋃₀ S) C

/-- The all-or-nothing verdict over `S`, super-truth over its propositions' counterfactuals. -/
noncomputable def homogeneousImp (w : W) : Trivalent :=
  Trivalent.supervaluationOn S fun A ↦ w ∈ closestImp ord A C

variable {ord S C} {T : Set (Set W)} {A B : Set W} {w : W}

@[simp] theorem mem_distributiveImp :
    w ∈ distributiveImp ord S C ↔ ∀ A ∈ S, w ∈ closestImp ord A C :=
  Set.mem_iInter₂

theorem distributiveImp_anti (h : S ⊆ T) : distributiveImp ord T C ⊆ distributiveImp ord S C :=
  Set.biInter_subset_biInter_left h

@[simp] theorem distributiveImp_singleton : distributiveImp ord {A} C = closestImp ord A C :=
  Set.biInter_singleton ..

theorem distributiveImp_pair :
    distributiveImp ord {A, B} C = closestImp ord A C ∩ closestImp ord B C :=
  Set.biInter_pair ..

theorem mem_distributiveImp_pair :
    w ∈ distributiveImp ord {A, B} C ↔ w ∈ closestImp ord A C ∧ w ∈ closestImp ord B C := by
  rw [distributiveImp_pair, Set.mem_inter_iff]

@[simp] theorem disjunctiveImp_singleton : disjunctiveImp ord {A} C = closestImp ord A C := by
  rw [disjunctiveImp, Set.sUnion_singleton]

theorem disjunctiveImp_pair : disjunctiveImp ord {A, B} C = closestImp ord (A ∪ B) C := by
  rw [disjunctiveImp, Set.sUnion_pair]

theorem mem_disjunctiveImp_pair_of_mem_distributiveImp (h : w ∈ distributiveImp ord {A, B} C) :
    w ∈ disjunctiveImp ord {A, B} C := by
  rw [disjunctiveImp_pair]
  exact mem_closestImp_union (mem_distributiveImp_pair.mp h).1 (mem_distributiveImp_pair.mp h).2

theorem homogeneousImp_eq_true_iff :
    homogeneousImp ord S C w = .true ↔ w ∈ distributiveImp ord S C := by
  rw [homogeneousImp, Trivalent.supervaluationOn_eq_true_iff, mem_distributiveImp]

theorem homogeneousImp_eq_false_iff :
    homogeneousImp ord S C w = .false ↔ S.Nonempty ∧ ∀ A ∈ S, w ∉ closestImp ord A C :=
  Trivalent.supervaluationOn_eq_false_iff

theorem homogeneousImp_eq_undefined_iff :
    homogeneousImp ord S C w = .undefined ↔
      (∃ A ∈ S, w ∈ closestImp ord A C) ∧ ∃ A ∈ S, w ∉ closestImp ord A C :=
  Trivalent.supervaluationOn_eq_undefined_iff

instance [Decidable (w ∈ closestImp ord A C)] : Decidable (w ∈ distributiveImp ord {A} C) :=
  decidable_of_iff _ (Set.ext_iff.mp distributiveImp_singleton w).symm

instance [Decidable (w ∈ closestImp ord A C)] [Decidable (w ∈ distributiveImp ord S C)] :
    Decidable (w ∈ distributiveImp ord (insert A S) C) :=
  decidable_of_iff (w ∈ closestImp ord A C ∧ w ∈ distributiveImp ord S C) <| by
    simp only [mem_distributiveImp, Set.forall_mem_insert]

instance [Decidable (w ∈ closestImp ord A C)] : Decidable (w ∈ disjunctiveImp ord {A} C) :=
  decidable_of_iff _ (Set.ext_iff.mp disjunctiveImp_singleton w).symm

instance [Decidable (w ∈ closestImp ord (A ∪ B) C)] :
    Decidable (w ∈ disjunctiveImp ord {A, B} C) :=
  decidable_of_iff _ (Set.ext_iff.mp disjunctiveImp_pair w).symm

end Conditional
