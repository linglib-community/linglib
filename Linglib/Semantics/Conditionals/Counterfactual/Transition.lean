module

public import Mathlib.Basic.Rel
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Core.Data.Set.Sups

/-!
# Counterfactuals over a transition relation

States are ordered by parthood, and a statement is exactly verified by a set of states and
inexactly verified by the states containing an exact verifier, the upper set `upperClosure A`.
A transition relation `outcome w` relates a state `t` to the possible outcomes `u` of imposing
`t` on the world `w`. The counterfactual `transitionImp outcome A C` is true at `w` when every
outcome at `w` of every exact verifier of the antecedent `A` inexactly verifies the consequent:
the image of `A` under `outcome w` is contained in `C`.

From the form of the clause, the counterfactual from a union of antecedents is the intersection
of the counterfactuals from each (`transitionImp_union`), so a disjunctive antecedent, verified
by the verifiers `A ∪ B ∪ A.lubs B` of either disjunct or of their conjunction, simplifies
(`transitionImp_union_union_lubs`). Where compatible states have a fusion, the counterfactual
to a conjunction is the intersection of the counterfactuals to the conjuncts
(`transitionImp_upperClosure_lubs`).

Three conditions on the transition relation give further rules. When an outcome contains the
state imposed, a statement is a counterfactual consequence of itself
(`transitionImp_upperClosure_self`). When a state within a world has an outcome within it,
modus ponens holds (`state_mem_of_mem_transitionImp`). When moreover an outcome of a state is
an outcome of its fusion with any part of that outcome, the counterfactual is transitive
(`transitionImp_trans`). The transition relation of a causal model satisfies all three.

## Implementation notes

The consequent is an inexact content, an upper set of states, so a consequent that is itself a
counterfactual is not expressed. Worlds are an index of the transition relation, with
`state w` the state of the world `w`, and need not be states.

## References

* [fine-2012]
* [embry-2014]
* [briggs-2012]
-/

@[expose] public section

namespace Conditional

variable {S W : Type*} [PartialOrder S]

/-- The counterfactual of a transition relation: `A > C` is true at `w` when the possible
outcomes at `w` of the exact verifiers of `A` inexactly verify `C`. -/
def transitionImp (outcome : W → SetRel S S) (A : Set S) (C : UpperSet S) : Set W :=
  {w | (outcome w).image A ⊆ C}

variable {outcome : W → SetRel S S} {A A' B D E : Set S} {C C' : UpperSet S} {w : W}

theorem mem_transitionImp : w ∈ transitionImp outcome A C ↔ (outcome w).image A ⊆ C := Iff.rfl

theorem transitionImp_union :
    transitionImp outcome (A ∪ B) C = transitionImp outcome A C ∩ transitionImp outcome B C :=
  Set.ext fun _ ↦ by
    simp only [mem_transitionImp, SetRel.image_union, Set.union_subset_iff, Set.mem_inter_iff]

/-- The counterfactual from a disjunction is the intersection of the counterfactuals from each
disjunct and from their conjunction. -/
theorem transitionImp_union_union_lubs :
    transitionImp outcome (A ∪ B ∪ A.lubs B) C =
      transitionImp outcome A C ∩ transitionImp outcome B C ∩
        transitionImp outcome (A.lubs B) C := by
  rw [transitionImp_union, transitionImp_union]

theorem transitionImp_sup :
    transitionImp outcome A (C ⊔ C') = transitionImp outcome A C ∩ transitionImp outcome A C' :=
  Set.ext fun _ ↦ by
    simp only [mem_transitionImp, UpperSet.coe_sup, Set.subset_inter_iff, Set.mem_inter_iff]

/-- The counterfactual to a conjunction is the intersection of the counterfactuals to the
conjuncts: an outcome contains the fusion of the verifiers it contains. -/
theorem transitionImp_upperClosure_lubs [IsBoundedComplete S] :
    transitionImp outcome A (upperClosure (D.lubs E)) =
      transitionImp outcome A (upperClosure D) ∩ transitionImp outcome A (upperClosure E) := by
  rw [Set.upperClosure_lubs, transitionImp_sup]

/-- Strengthening the exact content of the antecedent. -/
theorem transitionImp_anti (h : A' ⊆ A) : transitionImp outcome A C ⊆ transitionImp outcome A' C :=
  fun _ hw ↦ (SetRel.image_subset_image h).trans hw

/-- Weakening the inexact content of the consequent. -/
theorem transitionImp_mono (h : (C : Set S) ⊆ C') :
    transitionImp outcome A C ⊆ transitionImp outcome A C' :=
  fun _ hw ↦ hw.trans h

@[simp] theorem transitionImp_upperClosure_bot [OrderBot S] :
    transitionImp outcome A (upperClosure {⊥}) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ ↦ ⟨⊥, rfl, bot_le⟩

@[simp] theorem transitionImp_empty : transitionImp outcome ∅ C = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ by
    rw [mem_transitionImp, SetRel.image_empty_right]
    exact Set.empty_subset _

/-- Identity: where an outcome contains the state imposed, a statement is a counterfactual
consequence of itself. -/
theorem transitionImp_upperClosure_self (h : ∀ w t u, (t, u) ∈ outcome w → t ≤ u) :
    transitionImp outcome A (upperClosure A) = Set.univ :=
  Set.eq_univ_of_forall fun w u ⟨t, ht, htu⟩ ↦ ⟨t, ht, h w t u htu⟩

/-- Modus ponens: where a state within a world has an outcome within it, a counterfactual whose
antecedent is true at a world has a true consequent there. -/
theorem state_mem_of_mem_transitionImp (state : W → S)
    (h : ∀ w t, t ≤ state w → ∃ u ≤ state w, (t, u) ∈ outcome w)
    (hw : w ∈ transitionImp outcome A C) (hA : state w ∈ upperClosure A) : state w ∈ C := by
  obtain ⟨t, ht, htw⟩ := hA
  obtain ⟨u, huw, hu⟩ := h w t htw
  exact C.upper huw (hw ⟨t, ht, hu⟩)

/-- Transitivity: where an outcome contains the state imposed and is an outcome of the fusion of
that state with any of its parts, `A > B` and `A ∧ B > C` give `A > C`. -/
theorem transitionImp_trans [IsBoundedComplete S]
    (incl : ∀ w t u, (t, u) ∈ outcome w → t ≤ u)
    (inc : ∀ w t u u' r, (t, u) ∈ outcome w → u' ≤ u → IsLUB {t, u'} r → (r, u) ∈ outcome w) :
    transitionImp outcome A (upperClosure B) ∩ transitionImp outcome (A.lubs B) C ⊆
      transitionImp outcome A C := by
  rintro w ⟨h₁, h₂⟩ u ⟨t, ht, htu⟩
  obtain ⟨u', hu', hu'u⟩ := h₁ ⟨t, ht, htu⟩
  obtain ⟨r, hr⟩ := IsBoundedComplete.exists_isLUB_of_bddAbove t u'
    ⟨u, mem_upperBounds_pair.mpr ⟨incl w t u htu, hu'u⟩⟩
  exact h₂ ⟨r, ⟨t, ht, u', hu', hr⟩, inc w t u u' r htu hu'u hr⟩

end Conditional
