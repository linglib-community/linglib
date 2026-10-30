module

public import Studies.GeurtsPouscoulous2009

/-!
# Geurts (2010): Quantity Implicatures

This file formalizes the textbook's case against conventionalism in section 7.3 of [geurts-2010],
which rests on [geurts-pouscoulous-2009]'s verification experiment. Conventionalist theories of
scalar inference agree that *some* is read as *some but not all* under an upward-entailing
quantifier such as *all* or *more than one*, and the stronger versions predict the same under a
non-monotone quantifier such as *exactly two*, while none predicts it under a downward-entailing
one; the experiment found no such readings. The three quantifiers of (62) are the earlier study's
`Quant`, and the weak and strong predictions are its `PredictsLocalSIWeak` and `PredictsLocalSI`
(`conventionalist_predictions`). Chapter 3's observation that a downward-entailing environment
reverses a scale, so that *not all* blocks the local inference, is the negated case
(`downward_entailing_blocks`).

## References

* [geurts-2010]
* [geurts-pouscoulous-2009]
-/

@[expose] public section

namespace Geurts2010

open Quantifier Quantifier.Det GeurtsPouscoulous2009

theorem exactlyTwo_not_scopeUp : ¬ ScopeMonotone (Quant.exactlyTwo.sem : Det (Fin 3)) := by
  intro h
  have key : Quant.exactlyTwo.sem (Set.univ : Set (Fin 3)) {s | s = 0 ∨ s = 1} →
      Quant.exactlyTwo.sem (Set.univ : Set (Fin 3)) Set.univ :=
    h Set.univ (Set.subset_univ _)
  simp only [Quant.sem] at key
  revert key
  decide

theorem notAll_not_scopeUp : ¬ ScopeMonotone (Quant.notAll.sem : Det (Fin 3)) := fun h ↦
  h Set.univ (Set.empty_subset Set.univ) (fun hall ↦ hall (Set.mem_univ 0)) subset_rfl

/-- Every conventionalist theory predicts the local reading under *all* and *more than one*, but
only the stronger ones under *exactly two* (Section 7.3, (62)). -/
theorem conventionalist_predictions :
    PredictsLocalSIWeak (Quant.all.sem : Det (Fin 3)) ∧
      PredictsLocalSIWeak (Quant.moreThanOne.sem : Det (Fin 3)) ∧
      ¬ PredictsLocalSIWeak (Quant.exactlyTwo.sem : Det (Fin 3)) ∧
      PredictsLocalSI (Quant.exactlyTwo.sem : Det (Fin 3)) :=
  ⟨all_predictsLocalSIWeak, moreThanOne_predictsLocalSIWeak, exactlyTwo_not_scopeUp,
   exactlyTwo_predictsLocalSI⟩

/-- Section 3.2: the downward-entailing scope of *not all* supports no local inference on either
version of the prediction. -/
theorem downward_entailing_blocks :
    ¬ PredictsLocalSI (Quant.notAll.sem : Det (Fin 3)) ∧
      ¬ PredictsLocalSIWeak (Quant.notAll.sem : Det (Fin 3)) :=
  ⟨notAll_not_predictsLocalSI, notAll_not_scopeUp⟩

end Geurts2010
