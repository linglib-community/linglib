/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Basic
public import Linglib.Core.Probability.UniformOn

/-!
# Empirical entropies of a finite population

Under the uniform measure on a finite type,
[conditional entropies are counts](##condEntropy_uniformOn_univ): each fibre of the conditioning
attribute weighs in by its share of the population, with the entropy of the distribution of the
other attribute on it. The same holds for
[attributes valued in finite sets](##condEntropy_uniformOn_univ_finset).

## References

* [cover-thomas-2006], chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

section Empirical

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The conditional entropy of one attribute of a finite population given another, under the
uniform measure, weighs each fibre of `Y` by its share of the population and takes the entropy of
the distribution of `X` on the fibre, all as counts. -/
theorem condEntropy_uniformOn_univ [Fintype Ω] {S T : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S] [DecidableEq S] [MeasurableSpace T]
    [MeasurableSingletonClass T] [Fintype T] [DecidableEq T] (X : Ω → S) (Y : Ω → T) :
    H[X | Y ; uniformOn (Set.univ : Set Ω)]
      = ∑ y, ((Finset.univ.filter (Y · = y)).card / Fintype.card Ω : ℝ)
          * ∑ x, negMulLog (((Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card
              / (Finset.univ.filter (Y · = y)).card : ℝ)) := by
  have hY : ∀ y, (Y ⁻¹' {y}).ncard = (Finset.univ.filter (Y · = y)).card := fun y ↦ by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have hXY : ∀ y x, (Y ⁻¹' {y} ∩ X ⁻¹' {x}).ncard
      = (Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card := fun y x ↦ by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  rw [condEntropy_eq_sum X (measurable_of_finite Y)]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [uniformOn_univ_cond, entropy_eq_sum (measurable_of_finite X), uniformOn_real_apply,
    Set.univ_inter, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp_rw [uniformOn_real_apply, hY, hXY]

/-- `condEntropy_uniformOn_univ` for attributes valued in finite sets `A` and `B`, the sums running
over those sets. -/
theorem condEntropy_uniformOn_univ_finset [Fintype Ω] {S T : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [DecidableEq S] [MeasurableSpace T] [MeasurableSingletonClass T]
    [DecidableEq T] {X : Ω → S} {Y : Ω → T} {A : Finset S} {B : Finset T} (hX : ∀ ω, X ω ∈ A)
    (hY : ∀ ω, Y ω ∈ B) :
    H[X | Y ; uniformOn (Set.univ : Set Ω)]
      = ∑ y ∈ B, ((Finset.univ.filter (Y · = y)).card / Fintype.card Ω : ℝ)
          * ∑ x ∈ A, negMulLog (((Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card
              / (Finset.univ.filter (Y · = y)).card : ℝ)) := by
  let X' : Ω → A := fun ω ↦ ⟨X ω, hX ω⟩
  let Y' : Ω → B := fun ω ↦ ⟨Y ω, hY ω⟩
  have hval : MeasurableEmbedding (Subtype.val : B → T) :=
    MeasurableEmbedding.subtype_coe B.measurableSet
  have h : H[X | Y ; uniformOn (Set.univ : Set Ω)] = H[X' | Y' ; uniformOn Set.univ] := by
    rw [← condEntropy_comp_of_injective Y' _ (measurable_of_finite _) measurable_subtype_coe
      Subtype.val_injective, ← condEntropy_comp_right_of_measurableEmbedding _ _
      (measurable_of_finite _) hval]
    rfl
  rw [h, condEntropy_uniformOn_univ, ← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← Finset.sum_coe_sort A]
  simp only [X', Y', Subtype.ext_iff]

end Empirical

end InformationTheory
