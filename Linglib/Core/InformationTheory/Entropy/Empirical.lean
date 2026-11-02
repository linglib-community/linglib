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
other attribute on it. Equivalently the conditional entropy is
[an average over the population](##condEntropy_uniformOn_univ_eq_sum_log) of the logarithm of the
ratio of two class sizes, which needs no finite type of values.

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

private theorem condEntropy_uniformOn_univ_finset [Fintype Ω] {S T : Type*} [MeasurableSpace S]
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

/-- The conditional entropy of one attribute of a finite population given another, under the
uniform measure, is the average over the population of the logarithm of the size of an individual's
class under `Y` over the size of its class under `Y` and `X` together. -/
theorem condEntropy_uniformOn_univ_eq_sum_log [Fintype Ω] {S T : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [DecidableEq S] [MeasurableSpace T] [MeasurableSingletonClass T]
    [DecidableEq T] (X : Ω → S) (Y : Ω → T) :
    H[X | Y ; uniformOn (Set.univ : Set Ω)]
      = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, log ((Finset.univ.filter (Y · = Y ω)).card /
          (Finset.univ.filter fun ω' ↦ Y ω' = Y ω ∧ X ω' = X ω).card) := by
  have hA (ω : Ω) : X ω ∈ Finset.univ.image X := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hB (ω : Ω) : Y ω ∈ Finset.univ.image Y := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  set n : T → ℕ := fun y ↦ (Finset.univ.filter (Y · = y)).card with hn
  set m : T → S → ℕ := fun y x ↦ (Finset.univ.filter fun ω ↦ Y ω = y ∧ X ω = x).card with hm
  have hmn (y : T) (x : S) : m y x ≤ n y :=
    Finset.card_le_card fun ω hω ↦ by
      simp only [Finset.mem_filter] at hω ⊢
      exact ⟨hω.1, hω.2.1⟩
  have hgroup : ∑ ω, log ((n (Y ω) : ℝ) / m (Y ω) (X ω))
      = ∑ y ∈ Finset.univ.image Y, ∑ x ∈ Finset.univ.image X,
          (m y x : ℝ) * log ((n y : ℝ) / m y x) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image Y) (g := Y) fun ω _ ↦ hB ω]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image X) (g := X) fun ω _ ↦ hA ω]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.filter_filter, Finset.sum_congr rfl (g := fun _ ↦ log ((n y : ℝ) / m y x)),
      Finset.sum_const, nsmul_eq_mul]
    intro ω hω
    obtain ⟨rfl, rfl⟩ := (Finset.mem_filter.1 hω).2
    rfl
  rw [condEntropy_uniformOn_univ_finset hA hB]
  change _ = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, log ((n (Y ω) : ℝ) / m (Y ω) (X ω))
  rw [hgroup, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  change ((n y : ℝ) / _) * negMulLog ((m y x : ℝ) / n y) =
    _ * ((m y x : ℝ) * log ((n y : ℝ) / m y x))
  obtain h0 | h0 := Nat.eq_zero_or_pos (n y)
  · have hm0 : m y x = 0 := Nat.le_zero.1 (h0 ▸ hmn y x)
    simp [h0, hm0]
  · have hn0 : (n y : ℝ) ≠ 0 := by positivity
    rw [show log ((n y : ℝ) / m y x) = -log ((m y x : ℝ) / n y) by rw [← log_inv, inv_div],
      negMulLog, div_eq_inv_mul (n y : ℝ)]
    field_simp

end Empirical

end InformationTheory
