/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exchangeable laws

A family of random variables indexed by `ι` with values in `α` is *exchangeable* when its law, a
measure on `ι → α`, is unchanged by permuting the indices. The permutations act on `ι → α` by
precomposition, as the domain action `(Equiv.Perm ι)ᵈᵐᵃ` (`(DomMulAct.mk σ • x) i = x (σ i)`),
and `Exchangeable μ` is invariance under that action, `SMulInvariantMeasure`. Random partitions
are exchangeable in the same sense, for the action of the permutations on partitions. On a
countable space with measurable singletons, invariance is invariance of the point masses.
Independent and identically distributed values are exchangeable, and under an exchangeable law of
finitely many nonnegative quantities each takes in expectation the same share of their total.

## Main definitions

* `ProbabilityTheory.Exchangeable μ`: every permutation of the indices leaves `μ` unchanged.

## Main results

* `ProbabilityTheory.smulInvariantMeasure_of_measure_singleton`: on a countable space with
  measurable singletons, a measure is invariant under a group action when moving a point never
  changes its mass.
* `ProbabilityTheory.exchangeable_of_measure_singleton`: the same for exchangeability.
* `ProbabilityTheory.exchangeable_iff_map_comp_perm`: a law is exchangeable exactly when
  precomposing with each permutation maps it to itself.
* `ProbabilityTheory.exchangeable_pi`: a product of copies of one measure is exchangeable.
* `ProbabilityTheory.Exchangeable.integral_sum_div_sum`: the members of `A` take together the
  expected share `#A / card ι` of the probability that the total is nonzero.

## Implementation notes

For infinite `ι` the usual definition asks for invariance only under the permutations that move
finitely many indices; `Exchangeable` asks for all of them, which de Finetti's theorem shows
equivalent on standard Borel spaces but which is not proved here. `[UPSTREAM]` candidate:
mathlib has no notion of exchangeability.

## References

* [pitman-2006]
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- On a countable space with measurable singletons, a measure is invariant under a group action
as soon as moving a point never changes its mass. -/
theorem smulInvariantMeasure_of_measure_singleton {G X : Type*} [Group G] [MulAction G X]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] {ν : Measure X}
    (h : ∀ (g : G) (x : X), ν {g • x} = ν {x}) : SMulInvariantMeasure G X ν := by
  refine ⟨fun g S hS ↦ ?_⟩
  have hmap : ν.map (g • ·) = ν := Measure.ext_of_singleton fun x ↦ by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x),
      show (g • ·) ⁻¹' {x} = {g⁻¹ • x} from Set.ext fun y ↦ by
        simp [eq_inv_smul_iff], h]
  rw [← Measure.map_apply (measurable_of_countable _) hS, hmap]

variable {ι α : Type*} [MeasurableSpace α] {μ : Measure (ι → α)}

/-- The law `μ` of an `ι`-indexed family is *exchangeable* when every permutation of the indices,
acting by precomposition, leaves it unchanged. -/
abbrev Exchangeable (μ : Measure (ι → α)) : Prop :=
  SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → α) μ

/-- On a countable space with measurable singletons, a law is exchangeable as soon as permuting a
point never changes its mass. -/
theorem exchangeable_of_measure_singleton [Countable (ι → α)] [MeasurableSingletonClass (ι → α)]
    (h : ∀ (x : ι → α) (σ : Equiv.Perm ι), μ {x ∘ σ} = μ {x}) : Exchangeable μ :=
  smulInvariantMeasure_of_measure_singleton fun c x ↦ h x (DomMulAct.mk.symm c)

/-- Permuting the indices preserves an exchangeable law. -/
theorem Exchangeable.map_comp_perm (hμ : Exchangeable μ) (σ : Equiv.Perm ι) :
    μ.map (· ∘ σ) = μ := by
  have hT : Measurable fun x : ι → α ↦ x ∘ σ := Measurable.of_eval fun i ↦ measurable_pi_apply _
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply hT hs]
  exact SMulInvariantMeasure.measure_preimage_smul (DomMulAct.mk σ) hs

theorem exchangeable_of_map_comp_perm (h : ∀ σ : Equiv.Perm ι, μ.map (· ∘ σ) = μ) :
    Exchangeable μ := by
  refine ⟨fun c s hs ↦ ?_⟩
  set σ : Equiv.Perm ι := DomMulAct.mk.symm c
  have hT : Measurable fun x : ι → α ↦ x ∘ σ := Measurable.of_eval fun k ↦ measurable_pi_apply (σ k)
  have hc : (fun x : ι → α ↦ c • x) = (· ∘ σ) :=
    funext fun x ↦ funext fun k ↦ DomMulAct.smul_apply c x k
  rw [hc, ← Measure.map_apply hT hs, h]

theorem exchangeable_iff_map_comp_perm : Exchangeable μ ↔ ∀ σ : Equiv.Perm ι, μ.map (· ∘ σ) = μ :=
  ⟨fun h ↦ h.map_comp_perm, exchangeable_of_map_comp_perm⟩

/-- Independent and identically distributed values are exchangeable. -/
theorem exchangeable_pi [Fintype ι] (ν : Measure α) [SigmaFinite ν] :
    Exchangeable (Measure.pi fun _ : ι ↦ ν) := by
  refine exchangeable_of_map_comp_perm fun σ ↦ (Measure.pi_eq fun s hs ↦ ?_).symm
  have hT : Measurable fun x : ι → α ↦ x ∘ σ := Measurable.of_eval fun k ↦ measurable_pi_apply (σ k)
  rw [Measure.map_apply hT (MeasurableSet.univ_pi hs)]
  have : (· ∘ σ) ⁻¹' Set.univ.pi s = Set.univ.pi fun i ↦ s (σ.symm i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    exact ⟨fun h i ↦ by simpa using h (σ.symm i), fun h i ↦ by simpa using h (σ i)⟩
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm fun i ↦ ν (s i)

section Share

open scoped Finset

variable [Fintype ι] {f : α → ℝ}

/-- Under an exchangeable law of finitely many nonnegative quantities, each one's share of their
total has the same expectation, so the members of `A` take together the fraction `#A / card ι` of
the probability that the total is nonzero. Where the total is zero, the share is `0 / 0 = 0`: the
event on which the total vanishes, the extinction of a population counted by the quantities,
contributes nothing. -/
theorem Exchangeable.integral_sum_div_sum [IsFiniteMeasure μ] (hμ : Exchangeable μ)
    (hf : Measurable f) (hf0 : ∀ a, 0 ≤ f a) (A : Finset ι) :
    ∫ x, (∑ i ∈ A, f (x i)) / ∑ i, f (x i) ∂μ =
      #A / Fintype.card ι * μ.real {x | ∑ i, f (x i) ≠ 0} := by
  classical
  set F : ι → (ι → α) → ℝ := fun i x ↦ f (x i) / ∑ j, f (x j)
  have hFm i : Measurable (F i) :=
    ((hf.comp (measurable_pi_apply i)).div (Finset.measurable_sum _ fun j _ ↦
      hf.comp (measurable_pi_apply j)))
  have hFi i : Integrable (F i) μ := by
    refine Integrable.of_bound (hFm i).aestronglyMeasurable 1 (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (hf0 _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ hf0 _)]
    exact div_le_one_of_le₀ (Finset.single_le_sum (fun j _ ↦ hf0 (x j)) (Finset.mem_univ i))
      (Finset.sum_nonneg fun j _ ↦ hf0 _)
  have hswap i j : ∫ x, F i x ∂μ = ∫ x, F j x ∂μ := by
    have hT : Measurable fun x : ι → α ↦ x ∘ Equiv.swap i j :=
      Measurable.of_eval fun k ↦ measurable_pi_apply _
    conv_lhs => rw [← hμ.map_comp_perm (Equiv.swap i j)]
    rw [integral_map hT.aemeasurable (hFm i).aestronglyMeasurable]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [F, Function.comp_apply, Equiv.swap_apply_left]
    rw [Equiv.sum_comp (Equiv.swap i j) fun k ↦ f (x k)]
  have hSm : Measurable fun x : ι → α ↦ ∑ i, f (x i) :=
    Finset.measurable_sum _ fun j _ ↦ hf.comp (measurable_pi_apply j)
  have htot : ∑ i, ∫ x, F i x ∂μ = μ.real {x | ∑ i, f (x i) ≠ 0} := by
    rw [← integral_finsetSum _ fun i _ ↦ hFi i]
    calc ∫ x, ∑ i, F i x ∂μ = ∫ x, {x | ∑ i, f (x i) ≠ 0}.indicator 1 x ∂μ :=
          integral_congr_ae (.of_forall fun x ↦ ?_)
      _ = _ := integral_indicator_one (hSm (measurableSet_singleton 0).compl)
    simp only [F, ← Finset.sum_div]
    by_cases h : ∑ i, f (x i) = 0 <;> simp [Set.indicator, h]
  rw [show (fun x ↦ (∑ i ∈ A, f (x i)) / ∑ i, f (x i)) = fun x ↦ ∑ i ∈ A, F i x from
    funext fun x ↦ Finset.sum_div .., integral_finsetSum _ fun i _ ↦ hFi i]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.eq_empty_of_isEmpty A]
  have i₀ : ι := hι.some
  have hc : ∀ i, ∫ x, F i x ∂μ = ∫ x, F i₀ x ∂μ := fun i ↦ hswap i i₀
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := ι))
  simp only [hc, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at htot ⊢
  rw [← htot]
  field_simp

end Share

end ProbabilityTheory
