/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Marginals of a joint pushed through a parallel composition

Pushing a product measure through `η ∥ₖ η'` pushes each factor through its kernel. Pushing a
joint measure on `α × β` through `Kernel.id ∥ₖ η` keeps the first marginal and composes the
second with `η`. The joint is disintegrated as `ρ.fst ⊗ₘ ρ.condKernel`. On finite types, a
composition, a composition-product and a joint pushed through `Kernel.id ∥ₖ η` are computed at
atoms, and each row of a kernel charged by the input measure is absolutely continuous with
respect to the output marginal.
`[UPSTREAM]` candidate for `Mathlib/Probability/Kernel/Composition/Lemmas.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

/-- Pushing a product measure through a parallel composition pushes each factor through its
kernel, which is Fubini's theorem for the Giry monad. -/
theorem parallelComp_comp_prod (η : Kernel α γ) [IsSFiniteKernel η] (η' : Kernel β δ)
    [IsSFiniteKernel η'] (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν] :
    (η ∥ₖ η') ∘ₘ (μ.prod ν) = (η ∘ₘ μ).prod (η' ∘ₘ ν) := by
  calc (η ∥ₖ η') ∘ₘ (μ.prod ν)
      = ((η ∥ₖ η') ∘ₖ (Kernel.const Unit μ ×ₖ Kernel.const Unit ν)) () := by
        rw [Kernel.comp_apply, Kernel.prod_apply, Kernel.const_apply, Kernel.const_apply]
    _ = (η ∘ₘ μ).prod (η' ∘ₘ ν) := by
        rw [Kernel.parallelComp_comp_prod, Kernel.prod_apply, Kernel.comp_apply,
          Kernel.comp_apply, Kernel.const_apply, Kernel.const_apply]

section Marginals

variable (η : Kernel β γ) [IsMarkovKernel η]

variable [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]

theorem fst_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).fst = ρ.fst := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, fst_compProd]

theorem snd_parallelComp_id_comp : ((Kernel.id ∥ₖ η) ∘ₘ ρ).snd = η ∘ₘ ρ.snd := by
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [parallelComp_comp_compProd, snd_compProd, ← comp_assoc, ← snd_compProd ρ.fst ρ.condKernel,
    ρ.disintegrate ρ.condKernel]

end Marginals

/-! ### Atoms -/

section Atoms

/-- An atom charged by the input measure and emitted by the kernel there is charged by the
output marginal. -/
theorem comp_apply_singleton_ne_zero [MeasurableSingletonClass β] (κ : Kernel α β)
    (μ : Measure α) {a : α} {b : β} (hμ : μ {a} ≠ 0) (hκ : κ a {b} ≠ 0) : (κ ∘ₘ μ) {b} ≠ 0 := by
  rw [bind_apply (.singleton b) (Kernel.aemeasurable _), ← pos_iff_ne_zero,
    lintegral_pos_iff_support (Kernel.measurable_coe _ (.singleton b))]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμ) (measure_mono (Set.singleton_subset_iff.mpr hκ))

variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The output marginal at an atom sums the input mass times the emission over a finite input
type. -/
theorem comp_apply_singleton [Fintype α] (κ : Kernel α β) (μ : Measure α) (b : β) :
    (κ ∘ₘ μ) {b} = ∑ a, μ {a} * κ a {b} := by
  rw [bind_apply (.singleton b) (Kernel.aemeasurable _), lintegral_fintype]
  exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

theorem comp_real_singleton [Fintype α] (κ : Kernel α β) [IsFiniteKernel κ] (μ : Measure α)
    [IsFiniteMeasure μ] (b : β) : (κ ∘ₘ μ).real {b} = ∑ a, μ.real {a} * (κ a).real {b} := by
  rw [measureReal_def, comp_apply_singleton,
    ENNReal.toReal_sum fun a _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp_rw [ENNReal.toReal_mul, measureReal_def]

/-- The output marginal at an atom is the input expectation of the emission. -/
theorem comp_real_singleton_eq_integral [Fintype α] (κ : Kernel α β) [IsFiniteKernel κ]
    (μ : Measure α) [IsFiniteMeasure μ] (b : β) : (κ ∘ₘ μ).real {b} = ∫ a, (κ a).real {b} ∂μ := by
  rw [comp_real_singleton, integral_fintype .of_finite]; rfl

/-- A composition-product at an atom. -/
theorem compProd_apply_singleton (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) (b : β) : (μ ⊗ₘ κ) {(a, b)} = μ {a} * κ a {b} := by
  rw [compProd_apply (.singleton _)]
  have h : (fun a' ↦ κ a' (Prod.mk a' ⁻¹' {(a, b)})) = ({a} : Set α).indicator fun _ ↦ κ a {b} := by
    ext a'
    by_cases ha : a' = a
    · subst ha
      simp [Set.preimage]
    · simp [Set.preimage, ha]
  rw [h, lintegral_indicator (.singleton a), setLIntegral_const, mul_comm]

theorem compProd_real_singleton (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (a : α) (b : β) : (μ ⊗ₘ κ).real {(a, b)} = μ.real {a} * (κ a).real {b} := by
  simp [measureReal_def, compProd_apply_singleton]

variable [Fintype α] [Fintype β] [MeasurableSingletonClass γ]

/-- At an atom, a joint pushed through `Kernel.id ∥ₖ η` has its second coordinate summed out
through the kernel. -/
theorem parallelComp_id_comp_apply_singleton (ρ : Measure (α × β)) (η : Kernel β γ)
    [IsSFiniteKernel η] (a : α) (c : γ) :
    (((Kernel.id : Kernel α α) ∥ₖ η) ∘ₘ ρ) {(a, c)} = ∑ b, ρ {(a, b)} * η b {c} := by
  classical
  rw [comp_eq_sum_of_countable, sum_apply _ (.singleton _), tsum_fintype, Fintype.sum_prod_type]
  simp only [smul_apply, Kernel.parallelComp_apply, Kernel.id_apply, ← Set.singleton_prod_singleton,
    prod_prod, dirac_apply' _ (.singleton _), smul_eq_mul, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

theorem parallelComp_id_comp_real_singleton (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (η : Kernel β γ) [IsFiniteKernel η] (a : α) (c : γ) :
    (((Kernel.id : Kernel α α) ∥ₖ η) ∘ₘ ρ).real {(a, c)}
      = ∑ b, ρ.real {(a, b)} * (η b).real {c} := by
  rw [measureReal_def, parallelComp_id_comp_apply_singleton,
    ENNReal.toReal_sum fun b _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

end Atoms

section Fiber

variable [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β]
  (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]

/-- On finite types, integrating against a composition-product integrates each row against the
kernel and averages over the first measure. -/
theorem integral_compProd_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : α × β → E) :
    ∫ z, f z ∂(μ ⊗ₘ κ) = ∑ a, μ.real {a} • ∫ b, f (a, b) ∂(κ a) := by
  rw [integral_fintype .of_finite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_fintype .of_finite, Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [compProd_real_singleton, mul_smul]

/-- Conditioning a composition-product on a first coordinate of positive mass and forgetting
that coordinate gives its row. -/
theorem map_snd_cond_fst_compProd {a : α} (ha : μ {a} ≠ 0) :
    ((μ ⊗ₘ κ)[|Prod.fst ⁻¹' {a}]).map Prod.snd = κ a := by
  refine ext_iff_singleton.2 fun b ↦ ?_
  have hfst : (μ ⊗ₘ κ) (Prod.fst ⁻¹' {a}) = μ {a} := by
    rw [← fst_apply (.singleton a), fst_compProd]
  rw [map_apply measurable_snd (.singleton b), cond_apply (measurable_fst (.singleton a)),
    show Prod.fst ⁻¹' {a} ∩ Prod.snd ⁻¹' {b} = {(a, b)} by ext ⟨x, y⟩; simp,
    compProd_apply_singleton, hfst, ← mul_assoc, ENNReal.inv_mul_cancel ha (measure_ne_top _ _),
    one_mul]

end Fiber


end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- A composition of kernels at an atom, over a finite middle type. -/
theorem comp_apply_singleton [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (η : Kernel β γ) (κ : Kernel α β) (a : α) (c : γ) :
    (η ∘ₖ κ) a {c} = ∑ b, κ a {b} * η b {c} := by
  rw [comp_apply, Measure.comp_apply_singleton]

theorem comp_real_singleton [Fintype β] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] (η : Kernel β γ) [IsFiniteKernel η] (κ : Kernel α β)
    [IsFiniteKernel κ] (a : α) (c : γ) :
    ((η ∘ₖ κ) a).real {c} = ∑ b, (κ a).real {b} * (η b).real {c} := by
  rw [comp_apply, Measure.comp_real_singleton]

/-- A row of a kernel is absolutely continuous with respect to the output marginal of an input
measure that charges its input. -/
theorem absolutelyContinuous_comp [Fintype α] [MeasurableSingletonClass α] (κ : Kernel α β)
    (μ : Measure α) {a : α} (ha : μ {a} ≠ 0) : κ a ≪ κ ∘ₘ μ :=
  ae_iff_of_countable.1 Measure.absolutelyContinuous_comp_of_countable a ha

end ProbabilityTheory.Kernel
