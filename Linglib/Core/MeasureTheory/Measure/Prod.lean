/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Measures on a product at atoms

The product measure at a pair on reals and at a set given by its fibers over a finite second
coordinate; the marginals `Measure.fst` and `Measure.snd` at a singleton, as sums over the other
coordinate when it ranges over a finite type, in `ℝ≥0∞` and on reals; and absolute continuity of
a joint with respect to the product of its marginals. `[UPSTREAM]` candidate for
`Mathlib/MeasureTheory/Measure/Prod.lean`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem prod_real_singleton (μ : Measure α) (ν : Measure β) [SFinite ν] (a : α) (b : β) :
    (μ.prod ν).real {(a, b)} = μ.real {a} * ν.real {b} := by
  rw [← Set.singleton_prod_singleton, measureReal_prod_prod]

/-! ### Sets given by their fibers over a finite coordinate -/

section Fibers

variable [MeasurableSingletonClass β] [Fintype β] (μ : Measure α) (ν : Measure β)
  {f : β → Set α}

theorem prod_apply_fibers [SFinite ν] (hf : ∀ b, MeasurableSet (f b)) :
    (μ.prod ν) {p | p.1 ∈ f p.2} = ∑ b, μ (f b) * ν {b} := by
  rw [show {p : α × β | p.1 ∈ f p.2} = ⋃ b, f b ×ˢ {b} by ext ⟨a, b⟩; simp,
    measure_iUnion (fun b b' h ↦ Set.disjoint_prod.mpr (.inr (Set.disjoint_singleton.mpr h)))
      fun b ↦ (hf b).prod (.singleton b), tsum_fintype]
  simp only [prod_prod]

theorem prod_real_fibers [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf : ∀ b, MeasurableSet (f b)) :
    (μ.prod ν).real {p | p.1 ∈ f p.2} = ∑ b, μ.real (f b) * ν.real {b} := by
  rw [measureReal_def, prod_apply_fibers μ ν hf,
    ENNReal.toReal_sum fun b _ ↦ ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top ν _)]
  simp only [ENNReal.toReal_mul, measureReal_def]

end Fibers

/-! ### Marginals at a singleton -/

section Marginals

variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem fst_apply_singleton [Fintype β] (ρ : Measure (α × β)) (a : α) :
    ρ.fst {a} = ∑ b, ρ {(a, b)} := by
  rw [fst_apply (.singleton a), measure_preimage_fst_singleton_eq_sum]

theorem snd_apply_singleton [Fintype α] (ρ : Measure (α × β)) (b : β) :
    ρ.snd {b} = ∑ a, ρ {(a, b)} := by
  rw [snd_apply (.singleton b), measure_preimage_snd_singleton_eq_sum]

theorem fst_real_singleton [Fintype β] (ρ : Measure (α × β)) (a : α) :
    ρ.fst.real {a} = ρ.real ↑(({a} : Finset α) ×ˢ (Finset.univ : Finset β)) := by
  rw [measureReal_def, measureReal_def, fst_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product, Finset.sum_singleton]

theorem snd_real_singleton [Fintype α] (ρ : Measure (α × β)) (b : β) :
    ρ.snd.real {b} = ρ.real ↑((Finset.univ : Finset α) ×ˢ ({b} : Finset β)) := by
  rw [measureReal_def, measureReal_def, snd_apply_singleton, ← sum_measure_singleton,
    Finset.sum_product]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ ↦ (Finset.sum_singleton _ _).symm)

theorem fst_real_singleton_eq_sum [Fintype β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (a : α) : ρ.fst.real {a} = ∑ b, ρ.real {(a, b)} := by
  simp [measureReal_def, fst_apply_singleton, ENNReal.toReal_sum, measure_ne_top]

theorem snd_real_singleton_eq_sum [Fintype α] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (b : β) : ρ.snd.real {b} = ∑ a, ρ.real {(a, b)} := by
  simp [measureReal_def, snd_apply_singleton, ENNReal.toReal_sum, measure_ne_top]

theorem absolutelyContinuous_fst_prod_snd [Countable α] [Countable β] (ρ : Measure (α × β))
    [SFinite ρ] : ρ ≪ ρ.fst.prod ρ.snd := by
  refine absolutelyContinuous_of_forall_singleton fun ⟨a, b⟩ h ↦ ?_
  rw [← Set.singleton_prod_singleton, prod_prod, mul_eq_zero, fst_apply (.singleton a),
    snd_apply (.singleton b)] at h
  exact h.elim (measure_mono_null (Set.singleton_subset_iff.mpr rfl))
    (measure_mono_null (Set.singleton_subset_iff.mpr rfl))

end Marginals

end MeasureTheory.Measure
