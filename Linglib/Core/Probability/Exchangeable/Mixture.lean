/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.DirectingMeasure
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Condexp

/-!
# Mixtures of i.i.d. sequences

Consequences of de Finetti's theorem for an exchangeable sequence of random variables in a
standard Borel space, with the weakest measurability hypotheses: its joint law is a mixture of
laws of independent and identically distributed sequences, and conversely; its terms are
conditionally independent given the tail σ-algebra; and for zeros and ones the mixing measure
lives on `[0, 1]`.

## Main results

* `ProbabilityTheory.exchangeable_iff_exists_map_eq_iid_comp`: a sequence is exchangeable if and
  only if its law is `Kernel.iid ℕ E ∘ₘ Λ` for a probability measure `Λ` on the probability
  measures on `E`.
* `ProbabilityTheory.Contractable.iCondIndepFun`: a contractable sequence is conditionally
  independent given its tail σ-algebra.
* `ProbabilityTheory.Exchangeable.exists_measure_real_eq_integral_pow_mul`: for sequences of
  zeros and ones, the probability of a pattern is `∫ θ ^ k * (1 - θ) ^ (n - k) ∂Λ` for a
  probability measure `Λ` on `[0, 1]`.

## References

* [kallenberg-2005]
* [kallenberg-2021]

## Tags

exchangeable, de Finetti, mixture, conditionally independent
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

section Mixture

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {μ : Measure Ω}
  {X : ℕ → Ω → E}

/-- The joint law of an exchangeable sequence of random variables in a standard Borel space is a
mixture of laws of independent and identically distributed sequences. -/
theorem Exchangeable.exists_map_eq_iid_comp [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (h : Exchangeable X μ) :
    ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
      μ.map (fun ω i ↦ X i ω) = Kernel.iid ℕ E ∘ₘ Λ := by
  have : IsProbabilityMeasure (μ.map fun ω i ↦ X i ω) :=
    (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 ‹_›
  obtain ⟨Λ, hΛ, hlaw⟩ := ((exchangeable_tfae (μ := μ.map fun ω i ↦ X i ω)
    (X := fun i (x : ℕ → E) ↦ x i) measurable_pi_apply).out 1 3).1
    ((exchangeable_iff_exchangeable_eval_map h.aemeasurable).1 h)
  exact ⟨Λ, hΛ, by simpa using hlaw.map_eq⟩

/-- The joint law of a sequence of random variables in a standard Borel space is exchangeable if
and only if it is a mixture of laws of independent and identically distributed sequences. -/
theorem exchangeable_iff_exists_map_eq_iid_comp [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    Exchangeable X μ ↔ ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
      μ.map (fun ω i ↦ X i ω) = Kernel.iid ℕ E ∘ₘ Λ :=
  ⟨Exchangeable.exists_map_eq_iid_comp, fun ⟨_, _, h⟩ ↦ exchangeable_of_map_eq_bind hX h⟩

/-- Given the tail σ-algebra, the terms of a contractable sequence of random variables are
conditionally independent ([kallenberg-2005] Theorem 1.1). -/
theorem Contractable.iCondIndepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (h : Contractable X μ) (hX : ∀ i, Measurable (X i))
    (h𝓣 : limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ≤ mΩ) :
    iCondIndepFun (limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop) h𝓣 X μ := by
  classical
  rw [iCondIndepFun_iff _ h𝓣 _ _ hX]
  intro s g hg
  choose! B hB hBg using fun i (hi : i ∈ s) ↦ MeasurableSpace.measurableSet_comap.1 (hg i hi)
  let t : ℕ → Set E := fun i ↦ if i ∈ s then B i else Set.univ
  have ht (i : ℕ) : MeasurableSet (t i) := by
    by_cases hi : i ∈ s
    · simpa [t, hi] using hB i hi
    · simp [t, hi]
  have hgt (i : ℕ) (hi : i ∈ s) : g i = X i ⁻¹' t i := by simp [t, hi, hBg i hi]
  have hb (i : ℕ) (y : E) : |(t i).indicator (1 : E → ℝ) y| ≤ 1 := by
    by_cases hy : y ∈ t i <;> simp [hy]
  have hone (i : ℕ) (hi : i ∈ s) :
      μ⟦g i | limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop⟧ =ᵐ[μ]
        μ[(t i).indicator 1 ∘ X 0 |
          limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop] := by
    have := h.condExp_finsetProd_ae_eq hX {i} (fun i ↦ (t i).indicator 1)
      (fun i ↦ measurable_one.indicator (ht i)) (fun _ ↦ 1) hb
    simp only [Finset.prod_singleton] at this
    rw [hgt i hi]
    exact this
  have hS : (⋂ i ∈ s, g i) = (fun ω i ↦ X i ω) ⁻¹' (s : Set ℕ).pi t := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
    exact forall₂_congr fun i hi ↦ by rw [hgt i hi, Set.mem_preimage]
  have hinter : (⋂ i ∈ s, g i).indicator (fun _ ↦ (1 : ℝ)) =
      fun ω ↦ ∏ i ∈ s, (t i).indicator 1 (X i ω) := by
    rw [hS]
    funext ω
    exact Set.indicator_pi_one_apply s t (fun i ↦ X i ω)
  rw [hinter]
  refine (h.condExp_finsetProd_ae_eq hX s (fun i ↦ (t i).indicator 1)
    (fun i ↦ measurable_one.indicator (ht i)) (fun _ ↦ 1) hb).trans ?_
  filter_upwards [(eventually_all_finset s).2 hone] with ω hω
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun i hi ↦ (hω i hi).symm

/-- Under an exchangeable sequence of zeros and ones, the probability of each finite pattern is
`∫ θ ^ k * (1 - θ) ^ (n - k) ∂Λ` for one probability measure `Λ` on `[0, 1]`, where `k` is the
number of ones among the `n` terms. -/
theorem Exchangeable.exists_measure_real_eq_integral_pow_mul {X : ℕ → Ω → Bool}
    [IsProbabilityMeasure μ] (h : Exchangeable X μ) :
    ∃ Λ : Measure ℝ, IsProbabilityMeasure Λ ∧ Λ (Set.Icc 0 1)ᶜ = 0 ∧
      ∀ (n : ℕ) (x : Fin n → Bool),
        μ.real {ω | ∀ i : Fin n, X i ω = x i} =
          ∫ θ, θ ^ (Finset.univ.filter fun i ↦ x i = true).card *
            (1 - θ) ^ (Finset.univ.filter fun i ↦ x i = false).card ∂Λ := by
  classical
  obtain ⟨Λ₀, hΛ₀, hmix'⟩ := h.exists_map_eq_iid_comp
  have hmix : μ.map (fun ω i ↦ X i ω) =
      Λ₀.bind fun m ↦ Measure.infinitePi fun _ : ℕ ↦ (m : Measure Bool) := hmix'
  let p : ProbabilityMeasure Bool → ℝ := fun m ↦ ((m : Measure Bool) {true}).toReal
  have hp : Measurable p :=
    ((Measure.measurable_coe (measurableSet_singleton true)).comp
      measurable_subtype_coe).ennreal_toReal
  refine ⟨Λ₀.map p, inferInstance, ?_, fun n x ↦ ?_⟩
  · rw [Measure.map_apply hp measurableSet_Icc.compl]
    convert measure_empty (μ := Λ₀)
    ext m
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_not,
      Set.mem_empty_iff_false, iff_false]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  · let t : ℕ → Set Bool := fun i ↦ if hi : i < n then {x ⟨i, hi⟩} else Set.univ
    have ht (i : ℕ) : MeasurableSet (t i) := by
      by_cases hi : i < n <;> simp [t, hi]
    have hB : MeasurableSet ((Finset.range n : Set ℕ).pi t) :=
      .pi (Finset.range n).countable_toSet fun i _ ↦ ht i
    have hpre : {ω | ∀ i : Fin n, X i ω = x i} =
        (fun ω i ↦ X i ω) ⁻¹' (Finset.range n : Set ℕ).pi t := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Finset.coe_range,
        Set.mem_Iio]
      refine ⟨fun hω i hi ↦ by simpa [t, hi] using hω ⟨i, hi⟩, fun hω i ↦ ?_⟩
      simpa [t, i.isLt] using hω i i.isLt
    rw [hpre, measureReal_def, ← Measure.map_apply_of_aemeasurable h.aemeasurable hB, hmix,
      Measure.bind_apply hB (measurable_infinitePi_const ℕ).aemeasurable]
    simp_rw [Measure.infinitePi_pi _ fun i _ ↦ ht i]
    have hm : Measurable fun m : ProbabilityMeasure Bool ↦
        ∏ i ∈ Finset.range n, (m : Measure Bool) (t i) :=
      Finset.measurable_prod _ fun i _ ↦
        (Measure.measurable_coe (ht i)).comp measurable_subtype_coe
    rw [← integral_toReal hm.aemeasurable
        (ae_of_all _ fun m ↦ ENNReal.prod_lt_top fun i _ ↦ measure_lt_top _ _),
      integral_map hp.aemeasurable (by fun_prop : Continuous _).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun m ↦ ?_)
    have hx (i : Fin n) :
        ((m : Measure Bool) (t i)).toReal = if x i = true then p m else 1 - p m := by
      have hf : ({false} : Set Bool) = {true}ᶜ := by ext b; simp
      simp only [t, i.isLt, ↓reduceDIte]
      cases x i
      · rw [hf, ← measureReal_def, probReal_compl_eq_one_sub (measurableSet_singleton _)]
        rfl
      · rfl
    simp only [ENNReal.toReal_prod]
    rw [← Fin.prod_univ_eq_prod_range (fun i ↦ ((m : Measure Bool) (t i)).toReal)]
    simp_rw [hx, Finset.prod_ite, Finset.prod_const]
    simp

end Mixture

end ProbabilityTheory
