/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.DeFinetti
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.ProductMeasure

/-!
# De Finetti's theorem: exchangeable sequences are mixtures of i.i.d. sequences

The joint law of an exchangeable sequence of random variables in a standard Borel space `E` is a
mixture of laws of independent and identically distributed sequences: there is a probability
measure `Λ` on the probability measures on `E` such that the law of the sequence is
`Λ.bind fun m ↦ Measure.infinitePi fun _ ↦ m`. The mixing measure is the law of the conditional
distribution of the first variable given the tail σ-algebra.

## Main results

* `ProbabilityTheory.Exchangeable.exists_probabilityMeasure_map_eq_bind_infinitePi`: de Finetti's
  theorem, with a mixing measure on the probability measures on `E`.
* `ProbabilityTheory.Exchangeable.exists_kernel_map_eq_bind_infinitePi`: the same with the
  mixture given by a Markov kernel on the space of sequences.
* `ProbabilityTheory.Exchangeable.condExp_finsetProd_ae_eq`: the conditional product formula for
  a product over any finite set of indices.

## References

* [kallenberg-2005]

## Tags

exchangeable, de Finetti, mixture, directing random measure
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {μ : Measure Ω}
  {X : ℕ → Ω → E}

/-- The conditional product formula over a finset of indices. -/
theorem Exchangeable.condExp_finsetProd_ae_eq [IsFiniteMeasure μ] (h : Exchangeable X μ)
    (hX : ∀ i, Measurable (X i)) (s : Finset ℕ) (f : ℕ → E → ℝ) (hf : ∀ i, Measurable (f i))
    (hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C) :
    μ[fun ω ↦ ∏ i ∈ s, f i (X i ω) |
        limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop] =ᵐ[μ]
      fun ω ↦ ∏ i ∈ s, (μ[f i ∘ X 0 |
        limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop]) ω := by
  classical
  have hm : limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ≤ mΩ :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (hX n).comap_le)
  obtain ⟨n, hn⟩ : ∃ n, s ⊆ Finset.range n :=
    ⟨s.sup id + 1, fun i hi ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  have hprod (F : ℕ → ℝ) : ∏ i : Fin n, (if (i : ℕ) ∈ s then F i else 1) = ∏ i ∈ s, F i := by
    rw [Fin.prod_univ_eq_prod_range (fun i ↦ if i ∈ s then F i else 1), Finset.prod_ite_mem,
      Finset.inter_eq_right.2 hn]
  let g : ℕ → E → ℝ := fun i ↦ if i ∈ s then f i else 1
  have key := h.condExp_prod_ae_eq hX n (fun i ↦ g i) (fun i ↦ by
      by_cases hi : (i : ℕ) ∈ s <;> simp [g, hi, hf, measurable_one])
    (fun i ↦ by
      by_cases hi : (i : ℕ) ∈ s
      · simpa [g, hi] using hfb i
      · exact ⟨1, by simp [g, hi]⟩)
  have hl : (fun ω ↦ ∏ i : Fin n, g i (X i ω)) = fun ω ↦ ∏ i ∈ s, f i (X i ω) := by
    ext ω
    rw [← hprod]
    congr 1 with i
    by_cases hi : (i : ℕ) ∈ s <;> simp [g, hi]
  have hr (ω : Ω) : ∏ i : Fin n, (μ[g i ∘ X 0 |
      limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop]) ω =
      ∏ i ∈ s, (μ[f i ∘ X 0 |
        limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop]) ω := by
    rw [← hprod]
    congr 1 with i
    by_cases hi : (i : ℕ) ∈ s
    · simp [g, hi]
    · simp only [g, hi, ite_false]
      rw [show (1 : E → ℝ) ∘ X 0 = fun _ ↦ (1 : ℝ) from rfl, condExp_const hm]
  rw [hl] at key
  exact key.trans (.of_forall hr)

/-- The tail σ-algebra of the coordinates of `ℕ → E`. -/
private abbrev pathTail (E : Type*) [MeasurableSpace E] : MeasurableSpace (ℕ → E) :=
  limsup (fun n ↦ MeasurableSpace.comap (fun x : ℕ → E ↦ x n) inferInstance) atTop

/-- **De Finetti's theorem**, mixture form on the path space: an exchangeable probability measure
on sequences in a standard Borel space is a mixture of laws of independent and identically
distributed sequences. -/
theorem exists_kernel_eq_bind_infinitePi [StandardBorelSpace E] {μ : Measure (ℕ → E)}
    [IsProbabilityMeasure μ] (h : Exchangeable (fun i (x : ℕ → E) ↦ x i) μ) :
    ∃ (ν : Kernel (ℕ → E) E) (_ : IsMarkovKernel ν),
      μ = μ.bind fun x ↦ Measure.infinitePi fun _ : ℕ ↦ ν x := by
  have h𝓣 : pathTail E ≤ MeasurableSpace.pi :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (measurable_pi_apply n).comap_le)
  let ν : Kernel (ℕ → E) E :=
    ((condExpKernel μ (pathTail E)).comap id (measurable_id'' h𝓣)).map fun y ↦ y 0
  have hνM : IsMarkovKernel ν := Kernel.IsMarkovKernel.map _ (measurable_pi_apply 0)
  have hν (x : ℕ → E) {A : Set E} (hA : MeasurableSet A) :
      ν x A = condExpKernel μ (pathTail E) x ((fun y : ℕ → E ↦ y 0) ⁻¹' A) := by
    rw [Kernel.map_apply' _ (measurable_pi_apply 0) _ hA, Kernel.comap_apply, id]
  have hpi := isPiSystem_squareCylinders (α := fun _ : ℕ ↦ E)
    (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) fun _ ↦ MeasurableSet.univ
  have hF : Measurable fun x ↦ Measure.infinitePi fun _ : ℕ ↦ ν x := by
    refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_squareCylinders.symm hpi ?_
    rintro _ ⟨s, t, ht, rfl⟩
    simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
    simp_rw [Measure.infinitePi_pi _ fun i _ ↦ ht i]
    exact Finset.measurable_prod _ fun i _ ↦ ν.measurable_coe (ht i)
  refine ⟨ν, hνM, ?_⟩
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm hpi ?_ ?_
  · rintro _ ⟨s, t, ht, rfl⟩
    simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
    rw [Measure.bind_apply (.pi s.countable_toSet fun i _ ↦ ht i) hF.aemeasurable]
    simp_rw [Measure.infinitePi_pi _ fun i _ ↦ ht i]
    have hS : MeasurableSet ((s : Set ℕ).pi t) := .pi s.countable_toSet fun i _ ↦ ht i
    have hm : Measurable fun x ↦ ∏ i ∈ s, ν x (t i) :=
      Finset.measurable_prod _ fun i _ ↦ ν.measurable_coe (ht i)
    have hfin : ∫⁻ x, ∏ i ∈ s, ν x (t i) ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top μ Set.univ) <|
        (lintegral_mono fun x ↦ Finset.prod_le_one fun i _ ↦ prob_le_one).trans_eq lintegral_one
    have hb (i : ℕ) : ∃ C, ∀ y, |(t i).indicator (1 : E → ℝ) y| ≤ C :=
      ⟨1, fun y ↦ by by_cases hy : y ∈ t i <;> simp [hy]⟩
    rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin, ← measureReal_def,
      ← integral_indicator_one hS, ← integral_toReal hm.aemeasurable
        (ae_of_all _ fun x ↦ ENNReal.prod_lt_top fun i _ ↦ measure_lt_top _ _)]
    simp_rw [Set.indicator_pi_one_apply, ENNReal.toReal_prod]
    rw [← integral_condExp h𝓣]
    refine integral_congr_ae ?_
    filter_upwards [h.condExp_finsetProd_ae_eq measurable_pi_apply s (fun i ↦ (t i).indicator 1)
      (fun i ↦ measurable_one.indicator (ht i)) hb,
      ae_all_iff.2 fun i ↦ condExpKernel_ae_eq_condExp h𝓣 (measurable_pi_apply 0 (ht i))]
      with x hx hκ
    refine hx.trans (Finset.prod_congr rfl fun i _ ↦ ?_)
    rw [hν x (ht i), ← measureReal_def, hκ i]
    rfl
  · rw [Measure.bind_apply .univ hF.aemeasurable]
    simp

/-- **De Finetti's theorem**, mixture form: the joint law of an exchangeable sequence of random
variables in a standard Borel space is a mixture of laws of independent and identically
distributed sequences. -/
theorem Exchangeable.exists_kernel_map_eq_bind_infinitePi [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (h : Exchangeable X μ) :
    ∃ (ν : Kernel (ℕ → E) E) (_ : IsMarkovKernel ν),
      μ.map (fun ω i ↦ X i ω) =
        (μ.map fun ω i ↦ X i ω).bind fun x ↦ Measure.infinitePi fun _ : ℕ ↦ ν x :=
  have := (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 ‹IsProbabilityMeasure μ›
  exists_kernel_eq_bind_infinitePi ((exchangeable_iff_exchangeable_eval_map h.aemeasurable).1 h)

/-- The law of an independent and identically distributed sequence depends measurably on the
law of its terms. -/
theorem measurable_infinitePi_const (ι : Type*) :
    Measurable fun m : ProbabilityMeasure E ↦ Measure.infinitePi fun _ : ι ↦ (m : Measure E) := by
  have hpi := isPiSystem_squareCylinders (α := fun _ : ι ↦ E)
    (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) fun _ ↦ MeasurableSet.univ
  refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_squareCylinders.symm hpi ?_
  rintro _ ⟨s, t, ht, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
  simp_rw [Measure.infinitePi_pi _ fun i _ ↦ ht i]
  exact Finset.measurable_prod _ fun i _ ↦
    (Measure.measurable_coe (ht i)).comp measurable_subtype_coe

/-- **De Finetti's theorem**: the joint law of an exchangeable sequence of random variables in a
standard Borel space is a mixture of laws of independent and identically distributed sequences. -/
theorem Exchangeable.exists_probabilityMeasure_map_eq_bind_infinitePi [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (h : Exchangeable X μ) :
    ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
      μ.map (fun ω i ↦ X i ω) =
        Λ.bind fun m ↦ Measure.infinitePi fun _ : ℕ ↦ (m : Measure E) := by
  obtain ⟨ν, hν, hmix⟩ := h.exists_kernel_map_eq_bind_infinitePi
  let g : (ℕ → E) → ProbabilityMeasure E := fun x ↦ ⟨ν x, inferInstance⟩
  have hg : Measurable g := Measurable.subtype_mk ν.measurable
  have := (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 ‹IsProbabilityMeasure μ›
  refine ⟨(μ.map fun ω i ↦ X i ω).map g,
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance, ?_⟩
  exact hmix.trans
    (Measure.bind_map hg.aemeasurable (measurable_infinitePi_const ℕ).aemeasurable).symm

end ProbabilityTheory
