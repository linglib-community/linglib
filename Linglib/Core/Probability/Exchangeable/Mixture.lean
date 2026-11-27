/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.DeFinetti
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Condexp

/-!
# De Finetti's theorem: exchangeable sequences are mixtures of i.i.d. sequences

For a contractable probability measure on sequences in a standard Borel space, the conditional
law of the sequence given the tail σ-algebra is almost surely the law of an independent and
identically distributed sequence. Consequently the joint law of an exchangeable sequence is a
mixture of such laws, and conversely.

## Main results

* `ProbabilityTheory.Contractable.ae_condExpKernel_eq_infinitePi`: the conditional law given the
  tail.
* `ProbabilityTheory.exchangeable_iff_exists_probabilityMeasure_map_eq_bind_infinitePi`: a
  sequence is exchangeable if and only if its law is a mixture of laws of independent and
  identically distributed sequences.
* `ProbabilityTheory.Contractable.iCondIndepFun`: a contractable sequence is conditionally
  independent given its tail σ-algebra.
* `ProbabilityTheory.Exchangeable.exists_measure_real_eq_integral_pow_mul`: for sequences of
  zeros and ones, the probability of a pattern is `∫ θ ^ k * (1 - θ) ^ (n - k) ∂Λ` for a
  probability measure `Λ` on `[0, 1]`.

## References

* [kallenberg-2005]

## Tags

exchangeable, de Finetti, mixture, directing random measure
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory

section Mixture

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {μ : Measure Ω}
  {X : ℕ → Ω → E}

/-- Two families of finite measures on `ℕ → E`, for a countably generated `E`, are almost
everywhere equal as soon as, box by box, they almost everywhere give the box the same mass. -/
private theorem ae_eq_of_forall_ae_measureReal_pi_eq [MeasurableSpace.CountablyGenerated E]
    {α : Type*} {_ : MeasurableSpace α} {ν : Measure α} {κ η : α → Measure (ℕ → E)}
    (hκ : ∀ a, IsFiniteMeasure (κ a)) (hη : ∀ a, IsFiniteMeasure (η a))
    (h : ∀ (s : Finset ℕ) (t : ℕ → Set E), (∀ i, MeasurableSet (t i)) →
      ∀ᵐ a ∂ν, (κ a).real ((s : Set ℕ).pi t) = (η a).real ((s : Set ℕ).pi t)) :
    ∀ᵐ a ∂ν, κ a = η a := by
  classical
  let g := MeasurableSpace.natGeneratingSequence E
  let t : Finset (ℕ × ℕ) → ℕ → Set E := fun P i ↦ ⋂ p ∈ P.filter (·.1 = i), g p.2
  let B : Finset (ℕ × ℕ) → Set (ℕ → E) := fun P ↦ ((P.image Prod.fst : Finset ℕ) : Set ℕ).pi (t P)
  have ht (P : Finset (ℕ × ℕ)) (i : ℕ) : MeasurableSet (t P i) :=
    Finset.measurableSet_biInter _ fun p _ ↦ MeasurableSpace.measurableSet_natGeneratingSequence _
  have hB (P : Finset (ℕ × ℕ)) (x : ℕ → E) : x ∈ B P ↔ ∀ p ∈ P, x p.1 ∈ g p.2 := by
    simp only [B, t, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_iInter,
      Finset.mem_filter]
    constructor
    · exact fun hx p hp ↦ hx p.1 ⟨p, hp, rfl⟩ p ⟨hp, rfl⟩
    · rintro hx _ ⟨q, hq, rfl⟩ p ⟨hp, hpq⟩
      rw [← hpq]
      exact hx p hp
  have hpi : IsPiSystem (Set.range B) := by
    rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ _
    refine ⟨P ∪ Q, Set.ext fun x ↦ ?_⟩
    simp only [Set.mem_inter_iff, hB, Finset.forall_mem_union]
  have hgen : (MeasurableSpace.pi : MeasurableSpace (ℕ → E)) =
      MeasurableSpace.generateFrom (Set.range B) := by
    refine le_antisymm (iSup_le fun i ↦ ?_) (MeasurableSpace.generateFrom_le ?_)
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine (MeasurableSpace.generateFrom_natGeneratingSequence E).symm.trans_le
        (MeasurableSpace.generateFrom_le ?_)
      rintro _ ⟨j, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨{(i, j)}, Set.ext fun x ↦ ?_⟩
      simp [hB, g]
    · rintro _ ⟨P, rfl⟩
      exact MeasurableSet.pi (Finset.countable_toSet _) fun i _ ↦ ht P i
  filter_upwards [ae_all_iff.2 fun P ↦ h (P.image Prod.fst) (t P) (ht P)] with a ha
  have := hκ a
  have := hη a
  refine ext_of_generate_finite _ hgen hpi ?_ ?_
  · rintro _ ⟨P, rfl⟩
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (ha P)
  · have h0 := ha ∅
    simp only [Finset.image_empty, Finset.coe_empty, Set.empty_pi] at h0
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0

/-- Given the tail σ-algebra, the conditional law of the coordinates under a contractable law on
`ℕ → E`, for a standard Borel `E`, is almost surely the law of an independent sequence whose terms
all have the conditional law of the first coordinate (Kallenberg 2005, Theorem 1.1, equation
(2)). -/
theorem Contractable.ae_condExpKernel_eq_infinitePi [StandardBorelSpace E]
    {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]
    (h : Contractable (fun i (x : ℕ → E) ↦ x i) μ) :
    ∀ᵐ x ∂μ, condExpKernel μ
        (limsup (fun n ↦ MeasurableSpace.comap (fun x : ℕ → E ↦ x n) inferInstance) atTop) x =
      Measure.infinitePi fun _ : ℕ ↦ (condExpKernel μ
        (limsup (fun n ↦ MeasurableSpace.comap (fun x : ℕ → E ↦ x n) inferInstance) atTop) x).map
          fun y ↦ y 0 := by
  have h𝓣 : limsup (fun n ↦ MeasurableSpace.comap (fun x : ℕ → E ↦ x n) inferInstance) atTop ≤
      MeasurableSpace.pi :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (measurable_pi_apply n).comap_le)
  refine ae_eq_of_forall_ae_measureReal_pi_eq (fun x ↦ inferInstance) (fun x ↦ inferInstance)
    fun s t ht ↦ ?_
  have hS : MeasurableSet ((s : Set ℕ).pi t) := .pi s.countable_toSet fun i _ ↦ ht i
  have hb (i : ℕ) (y : E) : |(t i).indicator (1 : E → ℝ) y| ≤ 1 := by
    by_cases hy : y ∈ t i <;> simp [hy]
  filter_upwards [condExpKernel_ae_eq_condExp h𝓣 hS,
    h.condExp_finsetProd_ae_eq measurable_pi_apply s (fun i ↦ (t i).indicator 1)
      (fun i ↦ measurable_one.indicator (ht i)) (fun _ ↦ 1) hb,
    ae_all_iff.2 fun i ↦ condExpKernel_ae_eq_condExp h𝓣 (measurable_pi_apply 0 (ht i))]
    with x hκ hprod hκ0
  have e1 : ((s : Set ℕ).pi t).indicator (fun _ ↦ (1 : ℝ)) =
      fun ω : ℕ → E ↦ ∏ i ∈ s, (t i).indicator 1 (ω i) :=
    funext fun ω ↦ Set.indicator_pi_one_apply s t ω
  have e2 (i : ℕ) : (t i).indicator (1 : E → ℝ) ∘ (fun x : ℕ → E ↦ x 0) =
      ((fun f : ℕ → E ↦ f 0) ⁻¹' t i).indicator fun _ ↦ 1 := by
    funext ω
    by_cases hω : ω 0 ∈ t i <;> simp [hω]
  rw [hκ, e1, hprod, measureReal_def, Measure.infinitePi_pi _ fun i _ ↦ ht i, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [e2, ← hκ0 i, ← measureReal_def, map_measureReal_apply (measurable_pi_apply 0) (ht i)]

/-- The joint law of an exchangeable sequence of random variables in a standard Borel space is a
mixture of laws of independent and identically distributed sequences (Kallenberg 2005,
Theorem 1.1, equation (3)). -/
theorem Exchangeable.exists_probabilityMeasure_map_eq_bind_infinitePi [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (h : Exchangeable X μ) :
    ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
      μ.map (fun ω i ↦ X i ω) =
        Λ.bind fun m ↦ Measure.infinitePi fun _ : ℕ ↦ (m : Measure E) := by
  set P := μ.map fun ω i ↦ X i ω
  have : IsProbabilityMeasure P := (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 ‹_›
  have hc : Contractable (fun i (x : ℕ → E) ↦ x i) P :=
    ((exchangeable_iff_exchangeable_eval_map h.aemeasurable).1 h).contractable
  have h𝓣 : limsup (fun n ↦ MeasurableSpace.comap (fun x : ℕ → E ↦ x n) inferInstance) atTop ≤
      MeasurableSpace.pi :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (measurable_pi_apply n).comap_le)
  let ν : Kernel (ℕ → E) E :=
    ((condExpKernel P _).comap id (measurable_id'' h𝓣)).map fun y ↦ y 0
  have : IsMarkovKernel ν := Kernel.IsMarkovKernel.map _ (measurable_pi_apply 0)
  let g : (ℕ → E) → ProbabilityMeasure E := fun x ↦ ⟨ν x, inferInstance⟩
  have hg : Measurable g := Measurable.subtype_mk ν.measurable
  refine ⟨P.map g, (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 ‹_›, ?_⟩
  rw [Measure.bind_map hg.aemeasurable (measurable_infinitePi_const ℕ).aemeasurable]
  ext S hS
  rw [Measure.bind_apply hS (f := fun x ↦ Measure.infinitePi fun _ : ℕ ↦ (g x : Measure E))
    ((measurable_infinitePi_const ℕ).comp hg).aemeasurable]
  conv_lhs => rw [← condExpKernel_comp_trim (μ := P) h𝓣]
  rw [Measure.bind_apply hS (Kernel.measurable _).aemeasurable,
    lintegral_trim h𝓣 (Kernel.measurable_coe _ hS)]
  refine lintegral_congr_ae (hc.ae_condExpKernel_eq_infinitePi.mono fun x hx ↦ ?_)
  dsimp only
  rw [hx]
  simp [g, ν, Kernel.map_apply _ (measurable_pi_apply 0)]

/-- The joint law of a sequence of random variables in a standard Borel space is exchangeable if
and only if it is a mixture of laws of independent and identically distributed sequences
(Kallenberg 2005, Theorem 1.1). -/
theorem exchangeable_iff_exists_probabilityMeasure_map_eq_bind_infinitePi [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (hX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    Exchangeable X μ ↔ ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
      μ.map (fun ω i ↦ X i ω) = Λ.bind fun m ↦ Measure.infinitePi fun _ : ℕ ↦ (m : Measure E) :=
  ⟨Exchangeable.exists_probabilityMeasure_map_eq_bind_infinitePi,
    fun ⟨_, _, h⟩ ↦ exchangeable_of_map_eq_bind hX h⟩

/-- Given the tail σ-algebra, the terms of a contractable sequence of random variables are
conditionally independent (Kallenberg 2005, Theorem 1.1). -/
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
  obtain ⟨Λ₀, hΛ₀, hmix⟩ := h.exists_probabilityMeasure_map_eq_bind_infinitePi
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
