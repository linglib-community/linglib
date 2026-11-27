/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Probability.Exchangeable.Mixture
public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.StrongLaw

/-!
# De Finetti's theorem

For an infinite sequence `X` of random variables in a standard Borel space `E`, the following are
equivalent:

* `X` is exchangeable;
* `X` is contractable;
* `X` is mixed i.i.d.: its law is `Kernel.iid ℕ E ∘ₘ Λ` for a probability measure `Λ` on the
  probability measures on `E`;
* `X` is conditionally i.i.d.: there is a random probability measure `η` on `E` such that the
  conditional distribution of `X` given `η` is the kernel `Kernel.iid ℕ E`.

The random measure `η` is almost surely unique. It is the *directing random measure* of `X`, the
conditional law of `X 0` given the tail σ-algebra.

## Main definitions

* `ProbabilityTheory.Kernel.iid ι E`: the kernel sending a probability measure `m` on `E` to the
  law of an independent family of random variables with law `m`.
* `ProbabilityTheory.directingMeasure X μ`: the directing random measure of `X`.

## Main results

* `ProbabilityTheory.exchangeable_tfae`: the four conditions are equivalent.
* `ProbabilityTheory.Contractable.hasCondDistrib_directingMeasure`: given its directing random
  measure, a contractable sequence is conditionally i.i.d.
* `ProbabilityTheory.HasCondDistrib.ae_eq_of_iid`: the directing random measure is almost surely
  unique.

## Implementation notes

The directing random measure is defined from the tail σ-algebra
`limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop`. The shift-invariant σ-algebra
gives the same random measure almost surely for a contractable sequence.

## References

* [kallenberg-2021]
* [kallenberg-2005]

## Tags

exchangeable, contractable, de Finetti, directing random measure, mixed i.i.d.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {μ : Measure Ω}
  {X : ℕ → Ω → E}

/-- The kernel sending a probability measure `m` to the law `m^∞` of an i.i.d. sequence of
random variables with law `m`. -/
noncomputable def Kernel.iid (ι E : Type*) [MeasurableSpace E] :
    Kernel (ProbabilityMeasure E) (ι → E) where
  toFun m := Measure.infinitePi fun _ : ι ↦ (m : Measure E)
  measurable' := measurable_infinitePi_const ι

instance (ι : Type*) : IsMarkovKernel (Kernel.iid ι E) := ⟨fun _ ↦ by
  rw [Kernel.iid]; exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))⟩

/-- The directing random measure of a sequence: the conditional law of its first term given the
tail σ-algebra. -/
noncomputable def directingMeasure [StandardBorelSpace E] [Nonempty E] (X : ℕ → Ω → E)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Ω → ProbabilityMeasure E := fun ω ↦
  ⟨@condDistrib Ω Ω E _ _ _ mΩ
    (limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ⊓ mΩ) (X 0) id μ _ ω,
    inferInstance⟩

/-- The directing random measure is measurable for the tail σ-algebra, intersected with the
ambient one. -/
private theorem measurable_directingMeasure_inf [StandardBorelSpace E] [Nonempty E]
    [IsFiniteMeasure μ] :
    Measurable[limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ⊓ mΩ]
      (directingMeasure X μ) :=
  (Kernel.measurable _).subtype_mk

/-- The directing random measure of a sequence is measurable. -/
theorem measurable_directingMeasure [StandardBorelSpace E] [Nonempty E] [IsFiniteMeasure μ] :
    Measurable (directingMeasure X μ) :=
  measurable_directingMeasure_inf.mono inf_le_right le_rfl

/-- The mass that the directing random measure gives a measurable set is a version of the
conditional probability of that set for the first term, given the tail. -/
private theorem directingMeasure_ae_eq_condExp [StandardBorelSpace E] [Nonempty E]
    [IsFiniteMeasure μ] (hX : ∀ i, Measurable (X i)) {t : Set E} (ht : MeasurableSet t) :
    (fun ω ↦ (directingMeasure X μ ω : Measure E).real t) =ᵐ[μ]
      μ⟦X 0 ⁻¹' t | limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop⟧ := by
  have h𝓣 : limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ≤ mΩ :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (hX n).comap_le)
  have := condDistrib_ae_eq_condExp (μ := μ) (Y := X 0) (X := id)
    (mβ := limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ⊓ mΩ)
    (measurable_id'' inf_le_right) (hX 0) ht
  rw [MeasurableSpace.comap_id] at this
  rw [← inf_eq_left.2 h𝓣]
  exact this

/-- Given its directing random measure `η`, a contractable sequence is conditionally i.i.d. with
law `η` ([kallenberg-2021] Theorem 27.2). -/
theorem Contractable.hasCondDistrib_directingMeasure [StandardBorelSpace E] [Nonempty E]
    [IsProbabilityMeasure μ] (h : Contractable X μ) (hX : ∀ i, Measurable (X i)) :
    HasCondDistrib (fun ω i ↦ X i ω) (directingMeasure X μ) (Kernel.iid ℕ E) μ := by
  have h𝓣 : limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop ≤ mΩ :=
    limsup_le_iSup.trans (iSup_le fun n ↦ (hX n).comap_le)
  have hJ : Measurable fun ω i ↦ X i ω := .of_eval hX
  have hη : Measurable (directingMeasure X μ) := measurable_directingMeasure
  have hη𝓣 : Measurable[limsup (fun n ↦ MeasurableSpace.comap (X n) inferInstance) atTop]
      (directingMeasure X μ) := measurable_directingMeasure_inf.mono inf_le_left le_rfl
  refine ⟨(hη.prodMk hJ).aemeasurable, ?_⟩
  have := (Measure.isProbabilityMeasure_map_iff (hη.prodMk hJ).aemeasurable).2 ‹_›
  have := (Measure.isProbabilityMeasure_map_iff hη.aemeasurable).2 ‹IsProbabilityMeasure μ›
  have hpi := isPiSystem_squareCylinders (α := fun _ : ℕ ↦ E)
    (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) fun _ ↦ MeasurableSet.univ
  refine ext_of_generate_finite _ (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
    generateFrom_squareCylinders isCountablySpanning_measurableSet ?_).symm
    (MeasurableSpace.isPiSystem_measurableSet.prod hpi) ?_ (by simp)
  · exact ⟨fun _ ↦ Set.univ, fun _ ↦ ⟨∅, fun _ ↦ Set.univ, by simp, by simp⟩, Set.iUnion_const _⟩
  rintro _ ⟨A, hA, _, ⟨s, t, ht, rfl⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
  have hB : MeasurableSet ((s : Set ℕ).pi t) := .pi s.countable_toSet fun i _ ↦ ht i
  have e (ω : Ω) : Kernel.iid ℕ E (directingMeasure X μ ω) ((s : Set ℕ).pi t) =
      ∏ i ∈ s, (directingMeasure X μ ω : Measure E) (t i) :=
    Measure.infinitePi_pi _ fun i _ ↦ ht i
  rw [Measure.map_apply (hη.prodMk hJ) (hA.prod hB), Set.mk_preimage_prod,
    Measure.compProd_apply_prod hA hB, setLIntegral_map hA (Kernel.measurable_coe _ hB) hη]
  simp only [e]
  have hm : Measurable fun ω ↦ ∏ i ∈ s, (directingMeasure X μ ω : Measure E) (t i) :=
    Finset.measurable_prod _ fun i _ ↦
      (Measure.measurable_coe (ht i)).comp (measurable_subtype_coe.comp hη)
  have hfin : ∫⁻ ω in directingMeasure X μ ⁻¹' A,
      ∏ i ∈ s, (directingMeasure X μ ω : Measure E) (t i) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (lintegral_mono fun ω ↦ Finset.prod_le_one fun i _ ↦ prob_le_one)
  have hb (i : ℕ) (x : E) : |(t i).indicator (1 : E → ℝ) x| ≤ 1 := by
    by_cases hx : x ∈ t i <;> simp [hx]
  have e2 (i : ℕ) : (t i).indicator (1 : E → ℝ) ∘ X 0 = (X 0 ⁻¹' t i).indicator fun _ ↦ 1 := by
    funext ω
    by_cases hω : X 0 ω ∈ t i <;> simp [hω]
  have hF : ((fun ω i ↦ X i ω) ⁻¹' (s : Set ℕ).pi t).indicator (1 : Ω → ℝ) =
      fun ω ↦ ∏ i ∈ s, (t i).indicator 1 (X i ω) :=
    funext fun ω ↦ Set.indicator_pi_one_apply s t (fun i ↦ X i ω)
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin, ← measureReal_def,
    ← integral_toReal hm.aemeasurable
      (ae_of_all _ fun ω ↦ ENNReal.prod_lt_top fun i _ ↦ measure_lt_top _ _),
    Set.inter_comm, ← measureReal_restrict_apply (hJ hB), ← integral_indicator_one (hJ hB),
    ← setIntegral_condExp (f := ((fun ω i ↦ X i ω) ⁻¹' (s : Set ℕ).pi t).indicator 1) h𝓣
      ((integrable_const 1).indicator (hJ hB)) (hη𝓣 hA)]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  rw [hF]
  refine (h.condExp_finsetProd_ae_eq hX s (fun i ↦ (t i).indicator 1)
    (fun i ↦ measurable_one.indicator (ht i)) (fun _ ↦ 1) hb).trans ?_
  filter_upwards [(eventually_all_finset s).2 fun i _ ↦ directingMeasure_ae_eq_condExp hX (ht i)]
    with ω hω
  simp only [ENNReal.toReal_prod, ← measureReal_def]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [hω i hi, e2]

/-- **De Finetti's theorem**: for a sequence in a standard Borel space, being exchangeable,
contractable, mixed i.i.d., and conditionally i.i.d. given a random distribution are equivalent
([kallenberg-2021] Theorem 27.2). -/
theorem exchangeable_tfae [StandardBorelSpace E] [IsProbabilityMeasure μ]
    (hX : ∀ i, Measurable (X i)) :
    List.TFAE [
      Exchangeable X μ,
      Contractable X μ,
      ∃ Λ : Measure (ProbabilityMeasure E), IsProbabilityMeasure Λ ∧
        HasLaw (fun ω i ↦ X i ω) (Kernel.iid ℕ E ∘ₘ Λ) μ,
      ∃ η : Ω → ProbabilityMeasure E, Measurable η ∧
        HasCondDistrib (fun ω i ↦ X i ω) η (Kernel.iid ℕ E) μ] := by
  have hJ : Measurable fun ω i ↦ X i ω := .of_eval hX
  tfae_have 1 ↔ 2 := (contractable_iff_exchangeable hX).symm
  tfae_have 1 → 3 := fun h ↦
    let ⟨Λ, hΛ, hmix⟩ := h.exists_probabilityMeasure_map_eq_bind_infinitePi
    ⟨Λ, hΛ, hJ.aemeasurable, hmix⟩
  tfae_have 3 → 1 := fun ⟨_, _, h⟩ ↦ exchangeable_of_map_eq_bind hJ.aemeasurable h.map_eq
  tfae_have 2 → 4 := fun h ↦ by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
    have : Nonempty E := ⟨X 0 ω⟩
    exact ⟨directingMeasure X μ, measurable_directingMeasure,
      h.hasCondDistrib_directingMeasure hX⟩
  tfae_have 4 → 3 := fun ⟨η, hη, h⟩ ↦ by
    refine ⟨μ.map η, (Measure.isProbabilityMeasure_map_iff hη.aemeasurable).2 ‹_›,
      hJ.aemeasurable, ?_⟩
    rw [← Measure.snd_compProd, ← h.map_eq, Measure.snd_map_prodMk₀ hη.aemeasurable hJ.aemeasurable]
  tfae_finish

/-- Under the law of an i.i.d. sequence with law `m`, the frequency of visits to a measurable set
converges almost surely to its `m`-mass. -/
private theorem ae_tendsto_average_indicator_infinitePi (m : ProbabilityMeasure E) {B : Set E}
    (hB : MeasurableSet B) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ ↦ (m : Measure E)),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, B.indicator (1 : E → ℝ) (x i))
        atTop (𝓝 ((m : Measure E).real B)) := by
  have hf : Measurable (B.indicator (1 : E → ℝ)) := measurable_one.indicator hB
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ ↦ (m : Measure E)) fun _ ↦ hf
  have hid (i : ℕ) : IdentDistrib (fun x : ℕ → E ↦ B.indicator (1 : E → ℝ) (x i))
      (fun x ↦ B.indicator 1 (x 0)) (Measure.infinitePi fun _ : ℕ ↦ (m : Measure E))
      (Measure.infinitePi fun _ : ℕ ↦ (m : Measure E)) :=
    have h : IdentDistrib (fun x : ℕ → E ↦ x i) (fun x ↦ x 0)
        (Measure.infinitePi fun _ : ℕ ↦ (m : Measure E))
        (Measure.infinitePi fun _ : ℕ ↦ (m : Measure E)) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        by rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩
    h.comp hf
  have hint : Integrable (fun x : ℕ → E ↦ B.indicator (1 : E → ℝ) (x 0))
      (Measure.infinitePi fun _ : ℕ ↦ (m : Measure E)) :=
    .of_bound (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by by_cases hx : x 0 ∈ B <;> simp [hx])
  have hlim : ∫ x, B.indicator (1 : E → ℝ) (x 0) ∂(Measure.infinitePi fun _ : ℕ ↦ (m : Measure E))
      = (m : Measure E).real B := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable,
      Measure.infinitePi_map_eval, integral_indicator_one hB]
  have := strong_law_ae (fun i (x : ℕ → E) ↦ B.indicator (1 : E → ℝ) (x i)) hint
    (fun i j hij ↦ hind.indepFun hij) hid
  rwa [hlim] at this

/-- Given a random distribution `η` under which a sequence is conditionally i.i.d., the frequency
of visits of the sequence to a measurable set converges almost surely to its `η`-mass. -/
private theorem HasCondDistrib.ae_tendsto_average_indicator {η : Ω → ProbabilityMeasure E}
    (h : HasCondDistrib (fun ω i ↦ X i ω) η (Kernel.iid ℕ E) μ) [SFinite μ] {B : Set E}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, B.indicator (1 : E → ℝ) (X i ω))
      atTop (𝓝 ((η ω : Measure E).real B)) := by
  have hf : Measurable (B.indicator (1 : E → ℝ)) := measurable_one.indicator hB
  have hS : MeasurableSet {p : ProbabilityMeasure E × (ℕ → E) | Tendsto
      (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, B.indicator (1 : E → ℝ) (p.2 i) -
        (p.1 : Measure E).real B) atTop (𝓝 0)} :=
    measurableSet_tendsto _ fun n ↦ by
      have h1 : Measurable fun p : ProbabilityMeasure E × (ℕ → E) ↦ (p.1 : Measure E).real B :=
        ((Measure.measurable_coe hB).comp
          (measurable_subtype_coe.comp measurable_fst)).ennreal_toReal
      have h2 : Measurable fun p : ProbabilityMeasure E × (ℕ → E) ↦
          (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, B.indicator (1 : E → ℝ) (p.2 i) := by fun_prop
      exact h2.sub h1
  have := (h.ae_iff (measurableSet_setOfPred.1 hS)).2 ((Measure.ae_compProd_iff hS).2
    (ae_of_all _ fun m ↦ (ae_tendsto_average_indicator_infinitePi m hB).mono fun x hx ↦
      tendsto_sub_nhds_zero_iff.2 hx))
  exact this.mono fun ω hω ↦ tendsto_sub_nhds_zero_iff.1 hω

/-- Two random probability measures on a countably generated space are almost everywhere equal
as soon as, set by set, they almost everywhere give the set the same mass. -/
private theorem ae_eq_of_forall_ae_measureReal_eq [MeasurableSpace.CountablyGenerated E]
    {η₁ η₂ : Ω → ProbabilityMeasure E}
    (h : ∀ B : Set E, MeasurableSet B →
      ∀ᵐ ω ∂μ, (η₁ ω : Measure E).real B = (η₂ ω : Measure E).real B) :
    η₁ =ᵐ[μ] η₂ := by
  let g := MeasurableSpace.natGeneratingSequence E
  let C : Finset ℕ → Set E := fun P ↦ ⋂ i ∈ P, g i
  have hC (P : Finset ℕ) : MeasurableSet (C P) :=
    Finset.measurableSet_biInter _ fun i _ ↦ MeasurableSpace.measurableSet_natGeneratingSequence i
  have hpi : IsPiSystem (Set.range C) := by
    rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ _
    exact ⟨P ∪ Q, Finset.set_biInter_inter P Q g⟩
  have hgen : (inferInstance : MeasurableSpace E) = MeasurableSpace.generateFrom (Set.range C) := by
    refine le_antisymm ((MeasurableSpace.generateFrom_natGeneratingSequence E).symm.trans_le
      (MeasurableSpace.generateFrom_le ?_)) (MeasurableSpace.generateFrom_le ?_)
    · rintro _ ⟨j, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom ⟨{j}, by simp [C, g]⟩
    · rintro _ ⟨P, rfl⟩
      exact hC P
  filter_upwards [ae_all_iff.2 fun P ↦ h (C P) (hC P)] with ω hω
  refine ProbabilityMeasure.toMeasure_injective (ext_of_generate_finite _ hgen hpi ?_ (by simp))
  rintro _ ⟨P, rfl⟩
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (hω P)

/-- A random distribution given which a sequence is conditionally i.i.d. is almost surely unique
([kallenberg-2021] Theorem 27.2). -/
theorem HasCondDistrib.ae_eq_of_iid [StandardBorelSpace E] [IsProbabilityMeasure μ]
    {η₁ η₂ : Ω → ProbabilityMeasure E}
    (h₁ : HasCondDistrib (fun ω i ↦ X i ω) η₁ (Kernel.iid ℕ E) μ)
    (h₂ : HasCondDistrib (fun ω i ↦ X i ω) η₂ (Kernel.iid ℕ E) μ) : η₁ =ᵐ[μ] η₂ :=
  ae_eq_of_forall_ae_measureReal_eq fun _ hB ↦ by
    filter_upwards [h₁.ae_tendsto_average_indicator hB, h₂.ae_tendsto_average_indicator hB]
      with ω h₁ω h₂ω
    exact tendsto_nhds_unique h₁ω h₂ω

end ProbabilityTheory
