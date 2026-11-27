/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Conditional expectations and equality in law

If the pairs `(ξ, η)` and `(ξ, ζ)` have the same law and `η` is a function of `ζ`, then
conditioning a bounded function of `ξ` on `ζ` gives the same result as conditioning it on `η`:
the extra information in `ζ` is of no use for predicting `ξ`.

## Main results

* `MeasureTheory.condExp_comap_ae_eq_of_map_prodMk_eq`: the statement above.
* `MeasureTheory.integral_condExp_mul_of_bound`: against a bounded weight measurable for the
  conditioning σ-algebra, a function and its conditional expectation have the same integral.

## References

* [kallenberg-2005]
-/

public section

open Filter

namespace MeasureTheory

variable {Ω S T : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S] [MeasurableSpace T]
  {μ : Measure Ω}

/-- Against a bounded `m`-measurable weight, a function and its conditional expectation given `m`
have the same integral. -/
theorem integral_condExp_mul_of_bound {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {g w : Ω → ℝ} (hg : Integrable g μ) (hw : StronglyMeasurable[m] w)
    {c : ℝ} (hwc : ∀ ω, |w ω| ≤ c) :
    ∫ ω, μ[g | m] ω * w ω ∂μ = ∫ ω, g ω * w ω ∂μ := by
  have h := condExp_stronglyMeasurable_mul_of_bound hm hw hg c (ae_of_all _ hwc)
  calc ∫ ω, μ[g | m] ω * w ω ∂μ = ∫ ω, μ[w * g | m] ω ∂μ :=
        integral_congr_ae (h.mono fun ω hω ↦ by rw [hω, Pi.mul_apply, mul_comm])
    _ = ∫ ω, g ω * w ω ∂μ := by
        rw [integral_condExp hm]
        exact integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm (w ω) (g ω))

/-- If `(ξ, η)` and `(ξ', ζ)` have the same law, then integrating a function of the pair over the
event `η ∈ B` or `ζ ∈ B` gives the same result. -/
theorem setIntegral_preimage_snd_eq_of_map_prodMk_eq {ξ ξ' : Ω → S} {η ζ : Ω → T}
    (hξ : Measurable ξ) (hξ' : Measurable ξ') (hη : Measurable η) (hζ : Measurable ζ)
    (h : μ.map (fun ω ↦ (ξ ω, η ω)) = μ.map fun ω ↦ (ξ' ω, ζ ω))
    {F : S × T → ℝ} (hF : Measurable F) {B : Set T} (hB : MeasurableSet B) :
    ∫ ω in η ⁻¹' B, F (ξ ω, η ω) ∂μ = ∫ ω in ζ ⁻¹' B, F (ξ' ω, ζ ω) ∂μ := by
  have hs : MeasurableSet ((Set.univ : Set S) ×ˢ B) := MeasurableSet.univ.prod hB
  have h1 := setIntegral_map hs hF.aestronglyMeasurable (hξ.prodMk hη).aemeasurable (μ := μ)
  have h2 := setIntegral_map hs hF.aestronglyMeasurable (hξ'.prodMk hζ).aemeasurable (μ := μ)
  rw [h] at h1
  simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter] at h1 h2
  rw [← h1, h2]

/-- If `(ξ, η)` and `(ξ, ζ)` have the same law and `σ(η) ≤ σ(ζ)`, then conditioning a bounded
function of `ξ` on `ζ` gives the same result as conditioning it on `η`
([kallenberg-2005] Lemma 1.3). -/
theorem condExp_comap_ae_eq_of_map_prodMk_eq [IsFiniteMeasure μ] {ξ : Ω → S} {η ζ : Ω → T}
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (h : μ.map (fun ω ↦ (ξ ω, η ω)) = μ.map fun ω ↦ (ξ ω, ζ ω))
    (hle : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    {f : S → ℝ} (hf : Measurable f) (hfb : ∃ C, ∀ s, |f s| ≤ C) :
    μ[f ∘ ξ | MeasurableSpace.comap ζ inferInstance] =ᵐ[μ]
      μ[f ∘ ξ | MeasurableSpace.comap η inferInstance] := by
  obtain ⟨C, hC0, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ s, |f s| ≤ C :=
    let ⟨C, hC⟩ := hfb; ⟨|C|, abs_nonneg C, fun s ↦ (hC s).trans (le_abs_self C)⟩
  set G := MeasurableSpace.comap η inferInstance
  set H := MeasurableSpace.comap ζ inferInstance
  have hG : G ≤ mΩ := hη.comap_le
  have hH : H ≤ mΩ := hζ.comap_le
  have hint : Integrable (f ∘ ξ) μ :=
    .of_bound (hf.comp hξ).aestronglyMeasurable C (ae_of_all _ fun ω ↦ hC (ξ ω))
  have htr (F : S × T → ℝ) (hF : Measurable F) {B : Set T} (hB : MeasurableSet B) :=
    setIntegral_preimage_snd_eq_of_map_prodMk_eq hξ hξ hη hζ h hF hB
  obtain ⟨φ, hφ, hUφ⟩ :=
    (stronglyMeasurable_condExp (f := f ∘ ξ) (m := H) (μ := μ)).exists_eq_measurable_comp
  let ψ : T → ℝ := fun t ↦ max (-C) (min C (φ t))
  have hψm : Measurable ψ := measurable_const.max (measurable_const.min hφ.measurable)
  have hψR (t : T) : |ψ t| ≤ C :=
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hUψ : μ[f ∘ ξ | H] =ᵐ[μ] ψ ∘ ζ := by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := H) (f := f ∘ ξ)
      (ae_of_all μ fun ω ↦ hC (ξ ω))] with ω hω
    have e : μ[f ∘ ξ | H] ω = φ (ζ ω) := congrFun hUφ ω
    rw [e, abs_le] at hω
    simp only [e, Function.comp_apply, ψ, min_eq_right hω.2, max_eq_right hω.1]
  have hvG : StronglyMeasurable[G] (ψ ∘ η) :=
    (hψm.comp (comap_measurable η)).stronglyMeasurable
  have hu : Integrable (ψ ∘ ζ) μ :=
    .of_bound (hψm.comp hζ).aestronglyMeasurable _ (ae_of_all _ fun ω ↦ hψR (ζ ω))
  have hv : Integrable (ψ ∘ η) μ :=
    .of_bound (hψm.comp hη).aestronglyMeasurable _ (ae_of_all _ fun ω ↦ hψR (η ω))
  have hVψ : ψ ∘ η =ᵐ[μ] μ[f ∘ ξ | G] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hG hint (fun s _ _ ↦ hv.integrableOn)
      (fun s hs _ ↦ ?_) hvG.aestronglyMeasurable
    obtain ⟨B, hB, rfl⟩ := hs
    calc ∫ ω in η ⁻¹' B, ψ (η ω) ∂μ = ∫ ω in ζ ⁻¹' B, ψ (ζ ω) ∂μ :=
          htr (ψ ∘ Prod.snd) (hψm.comp measurable_snd) hB
      _ = ∫ ω in ζ ⁻¹' B, μ[f ∘ ξ | H] ω ∂μ :=
          setIntegral_congr_ae (hζ hB) (hUψ.mono fun ω hω _ ↦ hω.symm)
      _ = ∫ ω in ζ ⁻¹' B, f (ξ ω) ∂μ := setIntegral_condExp hH hint ⟨B, hB, rfl⟩
      _ = ∫ ω in η ⁻¹' B, f (ξ ω) ∂μ := (htr (f ∘ Prod.fst) (hf.comp measurable_fst) hB).symm
  refine hUψ.trans (EventuallyEq.trans ?_ hVψ)
  have hvb : ∀ᵐ ω ∂μ, ‖(ψ ∘ η) ω‖ ≤ C := ae_of_all _ fun ω ↦ hψR (η ω)
  have hub : ∀ᵐ ω ∂μ, ‖(ψ ∘ ζ) ω‖ ≤ C := ae_of_all _ fun ω ↦ hψR (ζ ω)
  have huv : ∫ ω, ψ (ζ ω) * ψ (η ω) ∂μ = ∫ ω, f (ξ ω) * ψ (η ω) ∂μ :=
    (integral_congr_ae (hUψ.mono fun ω hω ↦ congrArg (· * ψ (η ω)) hω.symm)).trans
      (integral_condExp_mul_of_bound hH hint (hvG.mono hle) fun ω ↦ hψR (η ω))
  have hvv : ∫ ω, ψ (η ω) * ψ (η ω) ∂μ = ∫ ω, f (ξ ω) * ψ (η ω) ∂μ :=
    (integral_congr_ae (hVψ.mono fun ω hω ↦ congrArg (· * ψ (η ω)) hω)).trans
      (integral_condExp_mul_of_bound hG hint hvG fun ω ↦ hψR (η ω))
  have huu : ∫ ω, ψ (ζ ω) * ψ (ζ ω) ∂μ = ∫ ω, ψ (η ω) * ψ (η ω) ∂μ := by
    simpa using (htr (fun p ↦ ψ p.2 * ψ p.2) (by fun_prop) MeasurableSet.univ).symm
  have huv' : Integrable (fun ω ↦ ψ (ζ ω) * ψ (η ω)) μ := hu.mul_bdd hv.aestronglyMeasurable hvb
  have huu' : Integrable (fun ω ↦ ψ (ζ ω) * ψ (ζ ω)) μ := hu.mul_bdd hu.aestronglyMeasurable hub
  have hvv' : Integrable (fun ω ↦ ψ (η ω) * ψ (η ω)) μ := hv.mul_bdd hv.aestronglyMeasurable hvb
  have hsq : ∫ ω, (ψ (ζ ω) - ψ (η ω)) ^ 2 ∂μ = 0 := by
    have e (ω : Ω) : (ψ (ζ ω) - ψ (η ω)) ^ 2 =
        ψ (ζ ω) * ψ (ζ ω) - 2 * (ψ (ζ ω) * ψ (η ω)) + ψ (η ω) * ψ (η ω) := by ring
    simp_rw [e]
    rw [integral_add ?_ hvv', integral_sub huu' (huv'.const_mul 2), integral_const_mul]
    · linarith
    · exact huu'.sub (huv'.const_mul 2)
  have hsq' : Integrable (fun ω ↦ (ψ (ζ ω) - ψ (η ω)) ^ 2) μ := by
    have e (ω : Ω) : (ψ (ζ ω) - ψ (η ω)) ^ 2 =
        ψ (ζ ω) * ψ (ζ ω) - 2 * (ψ (ζ ω) * ψ (η ω)) + ψ (η ω) * ψ (η ω) := by ring
    simp_rw [e]
    exact (huu'.sub (huv'.const_mul 2)).add hvv'
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) hsq').1 hsq] with ω hω
  simpa [sub_eq_zero] using hω

end MeasureTheory
