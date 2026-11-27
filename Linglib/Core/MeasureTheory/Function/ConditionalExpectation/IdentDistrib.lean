/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Probability.IdentDistrib

/-!
# Conditional expectations: decreasing σ-algebras and equality in law

Two facts about conditional expectations. If the conditional expectations of a function given
each member of a decreasing sequence of σ-algebras are almost everywhere equal, they are equal
to its conditional expectation given their intersection. If the pairs `(ξ, η)` and `(ξ, ζ)` are
identically distributed and `η` is a function of `ζ`, then conditioning a bounded function of `ξ`
on `ζ` gives the same result as conditioning it on `η`.

## Main results

* `MeasureTheory.condExp_ae_eq_condExp_iInf`: the statement for decreasing σ-algebras.
* `MeasureTheory.condExp_comap_ae_eq_of_identDistrib`: the statement for pairs with one law.

## References

* [kallenberg-2005]
-/

public section

namespace MeasureTheory

open Filter ProbabilityTheory

section CondExp

variable {Ω S T : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S] [MeasurableSpace T]
  {μ : Measure Ω}

/-- If the conditional expectations of `g` along a decreasing sequence of σ-algebras all agree,
they agree with the conditional expectation given the intersection. -/
theorem condExp_ae_eq_condExp_iInf [IsFiniteMeasure μ] {m : ℕ → MeasurableSpace Ω}
    (hm : Antitone m) (hm0 : m 0 ≤ mΩ) {g : Ω → ℝ}
    (h : ∀ n, μ[g | m n] =ᵐ[μ] μ[g | m 0]) : μ[g | m 0] =ᵐ[μ] μ[g | ⨅ n, m n] := by
  let U : ℕ → Ω → ℝ := fun n ↦ μ[g | m n]
  have hU : ∀ᵐ ω ∂μ, ∀ n, U n ω = U 0 ω := ae_all_iff.2 h
  let W : Ω → ℝ := fun ω ↦ limsup (fun n ↦ U n ω) atTop
  have hWU : W =ᵐ[μ] U 0 := hU.mono fun ω hω ↦ by
    have e : (fun n ↦ U n ω) = fun _ ↦ U 0 ω := funext hω
    simp only [W, e, limsup_const]
  have hWm : Measurable[⨅ n, m n] W := by
    intro B hB
    rw [MeasurableSpace.measurableSet_iInf]
    intro N
    have hN : Measurable[m N] fun ω ↦ limsup (fun n ↦ U (n + N) ω) atTop :=
      Measurable.limsup fun n ↦
        stronglyMeasurable_condExp.measurable.mono (hm (by omega)) le_rfl
    have e : W = fun ω ↦ limsup (fun n ↦ U (n + N) ω) atTop :=
      funext fun ω ↦ (limsup_nat_add (fun n ↦ U n ω) N).symm
    rw [e]
    exact hN hB
  have hle : (⨅ n, m n) ≤ m 0 := iInf_le _ _
  have hint : Integrable W μ := integrable_condExp.congr hWU.symm
  calc μ[g | m 0] =ᵐ[μ] W := hWU.symm
    _ = μ[W | ⨅ n, m n] := (condExp_of_stronglyMeasurable
        (hle.trans hm0) hWm.stronglyMeasurable hint).symm
    _ =ᵐ[μ] μ[U 0 | ⨅ n, m n] := condExp_congr_ae hWU
    _ =ᵐ[μ] μ[g | ⨅ n, m n] := condExp_condExp_of_le hle hm0

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

/-- If `(ξ, η)` and `(ξ', ζ)` are identically distributed, then integrating a function of the
pair over the event `η ∈ B` or `ζ ∈ B` gives the same result. -/
theorem setIntegral_preimage_snd_eq_of_identDistrib {ξ ξ' : Ω → S} {η ζ : Ω → T}
    (h : IdentDistrib (fun ω ↦ (ξ ω, η ω)) (fun ω ↦ (ξ' ω, ζ ω)) μ μ)
    {F : S × T → ℝ} (hF : Measurable F) {B : Set T} (hB : MeasurableSet B) :
    ∫ ω in η ⁻¹' B, F (ξ ω, η ω) ∂μ = ∫ ω in ζ ⁻¹' B, F (ξ' ω, ζ ω) ∂μ := by
  have hG : Measurable ((Prod.snd ⁻¹' B : Set (S × T)).indicator F) :=
    hF.indicator (measurable_snd hB)
  rw [← integral_indicator₀ (h.aemeasurable_fst.snd.nullMeasurableSet_preimage hB),
    ← integral_indicator₀ (h.aemeasurable_snd.snd.nullMeasurableSet_preimage hB)]
  exact (h.comp hG).integral_eq

/-- If `(ξ, η)` and `(ξ, ζ)` are identically distributed and `σ(η) ≤ σ(ζ)`, then conditioning a
bounded function of `ξ` on `ζ` gives the same result as conditioning it on `η`
([kallenberg-2005] Lemma 1.3). -/
theorem condExp_comap_ae_eq_of_identDistrib [IsFiniteMeasure μ] {ξ : Ω → S} {η ζ : Ω → T}
    (hζ : Measurable ζ) (h : IdentDistrib (fun ω ↦ (ξ ω, η ω)) (fun ω ↦ (ξ ω, ζ ω)) μ μ)
    (hle : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    {f : S → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ s, |f s| ≤ C) :
    μ[f ∘ ξ | MeasurableSpace.comap ζ inferInstance] =ᵐ[μ]
      μ[f ∘ ξ | MeasurableSpace.comap η inferInstance] := by
  obtain ⟨C, hC0, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ s, |f s| ≤ C :=
    ⟨|C|, abs_nonneg C, fun s ↦ (hC s).trans (le_abs_self C)⟩
  have hη : Measurable η := measurable_iff_comap_le.2 (hle.trans hζ.comap_le)
  have hint : Integrable (f ∘ ξ) μ :=
    .of_bound (hf.comp_aemeasurable h.aemeasurable_fst.fst).aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ hC (ξ ω))
  have htr (F : S × T → ℝ) (hF : Measurable F) {B : Set T} (hB : MeasurableSet B) :=
    setIntegral_preimage_snd_eq_of_identDistrib h hF hB
  have hid (F : S × T → ℝ) (hF : Measurable F) :
      ∫ ω, F (ξ ω, η ω) ∂μ = ∫ ω, F (ξ ω, ζ ω) ∂μ :=
    (h.comp hF).integral_eq
  set G := MeasurableSpace.comap η inferInstance
  set H := MeasurableSpace.comap ζ inferInstance
  have hH : H ≤ mΩ := hζ.comap_le
  have hG : G ≤ mΩ := hη.comap_le
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
  have huu : ∫ ω, ψ (ζ ω) * ψ (ζ ω) ∂μ = ∫ ω, ψ (η ω) * ψ (η ω) ∂μ :=
    (hid (fun p ↦ ψ p.2 * ψ p.2) (by fun_prop)).symm
  have huv' : Integrable (fun ω ↦ ψ (ζ ω) * ψ (η ω)) μ := hu.mul_bdd hv.aestronglyMeasurable hvb
  have huu' : Integrable (fun ω ↦ ψ (ζ ω) * ψ (ζ ω)) μ := hu.mul_bdd hu.aestronglyMeasurable hub
  have hvv' : Integrable (fun ω ↦ ψ (η ω) * ψ (η ω)) μ := hv.mul_bdd hv.aestronglyMeasurable hvb
  have e (ω : Ω) : (ψ (ζ ω) - ψ (η ω)) ^ 2 =
      ψ (ζ ω) * ψ (ζ ω) - 2 * (ψ (ζ ω) * ψ (η ω)) + ψ (η ω) * ψ (η ω) := by ring
  have hsq' : Integrable (fun ω ↦ (ψ (ζ ω) - ψ (η ω)) ^ 2) μ := by
    simp_rw [e]
    exact (huu'.sub (huv'.const_mul 2)).add hvv'
  have hsq : ∫ ω, (ψ (ζ ω) - ψ (η ω)) ^ 2 ∂μ = 0 := by
    simp_rw [e]
    rw [integral_add ?_ hvv', integral_sub huu' (huv'.const_mul 2), integral_const_mul]
    · linarith
    · exact huu'.sub (huv'.const_mul 2)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun ω ↦ sq_nonneg _) hsq').1 hsq] with ω hω
  simpa [sub_eq_zero] using hω

end CondExp

end MeasureTheory
