module

public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Tessler and Goodman (2019): The Language of Generalization

This file models generic, habitual and causal language as a threshold on prevalence, the
probability that an instance of the category has the property, with the threshold left uncertain.
The interpretation is a joint posterior over prevalence and threshold, the product of their priors
conditioned on the truth of the utterance, and the endorser chooses between the generalization and
silence by its prevalence marginal. [Integrating the threshold out](##listener_eq_ofDensity)
reweights the prevalence prior by the threshold prior's mass below the prevalence, so the
generalization is [endorsed](##endorse_iff) exactly when that mass at the referent prevalence
exceeds its prior expectation, and [more readily at higher prevalence](##endorse_mono). Under a
uniform threshold prior the mass is the prevalence itself, and endorsement is [prevalence above the
prior mean prevalence](##endorse_iff_expectation_lt), the cue validity of the paper's appendix. At
prevalence one half, *robins are female* under a symmetric prior is [no more informative than
silence](##boundary_of_symm), while *robins lay eggs*, whose prior has a component at zero
prevalence, is [endorsed](##endorse_of_mixture).

## Implementation notes

* The prevalence scale is a finite type carrying a real prevalence, and the prevalence prior a
  probability measure on it; the threshold prior is any nonzero finite measure on the reals, the
  paper's uniform prior on the unit interval being `uniformThreshold`.
* Silence is true at every threshold, so its marginalized meaning is the threshold prior's total
  mass, which the normalization cancels.
* The rationality of the endorser is a parameter, so the theorems hold at every positive
  rationality; the paper's fitted values are not pinned. The fits to the endorsement data of the
  three case studies are the paper's empirical content and are not formalized.

## References

* [tessler-goodman-2019]
* [frank-goodman-2012]
* [lassiter-goodman-2017]
* [leslie-2008]
-/

@[expose] public section

namespace TesslerGoodman2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal NNReal

/-- In the endorsement model the speaker says the generalization or stays silent. -/
inductive Utterance
  | generic
  | silent
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩

/-- Under the threshold semantics (2), a generalization is true when the prevalence exceeds the
threshold. -/
def genericMeaning (θ p : ℝ) : Prop := θ < p

section Model

variable {W : Type*}

/-- The pairs of a state and a threshold at which an utterance is true (2): the generalization
where the prevalence exceeds the threshold, silence everywhere. -/
def truthSet (prev : W → ℝ) : Utterance → Set (W × ℝ)
  | .generic => {x | genericMeaning x.2 (prev x.1)}
  | .silent => Set.univ

/-- The marginalized meaning of an utterance at a state is the threshold prior's mass on the
thresholds at which it is true there. -/
noncomputable def meaning (ν : Measure ℝ) (prev : W → ℝ) (u : Utterance) (w : W) : ℝ≥0∞ :=
  ν (Prod.mk w ⁻¹' truthSet prev u)

variable [MeasurableSpace W]

/-- The interpretation model (1) conditions the joint prior over prevalence and threshold on the
truth of the utterance. -/
noncomputable def interpretation (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) (u : Utterance) :
    Measure (W × ℝ) :=
  (μ.prod ν)[|truthSet prev u]

/-- The endorsement model (3) reads the interpretation's marginal on prevalence. -/
noncomputable def listener (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) :
    Kernel Utterance W :=
  Kernel.ofFunOfCountable fun u ↦ (interpretation μ ν prev u).fst

instance (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) : IsFiniteKernel (listener μ ν prev) :=
  ⟨⟨1, ENNReal.one_lt_top, fun u ↦ by
    rw [listener, Kernel.ofFunOfCountable_apply, Measure.fst_univ, interpretation]
    exact prob_le_one⟩⟩

theorem measurableSet_truthSet [DiscreteMeasurableSpace W] (prev : W → ℝ) :
    ∀ u, MeasurableSet (truthSet prev u)
  | .generic => measurableSet_lt measurable_snd (Measurable.of_discrete.comp measurable_fst)
  | .silent => .univ

variable [Fintype W]

/-- The expectation under the prevalence prior of the marginalized meaning of the
generalization. -/
noncomputable def expectedMeaning (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) : ℝ≥0∞ :=
  ∑ w, meaning ν prev .generic w * μ {w}

theorem expectedMeaning_ne_top (μ : Measure W) [IsFiniteMeasure μ] (ν : Measure ℝ)
    [IsFiniteMeasure ν] (prev : W → ℝ) : expectedMeaning μ ν prev ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top μ _)

variable [DiscreteMeasurableSpace W]

/-- Integrating the threshold out of the interpretation reweights the prevalence prior by the
marginalized meaning. -/
theorem listener_eq_ofDensity (μ : Measure W) (ν : Measure ℝ) [SFinite ν] (prev : W → ℝ) :
    listener μ ν prev = Kernel.ofDensity μ (meaning ν prev) :=
  Kernel.ext fun u ↦ by
    rw [listener, Kernel.ofFunOfCountable_apply, interpretation,
      Measure.fst_cond_prod μ ν (measurableSet_truthSet prev u)]
    rfl

/-- The endorsement model (3) is the speaker at rationality `lam`, choosing between the
generalization and silence at no cost. -/
noncomputable def endorser (lam : ℝ) (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) :
    Kernel W Utterance :=
  speaker lam 0 (listener μ ν prev) Measure.dirac

/-- The generalization is endorsed at a state when the speaker produces it more readily than
silence. -/
def Endorsed (lam : ℝ) (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ) (w : W) : Prop :=
  (endorser lam μ ν prev w).real {.silent} < (endorser lam μ ν prev w).real {.generic}

variable (μ : Measure W) (ν : Measure ℝ) (prev : W → ℝ)

theorem listener_generic_apply [SFinite ν] (w : W) :
    listener μ ν prev .generic {w} =
      meaning ν prev .generic w * μ {w} / expectedMeaning μ ν prev := by
  rw [listener_eq_ofDensity, Kernel.ofDensity_apply_singleton]; rfl

variable [IsProbabilityMeasure μ] [IsFiniteMeasure ν] [NeZero ν] {lam : ℝ} {w : W}

theorem listener_silent : listener μ ν prev .silent = μ := by
  rw [listener_eq_ofDensity, Kernel.ofDensity_apply_eq_of_eq_mul μ (f := 1)
    (Measure.measure_univ_ne_zero.2 (NeZero.ne ν)) (measure_ne_top ν _) fun _ ↦ (mul_one _).symm,
    Kernel.ofDensity_apply, Pi.one_apply, withDensity_one, cond_univ]

/-- The generalization is endorsed iff its marginalized meaning at the referent state exceeds its
prior expectation, the comparison of Figure 1C. -/
theorem endorse_iff (hlam : 0 < lam) (hw : μ {w} ≠ 0) (hZ : expectedMeaning μ ν prev ≠ 0) :
    Endorsed lam μ ν prev w ↔ expectedMeaning μ ν prev < meaning ν prev .generic w := by
  rw [Endorsed, endorser, speaker_dirac_real_singleton_lt_iff (L := listener μ ν prev) (w := w)
    hlam.le ⟨.silent, by rwa [listener_silent]⟩]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [ENNReal.rpow_lt_rpow_iff hlam, listener_silent, listener_generic_apply,
    ENNReal.lt_div_iff_mul_lt (Or.inl hZ) (Or.inl (expectedMeaning_ne_top μ ν prev)), mul_comm,
    ENNReal.mul_lt_mul_iff_left hw (measure_ne_top μ _)]

/-- Endorsement is monotone in prevalence at a fixed prior (Figure 1C). -/
theorem endorse_mono (hlam : 0 < lam) (hZ : expectedMeaning μ ν prev ≠ 0) {w w' : W}
    (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (hle : prev w ≤ prev w') (h : Endorsed lam μ ν prev w) :
    Endorsed lam μ ν prev w' := by
  rw [endorse_iff μ ν prev hlam hw hZ] at h
  rw [endorse_iff μ ν prev hlam hw' hZ]
  exact h.trans_le (measure_mono fun θ (hθ : θ < prev w) => lt_of_lt_of_le hθ hle)

end Model

/-! ### The uniform threshold prior -/

section Uniform

/-- The uniform threshold prior on the unit interval, the support of a prevalence prior. -/
noncomputable def uniformThreshold : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure uniformThreshold :=
  ⟨by rw [uniformThreshold, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one]⟩

theorem uniformThreshold_Iio {p : ℝ} (h1 : p ≤ 1) :
    uniformThreshold (Set.Iio p) = ENNReal.ofReal p := by
  rw [uniformThreshold, Measure.restrict_apply measurableSet_Iio,
    show Set.Iio p ∩ Set.Icc 0 1 = Set.Ico 0 p by
      ext θ; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h, h0', _⟩; exact ⟨h0', h⟩
      · rintro ⟨h0', h⟩; exact ⟨h, h0', by linarith⟩,
    Real.volume_Ico, sub_zero]

variable {W : Type*}

theorem meaning_uniformThreshold (prev : W → ℝ) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) (w : W) :
    meaning uniformThreshold prev .generic w = ENNReal.ofReal (prev w) :=
  uniformThreshold_Iio (hp w).2

variable [MeasurableSpace W]

/-- The mean prevalence under the prior. -/
noncomputable def expectedPrevalence (μ : Measure W) (prev : W → ℝ) : ℝ := ∫ w, prev w ∂μ

variable (prev : W → ℝ)

/-- For a pushforward prevalence prior, the mean prevalence over categories is the mean of the
prevalence prior (Appendix A). -/
theorem expectedPrevalence_map {K : Type*} [MeasurableSpace K] [DiscreteMeasurableSpace K]
    [Countable K] (P : Measure K) (prevK : K → W) (hprev : Measurable prevK)
    (hf : Measurable prev) :
    expectedPrevalence (P.map prevK) prev = ∫ k, prev (prevK k) ∂P := by
  rw [expectedPrevalence, integral_map hprev.aemeasurable hf.aestronglyMeasurable]

variable [Fintype W] [DiscreteMeasurableSpace W] (μ : Measure W) [IsProbabilityMeasure μ]

theorem expectedPrevalence_eq_sum :
    expectedPrevalence μ prev = ∑ w, μ.real {w} * prev w := by
  rw [expectedPrevalence, integral_fintype .of_finite]
  rfl

theorem expectedMeaning_uniformThreshold (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) :
    expectedMeaning μ uniformThreshold prev = ENNReal.ofReal (expectedPrevalence μ prev) := by
  rw [expectedPrevalence_eq_sum, expectedMeaning,
    ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg measureReal_nonneg (hp w).1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [meaning_uniformThreshold prev hp, ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ _), mul_comm]

variable {lam : ℝ} {w : W}

/-- The generalization is endorsed exactly when the referent prevalence exceeds the mean
prevalence under the prior, the cue validity of Appendix A. -/
theorem endorse_iff_expectation_lt (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev) :
    Endorsed lam μ uniformThreshold prev w ↔ expectedPrevalence μ prev < prev w := by
  rw [endorse_iff μ uniformThreshold prev hlam hw
    (by rw [expectedMeaning_uniformThreshold prev μ hp]; exact (ENNReal.ofReal_pos.2 hZ).ne'),
    expectedMeaning_uniformThreshold prev μ hp, meaning_uniformThreshold prev hp,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hZ.le]

theorem endorse_of_expectation_lt (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev)
    (h : expectedPrevalence μ prev < prev w) : Endorsed lam μ uniformThreshold prev w :=
  (endorse_iff_expectation_lt prev μ hlam hp hw hZ).2 h

theorem not_endorse_of_le_expectation (hlam : 0 < lam) (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1)
    (hw : μ {w} ≠ 0) (hZ : 0 < expectedPrevalence μ prev)
    (h : prev w ≤ expectedPrevalence μ prev) : ¬ Endorsed lam μ uniformThreshold prev w :=
  fun he => absurd ((endorse_iff_expectation_lt prev μ hlam hp hw hZ).1 he) (not_lt.2 h)

end Uniform

/-! ### Table 1: symmetric and bimodal priors -/

theorem isProbabilityMeasure_mixture {W : Type*} [MeasurableSpace W] (ν₁ ν₀ : Measure W)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₀] {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1) :
    IsProbabilityMeasure (φ.toNNReal • ν₁ + (1 - φ).toNNReal • ν₀) :=
  ⟨by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.coe_add, ← Real.toNNReal_add h0 (by linarith), add_sub_cancel,
      Real.toNNReal_one, ENNReal.coe_one]⟩

section Examples

variable {W : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  (prev : W → ℝ)

theorem expectedPrevalence_eq_half_of_symm (μ : Measure W) [IsProbabilityMeasure μ] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hμ : ∀ w, μ {σ w} = μ {w}) :
    expectedPrevalence μ prev = 1 / 2 := by
  have h1 : ∑ w, μ.real {w} = 1 := sum_measureReal_singleton_eq_one μ
  have key : expectedPrevalence μ prev = ∑ w, μ.real {w} * (1 - prev w) := by
    rw [expectedPrevalence_eq_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hσ, measureReal_def, hμ, ← measureReal_def]
  have : ∑ w, μ.real {w} * (1 - prev w) = (∑ w, μ.real {w}) - ∑ w, μ.real {w} * prev w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [this, h1, ← expectedPrevalence_eq_sum] at key
  linarith

theorem expectedPrevalence_mixture (ν₁ ν₀ : Measure W) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₀]
    (c d : ℝ≥0) :
    expectedPrevalence (c • ν₁ + d • ν₀) prev =
      c * expectedPrevalence ν₁ prev + d * expectedPrevalence ν₀ prev := by
  simp only [expectedPrevalence]
  rw [integral_add_measure (.of_finite) (.of_finite), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]

theorem boundary_of_symm (μ : Measure W) [IsProbabilityMeasure μ] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hμ : ∀ w, μ {σ w} = μ {w}) {lam : ℝ} (hlam : 0 < lam)
    (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) {w : W} (hw : μ {w} ≠ 0) (hhalf : prev w = 1 / 2) :
    (endorser lam μ uniformThreshold prev w).real {.generic} =
      (endorser lam μ uniformThreshold prev w).real {.silent} := by
  have hE := expectedPrevalence_eq_half_of_symm prev μ σ hσ hμ
  have hZ : 0 < expectedPrevalence μ prev := by rw [hE]; norm_num
  have h1 := not_endorse_of_le_expectation prev μ hlam hp hw hZ (by rw [hE, hhalf])
  have h2 : ¬ (endorser lam μ uniformThreshold prev w).real {.generic} <
      (endorser lam μ uniformThreshold prev w).real {.silent} := by
    rw [endorser,
      speaker_dirac_real_singleton_lt_iff (L := listener μ uniformThreshold prev) (w := w)
      hlam.le ⟨.silent, by rwa [listener_silent]⟩]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
    rw [ENNReal.rpow_lt_rpow_iff hlam, listener_silent, listener_generic_apply,
      expectedMeaning_uniformThreshold prev μ hp, meaning_uniformThreshold prev hp, hE, hhalf,
      ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact lt_irrefl _
  exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)

theorem expectedPrevalence_bimodal (ν₁ : Measure W) [IsProbabilityMeasure ν₁] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hν : ∀ w, ν₁ {σ w} = ν₁ {w}) (w₀ : W)
    (hw₀ : prev w₀ = 0) {φ : ℝ} (h0 : 0 ≤ φ) :
    expectedPrevalence (φ.toNNReal • ν₁ + (1 - φ).toNNReal • Measure.dirac w₀) prev = φ / 2 := by
  rw [expectedPrevalence_mixture, expectedPrevalence_eq_half_of_symm prev ν₁ σ hσ hν,
    expectedPrevalence, integral_dirac, hw₀, Real.coe_toNNReal _ h0]
  ring

theorem endorse_of_mixture (ν₁ : Measure W) [IsProbabilityMeasure ν₁] (σ : W ≃ W)
    (hσ : ∀ w, prev (σ w) = 1 - prev w) (hν : ∀ w, ν₁ {σ w} = ν₁ {w}) (w₀ : W)
    (hw₀ : prev w₀ = 0) {φ : ℝ} (h0 : 0 < φ) (h1 : φ < 1) {lam : ℝ} (hlam : 0 < lam)
    (hp : ∀ w, 0 ≤ prev w ∧ prev w ≤ 1) {w : W} (hw : ν₁ {w} ≠ 0) (hhalf : prev w = 1 / 2) :
    haveI := isProbabilityMeasure_mixture ν₁ (Measure.dirac w₀) h0.le h1.le
    Endorsed lam (φ.toNNReal • ν₁ + (1 - φ).toNNReal • Measure.dirac w₀) uniformThreshold prev
      w := by
  have := isProbabilityMeasure_mixture ν₁ (Measure.dirac w₀) h0.le h1.le
  have hE := expectedPrevalence_bimodal prev ν₁ σ hσ hν w₀ hw₀ h0.le
  refine endorse_of_expectation_lt prev _ hlam hp ?_ (by rw [hE]; positivity)
    (by rw [hE, hhalf]; linarith)
  rw [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos ?_ hw) le_self_add)
  exact_mod_cast (Real.toNNReal_pos.2 h0).ne'

end Examples

end TesslerGoodman2019
