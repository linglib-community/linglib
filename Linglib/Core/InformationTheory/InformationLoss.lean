/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Linglib.Core.Probability.Kernel.Posterior

/-!
# The information loss of a decoder

A state is drawn from a prior and sent through a channel, and a decoder assigns each output a
distribution over states. The information the decoder loses is the expected surprisal of the state
under its distribution at the output, infinite [exactly when](##informationLoss_eq_top_iff) the
decoder rules out a state that can produce an output. Over finite types the loss of any decoder is
the conditional entropy of the state given the output plus [the expected divergence of the
posterior from it](##informationLoss_eq_posterior_add), so the posterior [loses the
least](##informationLoss_posterior_le) and [only the posterior
does](##informationLoss_eq_posterior_iff).

## References

* [cover-thomas-2006], chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace InformationTheory

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] (μ : Measure Ω) (κ : Kernel Ω 𝓧)
  (φ : Kernel 𝓧 Ω)

/-- The information the decoder `φ` loses about a state drawn from `μ` and sent through the
channel `κ`: the expected surprisal of the state under the decoder's distribution at the output. -/
noncomputable def informationLoss : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x, surprisal (φ x) ω ∂κ ω ∂μ

variable [Fintype Ω] [Fintype 𝓧] [MeasurableSingletonClass Ω] [MeasurableSingletonClass 𝓧]

theorem informationLoss_eq_sum :
    informationLoss μ κ φ = ∑ x, ∑ ω, μ {ω} * κ ω {x} * surprisal (φ x) ω := by
  simp_rw [informationLoss, lintegral_fintype, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring

variable {μ κ φ} in
/-- The loss depends on the decoder only at the outputs that occur. -/
theorem informationLoss_congr {φ' : Kernel 𝓧 Ω} (h : φ =ᵐ[κ ∘ₘ μ] φ') :
    informationLoss μ κ φ = informationLoss μ κ φ' := by
  rw [informationLoss_eq_sum, informationLoss_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun ω _ ↦ ?_
  rcases eq_or_ne ((κ ∘ₘ μ) {x}) 0 with hx | hx
  · rw [Measure.comp_apply_singleton, Finset.sum_eq_zero_iff] at hx
    rw [hx ω (Finset.mem_univ ω), zero_mul, zero_mul]
  · rw [ae_iff_of_countable.1 h x hx]

section Finite

variable {μ κ φ} [IsFiniteMeasure μ] [IsFiniteKernel κ]

/-- The loss is infinite exactly when the decoder rules out a state that can produce an output. -/
theorem informationLoss_eq_top_iff :
    informationLoss μ κ φ = ∞ ↔ ∃ ω x, μ {ω} ≠ 0 ∧ κ ω {x} ≠ 0 ∧ φ x {ω} = 0 := by
  rw [informationLoss_eq_sum]
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := ENNReal.sum_eq_top.1 h
    obtain ⟨ω, -, hω⟩ := ENNReal.sum_eq_top.1 hx
    rcases ENNReal.mul_eq_top.1 hω with ⟨h0, htop⟩ | ⟨htop, -⟩
    · exact ⟨ω, x, left_ne_zero_of_mul h0, right_ne_zero_of_mul h0, surprisal_eq_top_iff.1 htop⟩
    · exact absurd htop (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
  · rintro ⟨ω, x, hμ, hκ, hφ⟩
    refine ENNReal.sum_eq_top.2 ⟨x, Finset.mem_univ x, ENNReal.sum_eq_top.2
      ⟨ω, Finset.mem_univ ω, ?_⟩⟩
    rw [surprisal_eq_top_iff.2 hφ]
    exact ENNReal.mul_top (mul_ne_zero hμ hκ)

theorem informationLoss_ne_top_iff :
    informationLoss μ κ φ ≠ ∞ ↔ ∀ ω x, μ {ω} ≠ 0 → κ ω {x} ≠ 0 → φ x {ω} ≠ 0 := by
  simp only [ne_eq, informationLoss_eq_top_iff, not_exists, not_and]

/-- A finite loss is minus the expected log-probability of the state. -/
theorem toReal_informationLoss [∀ x, IsZeroOrProbabilityMeasure (φ x)]
    (h : ∀ ω x, μ {ω} ≠ 0 → κ ω {x} ≠ 0 → φ x {ω} ≠ 0) :
    (informationLoss μ κ φ).toReal = -∑ ω, μ.real {ω} * ∫ x, log ((φ x).real {ω}) ∂κ ω := by
  have hterm (ω : Ω) (x : 𝓧) : μ {ω} * κ ω {x} * surprisal (φ x) ω =
      ENNReal.ofReal (μ.real {ω} * ((κ ω).real {x} * -log ((φ x).real {ω}))) := by
    rcases eq_or_ne (μ {ω} * κ ω {x}) 0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h1 | h1 <;> simp [measureReal_def, h1]
    · rw [surprisal_of_ne_zero (h ω x (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0))
          (measure_ne_top _ _), ENNReal.ofReal_mul measureReal_nonneg,
        ENNReal.ofReal_mul measureReal_nonneg, measureReal_def μ, measureReal_def (κ ω),
        ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
        mul_assoc]
  have hnn (ω : Ω) (x : 𝓧) : 0 ≤ μ.real {ω} * ((κ ω).real {x} * -log ((φ x).real {ω})) :=
    mul_nonneg measureReal_nonneg (mul_nonneg measureReal_nonneg
      (neg_nonneg.2 (log_nonpos measureReal_nonneg measureReal_le_one)))
  rw [informationLoss_eq_sum, Finset.sum_comm,
    Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun x _ ↦ hterm ω x,
    Finset.sum_congr rfl fun ω _ ↦ (ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hnn ω x).symm,
    ← ENNReal.ofReal_sum_of_nonneg fun ω _ ↦ Finset.sum_nonneg fun x _ ↦ hnn ω x,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun ω _ ↦ Finset.sum_nonneg fun x _ ↦ hnn ω x),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [integral_fintype .of_finite, ← mul_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [smul_eq_mul, mul_neg]

end Finite

/-! ### The posterior -/

section Posterior

variable [Nonempty Ω] [IsFiniteMeasure μ] [IsFiniteKernel κ]

omit [Fintype 𝓧] in
private theorem sum_mul_surprisal_eq (φ : Kernel 𝓧 Ω) [∀ x, IsZeroOrProbabilityMeasure (φ x)]
    (x : 𝓧) :
    ∑ ω, μ {ω} * κ ω {x} * surprisal (φ x) ω =
      (κ ∘ₘ μ) {x} * (ENNReal.ofReal (Hm[(κ†μ) x]) + klDiv ((κ†μ) x) (φ x)) := by
  rcases eq_or_ne ((κ ∘ₘ μ) {x}) 0 with hx | hx
  · rw [hx, zero_mul]
    rw [Measure.comp_apply_singleton, Finset.sum_eq_zero_iff] at hx
    exact Finset.sum_eq_zero fun ω _ ↦ by rw [hx ω (Finset.mem_univ ω), zero_mul]
  · rw [← lintegral_surprisal_eq_ofReal_add_klDiv, lintegral_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [posterior_apply_singleton κ μ hx, mul_left_comm,
      ENNReal.mul_div_cancel hx (measure_ne_top _ _), mul_comm]

/-- The posterior loses the conditional entropy of the state given the output. -/
theorem informationLoss_posterior :
    informationLoss μ κ (κ†μ) = ∑ x, (κ ∘ₘ μ) {x} * ENNReal.ofReal (Hm[(κ†μ) x]) := by
  rw [informationLoss_eq_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by
    rw [sum_mul_surprisal_eq μ κ (κ†μ) x, klDiv_self, add_zero]

variable [∀ x, IsZeroOrProbabilityMeasure (φ x)]

/-- Any decoder loses what the posterior loses and, besides, the expected divergence of the
posterior from it over the outputs. -/
theorem informationLoss_eq_posterior_add :
    informationLoss μ κ φ = informationLoss μ κ (κ†μ) +
      ∑ x, (κ ∘ₘ μ) {x} * klDiv ((κ†μ) x) (φ x) := by
  rw [informationLoss_posterior, informationLoss_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [sum_mul_surprisal_eq μ κ φ x, mul_add]

/-- The posterior loses the least information. -/
theorem informationLoss_posterior_le : informationLoss μ κ (κ†μ) ≤ informationLoss μ κ φ :=
  informationLoss_eq_posterior_add μ κ φ ▸ le_self_add

theorem informationLoss_posterior_ne_top : informationLoss μ κ (κ†μ) ≠ ∞ := by
  rw [informationLoss_posterior]
  exact ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

/-- Only the posterior loses the least information: a decoder that loses no more agrees with it at
every output that occurs. -/
theorem informationLoss_eq_posterior_iff :
    informationLoss μ κ φ = informationLoss μ κ (κ†μ) ↔ φ =ᵐ[κ ∘ₘ μ] κ†μ := by
  have h {a d : ℝ≥0∞} (ha : a ≠ ∞) : a + d = a ↔ d = 0 :=
    ⟨fun h ↦ (ENNReal.add_right_inj ha).1 (h.trans (add_zero a).symm), fun h ↦ by rw [h, add_zero]⟩
  rw [informationLoss_eq_posterior_add μ κ φ, h (informationLoss_posterior_ne_top μ κ),
    Finset.sum_eq_zero_iff, Filter.EventuallyEq, ae_iff_of_countable]
  simp only [Finset.mem_univ, true_imp_iff]
  refine forall_congr' fun x ↦ ?_
  rw [mul_eq_zero, klDiv_eq_zero_iff, or_iff_not_imp_left]
  exact imp_congr_right fun _ ↦ eq_comm

end Posterior

end InformationTheory
