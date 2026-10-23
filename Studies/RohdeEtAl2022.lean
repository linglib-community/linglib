module

public import Linglib.Pragmatics.RSA.Basic

/-!
# Rohde, Hoek, Keshev and Franke (2022): This better be interesting

This file formalizes the paper's Bayesian conceptualization of a listener's expectations
about upcoming content: the probability of a meaning given that a speaker chose to report
it combines the prior probability of the situation with the likelihood that a speaker would
articulate it, and the two are separable, the likelihood varying with the context of speech.
Over the two values of the paper's forced choice, one near the pretest mean and one a
standard deviation above it, the posterior on the atypical value given a report exceeds its
prior exactly when the atypical situation is the likelier to be reported,
`prior_lt_posterior_iff`, and between two contexts the posterior is larger where the atypical
situation is relatively likelier to be reported, `posterior_lt_posterior_iff`. An
informativity speaker who may also stay silent, silence conveying only the prior, derives the
direction of the likelihood: because silence is the more attractive the likelier the situation,
a report is likelier at the atypical value, `S_report_lt`, so a report shifts the guess toward
the atypical value relative to the prior, `prior_lt_posterior`, the more so the more
available silence is, `posterior_lt_of_silence_lt`, and not at all when the speaker was asked
and silence was not an option, `posterior_eq_prior_of_asked`.

## Implementation notes

The paper gives the conceptualization in prose and its predictions through four
forced-choice experiments; the speaker with a null message is the model the paper takes from
its precursors, on the substrate's kernel pipeline, and the null message's cost is the
parameter the paper's contexts vary; when the speaker is asked, the null message is absent.
The experiments' selection rates are not represented.

## References

* [H. Rohde, J. Hoek, M. Keshev, M. Franke, *This better be interesting: a speaker's decision
  to speak cues listeners to expect informative content* (2022)][rohde-etal-2022]
* [L. Bergen, R. Levy, N. D. Goodman, *Pragmatic reasoning through semantic inference*
  (2016)][bergen-levy-goodman-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace RohdeEtAl2022

/-- The forced choice offers two values, one near the mean of the pretest and one a standard
deviation above it. -/
inductive Value
  | typical
  | atypical
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Value := ⊤
instance : DiscreteMeasurableSpace Value := ⟨fun _ ↦ trivial⟩

private theorem pair_support (μ : Measure Value) :
    ∀ v, μ {v} ≠ 0 → v = Value.atypical ∨ v = Value.typical :=
  fun v _ ↦ by cases v <;> simp

/-! ### The Bayesian conceptualization -/

section Bayes

variable (μ : Measure Value) [IsProbabilityMeasure μ]

theorem prior_lt_posterior_iff (report : Kernel Value Bool) [IsFiniteKernel report]
    (hx : (report ∘ₘ μ) {true} ≠ 0) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) :
    μ.real {.atypical} < (listener μ report true).real {.atypical} ↔
      (report .typical).real {true} < (report .atypical).real {true} := by
  rw [listener_apply_eq_posterior _ _ hx]
  exact real_lt_posterior_real_singleton_iff_of_pair report μ (by decide) (pair_support μ) hx ha ht

theorem posterior_lt_posterior_iff (report₁ report₂ : Kernel Value Bool)
    [IsFiniteKernel report₁] [IsFiniteKernel report₂] (hx₁ : (report₁ ∘ₘ μ) {true} ≠ 0)
    (hx₂ : (report₂ ∘ₘ μ) {true} ≠ 0) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) :
    (listener μ report₁ true).real {.atypical} < (listener μ report₂ true).real {.atypical} ↔
      (report₁ .atypical).real {true} * (report₂ .typical).real {true} <
        (report₂ .atypical).real {true} * (report₁ .typical).real {true} := by
  have hm₁ : 0 < (report₁ ∘ₘ μ).real {true} :=
    ENNReal.toReal_pos hx₁ (measure_ne_top _ _)
  have hm₂ : 0 < (report₂ ∘ₘ μ).real {true} :=
    ENNReal.toReal_pos hx₂ (measure_ne_top _ _)
  have hp : 0 < μ.real {Value.atypical} := ENNReal.toReal_pos ha (measure_ne_top _ _)
  have hq : 0 < μ.real {Value.typical} := ENNReal.toReal_pos ht (measure_ne_top _ _)
  rw [listener_apply_eq_posterior _ _ hx₁, listener_apply_eq_posterior _ _ hx₂,
    posterior_real_singleton _ _ hx₁, posterior_real_singleton _ _ hx₂, div_lt_div_iff₀ hm₁ hm₂,
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ),
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ), ← sub_pos]
  rw [show μ.real {Value.atypical} * (report₂ Value.atypical).real {true} *
      (μ.real {Value.atypical} * (report₁ Value.atypical).real {true} +
        μ.real {Value.typical} * (report₁ Value.typical).real {true}) -
      μ.real {Value.atypical} * (report₁ Value.atypical).real {true} *
      (μ.real {Value.atypical} * (report₂ Value.atypical).real {true} +
        μ.real {Value.typical} * (report₂ Value.typical).real {true}) =
      μ.real {Value.atypical} * μ.real {Value.typical} *
        ((report₂ Value.atypical).real {true} * (report₁ Value.typical).real {true} -
          (report₁ Value.atypical).real {true} * (report₂ Value.typical).real {true}) by ring,
    mul_pos_iff_of_pos_left (mul_pos hp hq), sub_pos]

end Bayes

/-! ### Informativity and the null message -/

/-- A report of a value, or silence. -/
abbrev Utterance := Option Value

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩

/-- A report is true of the value it reports; silence is true of both. -/
def extension : Utterance → Set Value
  | some v => {v}
  | none => Set.univ

variable (μ : Measure Value)

/-- To the literal listener a report conveys its value and silence conveys the prior. -/
noncomputable def L0 : Kernel Utterance Value :=
  listener μ (truthful extension)

theorem L0_some_of_ne {v w : Value} (h : v ≠ w) : L0 μ (some v) {w} = 0 :=
  listener_truthful_apply_singleton_of_notMem μ extension
    (by simp [extension, Ne.symm h])

instance : IsFiniteKernel (L0 μ) := inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

variable (α cs cn : ℝ)

/-- The speaker is the informativity speaker over reports, each costing `cs`, with silence
costing `cn`. -/
noncomputable def S : Kernel Value Utterance :=
  speaker α (Option.elim · cn fun _ ↦ cs) (L0 μ) Measure.dirac

instance : IsFiniteKernel (S μ α cs cn) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- When asked, the speaker has no silence option and chooses among the reports. -/
noncomputable def askedS : Kernel Value Value :=
  speaker α (fun _ ↦ cs) (listener μ (truthful fun v ↦ ({v} : Set Value))) Measure.dirac

instance : IsFiniteKernel (askedS μ α cs) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-! ### The decision to speak as the observation -/

/-- `spoke` records the report's form, whether a value was reported or the speaker stayed
silent. -/
noncomputable def spoke : Kernel Value Bool := (S μ α cs cn).map Option.isSome

instance : IsFiniteKernel (spoke μ α cs cn) :=
  inferInstanceAs (IsFiniteKernel ((S μ α cs cn).map Option.isSome))

theorem spoke_apply_true (hα : 0 < α) (v : Value) :
    spoke μ α cs cn v {true} = S μ α cs cn v {some v} := by
  rw [spoke, Kernel.map_apply' _ Measurable.of_discrete _ (MeasurableSet.singleton true),
    show (Option.isSome ⁻¹' ({true} : Set Bool) : Set Utterance) =
      {some .typical} ∪ {some .atypical} by ext u; rcases u with _ | (_ | _) <;> simp,
    measure_union (by simp) (MeasurableSet.singleton _)]
  simp only [S]
  cases v
  · rw [speaker_dirac_apply_singleton_eq_zero hα
      (L0_some_of_ne μ (v := .atypical) (w := .typical) (by decide)), add_zero]
  · rw [speaker_dirac_apply_singleton_eq_zero hα
      (L0_some_of_ne μ (v := .typical) (w := .atypical) (by decide)), zero_add]

variable [IsProbabilityMeasure μ]

theorem L0_some_self {v : Value} (hv : μ {v} ≠ 0) : L0 μ (some v) {v} = 1 :=
  listener_truthful_apply_singleton_of_eq_singleton μ extension rfl hv

theorem L0_none (v : Value) : L0 μ none {v} = μ {v} :=
  listener_truthful_apply_singleton_of_eq_univ μ extension rfl v

/-! ### Newsworthiness -/

theorem S_report (hα : 0 < α) {v : Value} (hv : μ {v} ≠ 0) :
    (S μ α cs cn v).real {some v} =
      Real.exp (-(α * cs)) /
        (Real.exp (-(α * cs)) + Real.exp (-(α * cn)) * (μ {v} ^ α).toReal) := by
  rw [S, speaker_dirac_real_singleton hα.le, Fintype.sum_option,
    Finset.sum_eq_single v
      (fun w _ hw ↦ by
        rw [L0_some_of_ne μ hw, ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ v) h),
    L0_some_self μ hv, L0_none, ENNReal.one_rpow, ENNReal.toReal_one, one_mul,
    Option.elim_some, Option.elim_none, add_comm, mul_comm (μ {v} ^ α).toReal]

theorem S_report_pos (hα : 0 < α) {v : Value} (hv : μ {v} ≠ 0) :
    0 < (S μ α cs cn v).real {some v} := by
  rw [S_report μ α cs cn hα hv]
  positivity

theorem S_report_lt (hα : 0 < α) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0)
    (h : μ {.atypical} < μ {.typical}) :
    (S μ α cs cn .typical).real {some .typical} <
      (S μ α cs cn .atypical).real {some .atypical} := by
  rw [S_report μ α cs cn hα ht, S_report μ α cs cn hα ha]
  have hpow : (μ {Value.atypical} ^ α).toReal < (μ {Value.typical} ^ α).toReal :=
    (ENNReal.toReal_lt_toReal (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))).mpr (ENNReal.rpow_lt_rpow h hα)
  rw [div_lt_div_iff_of_pos_left (Real.exp_pos _) (by positivity) (by positivity)]
  exact add_lt_add_right (mul_lt_mul_of_pos_left hpow (Real.exp_pos _)) _

theorem spoke_apply_true_ne_zero (hα : 0 < α) {v : Value} (hv : μ {v} ≠ 0) :
    spoke μ α cs cn v {true} ≠ 0 := by
  rw [spoke_apply_true μ α cs cn hα]
  intro h0
  have := S_report_pos μ α cs cn hα hv
  rw [measureReal_def, h0, ENNReal.toReal_zero] at this
  exact lt_irrefl _ this

theorem prior_lt_posterior (hα : 0 < α) (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0)
    (h : μ {.atypical} < μ {.typical}) :
    μ.real {.atypical} < (listener μ (spoke μ α cs cn) true).real {.atypical} := by
  rw [prior_lt_posterior_iff μ _
    (Measure.comp_apply_singleton_ne_zero _ _ ht (spoke_apply_true_ne_zero μ α cs cn hα ht)) ht ha]
  simpa only [measureReal_def, spoke_apply_true μ α cs cn hα] using
    S_report_lt μ α cs cn hα ht ha h

theorem posterior_eq_prior_of_asked (hα : 0 < α) (ht : μ {.typical} ≠ 0)
    (ha : μ {.atypical} ≠ 0) :
    (listener μ ((askedS μ α cs).map fun _ ↦ true) true).real {.atypical} =
      μ.real {.atypical} := by
  have h1 : ∀ v, μ {v} ≠ 0 → ((askedS μ α cs).map (fun _ ↦ true) v).real {true} = 1 :=
      fun v hv ↦ by
    have hv1 : askedS μ α cs v {v} = 1 :=
      speaker_listener_truthful_dirac_eq_one hα _ μ _ hv rfl fun _ h hv' ↦ h hv'.symm
    rw [measureReal_def, Kernel.map_apply' _ measurable_const _ (MeasurableSet.singleton true),
      askedS,
      Set.preimage_const_of_mem (Set.mem_singleton true),
      le_antisymm (speaker_apply_univ_le_one α _ _ _ v) (hv1 ▸ measure_mono (Set.subset_univ _)),
      ENNReal.toReal_one]
  have hx : (((askedS μ α cs).map fun _ ↦ true) ∘ₘ μ) {true} ≠ 0 :=
    Measure.comp_apply_singleton_ne_zero _ _ ht fun h ↦ by simpa [measureReal_def, h] using h1 _ ht
  rw [listener_apply_eq_posterior _ _ hx, posterior_real_singleton _ _ hx,
    Measure.comp_real_singleton_of_pair _ _ (by decide) (pair_support μ), h1 _ ha, h1 _ ht,
    mul_one, mul_one, measureReal_singleton_add_singleton_of_pair μ (by decide) (pair_support μ),
    div_one]

theorem posterior_lt_of_silence_lt (hα : 0 < α) {cn₁ cn₂ : ℝ} (hlt : cn₂ < cn₁)
    (ht : μ {.typical} ≠ 0) (ha : μ {.atypical} ≠ 0) (h : μ {.atypical} < μ {.typical}) :
    (listener μ (spoke μ α cs cn₁) true).real {.atypical} <
      (listener μ (spoke μ α cs cn₂) true).real {.atypical} := by
  rw [posterior_lt_posterior_iff μ _ _
    (Measure.comp_apply_singleton_ne_zero _ _ ht (spoke_apply_true_ne_zero μ α cs cn₁ hα ht))
    (Measure.comp_apply_singleton_ne_zero _ _ ht (spoke_apply_true_ne_zero μ α cs cn₂ hα ht)) ht ha]
  simp only [measureReal_def, spoke_apply_true μ α cs _ hα]
  rw [← measureReal_def, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    S_report μ α cs cn₁ hα ha, S_report μ α cs cn₂ hα ht,
    S_report μ α cs cn₂ hα ha, S_report μ α cs cn₁ hα ht]
  have hn : Real.exp (-(α * cn₁)) < Real.exp (-(α * cn₂)) :=
    Real.exp_lt_exp.2 (neg_lt_neg (mul_lt_mul_of_pos_left hlt hα))
  have hAB : (μ {Value.atypical} ^ α).toReal < (μ {Value.typical} ^ α).toReal :=
    (ENNReal.toReal_lt_toReal (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (measure_ne_top _ _))).mpr (ENNReal.rpow_lt_rpow h hα)
  have hs := Real.exp_pos (-(α * cs))
  have hn₁ := (Real.exp_pos (-(α * cn₁))).le
  have hB : 0 ≤ (μ {Value.atypical} ^ α).toReal := ENNReal.toReal_nonneg
  set s := Real.exp (-(α * cs))
  set n₁ := Real.exp (-(α * cn₁))
  set n₂ := Real.exp (-(α * cn₂))
  set A := (μ {Value.typical} ^ α).toReal
  set B := (μ {Value.atypical} ^ α).toReal
  have hA : 0 ≤ A := hB.trans hAB.le
  have d₁ : 0 < s + n₁ * B := add_pos_of_pos_of_nonneg hs (mul_nonneg hn₁ hB)
  have d₂ : 0 < s + n₂ * A := add_pos_of_pos_of_nonneg hs (mul_nonneg (hn₁.trans hn.le) hA)
  have d₃ : 0 < s + n₂ * B := add_pos_of_pos_of_nonneg hs (mul_nonneg (hn₁.trans hn.le) hB)
  have d₄ : 0 < s + n₁ * A := add_pos_of_pos_of_nonneg hs (mul_nonneg hn₁ hA)
  rw [div_mul_div_comm, div_mul_div_comm, div_lt_div_iff₀ (mul_pos d₁ d₂) (mul_pos d₃ d₄)]
  refine mul_lt_mul_of_pos_left ?_ (mul_pos hs hs)
  have key : (s + n₁ * B) * (s + n₂ * A) - (s + n₂ * B) * (s + n₁ * A)
      = s * ((n₂ - n₁) * (A - B)) := by ring
  linarith [key, mul_pos hs (mul_pos (sub_pos.mpr hn) (sub_pos.mpr hAB))]

end RohdeEtAl2022
