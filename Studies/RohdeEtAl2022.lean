module

public import Linglib.Core.InformationTheory.Entropy.Surprisal
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.RSA.Basic

/-!
# Rohde, Hoek, Keshev and Franke (2022): This better be interesting

A listener guessing what a speaker reported weighs the prior of each situation by the likelihood
that a speaker would report it: [posterior odds are prior odds times the likelihood
ratio](##RSA.listener_real_singleton_div). Here the speaker knows the situation and reports it or
stays silent, silence conveying only the prior, and [speaks with a probability logistic in its
surprisal](##spoke_real_true). Told only that she spoke, the listener [expects more surprising
content than the prior does](##measureEntropy_le_integral_surprisal) and [favours the rarer of the
two values offered](##prior_odds_lt_listener_odds), [the more so where silence is
cheaper](##listener_odds_lt_of_silence_lt); [an answer to a question conveys only the
prior](##listener_asked_eq_prior).

## Implementation notes

The situations are the values of the quantity guessed, any finite type, and the forced choice
offers two of them, the higher less probable under the prior; a choice between two is monotone in
their odds, so the predictions compare odds. A thought is not chosen for being worth saying, so
the paper's THINK condition is the prior. Announcing and speaking out of the blue are the speaker
who may stay silent, answering a question is one without that option, and a larger audience makes
silence cheaper relative to speaking; only the difference of the two costs matters. Silence is the
null utterance of [lassiter-goodman-2017], whom the paper cites for the decision to speak. The
narrator through whom every passage is reported and the selection rates are not represented, and
the model distinguishes any two costs of silence, where the fourth experiment found no difference
between announcing and addressing a crowd.

## References

* [H. Rohde, J. Hoek, M. Keshev, M. Franke, *This better be interesting: a speaker's decision
  to speak cues listeners to expect informative content* (2022)][rohde-etal-2022]
* [D. Lassiter, N. D. Goodman, *Adjectival vagueness in a Bayesian model of interpretation*
  (2017)][lassiter-goodman-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA InformationTheory
open scoped ENNReal

namespace RohdeEtAl2022

variable {W : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-- A report is true of the situation it reports; silence is true of every situation. -/
def extension : Option W → Set W
  | some v => {v}
  | none => Set.univ

variable (μ : Measure W) (α cs cn : ℝ)

/-- The speaker knows the situation and soft-maximizes informativity to the literal listener, to
whom a report conveys its situation and silence the prior; a report costs `cs`, silence `cn`. -/
noncomputable def S : Kernel W (Option W) :=
  speaker α (Option.elim · cn fun _ ↦ cs) (listener μ (truthful extension)) Measure.dirac

/-- The listener observes whether the speaker spoke, not what she reported. -/
noncomputable def spoke : Kernel W Bool := (S μ α cs cn).map Option.isSome

/-- When asked, the speaker has no silent option and chooses among the reports. -/
noncomputable def askedS : Kernel W W :=
  speaker α (fun _ ↦ cs) (listener μ (truthful fun v ↦ ({v} : Set W))) Measure.dirac

instance : IsFiniteKernel (S μ α cs cn) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

instance : IsFiniteKernel (spoke μ α cs cn) :=
  inferInstanceAs (IsFiniteKernel ((S μ α cs cn).map Option.isSome))

/-! ### The decision to speak -/

theorem spoke_apply_true (hα : 0 < α) (v : W) :
    spoke μ α cs cn v {true} = S μ α cs cn v {some v} := by
  rw [spoke, Kernel.map_apply' _ .of_discrete _ (.singleton true),
    show Option.isSome ⁻¹' {true} = ((Finset.univ.map .some : Finset (Option W)) : Set _) by
      ext u; cases u <;> simp,
    ← sum_measure_singleton, Finset.sum_map]
  exact Finset.sum_eq_single v
    (fun w _ hw ↦ speaker_listener_truthful_dirac_apply_singleton_eq_zero hα _ μ extension
      (show v ∉ extension (some w) from fun h ↦ hw h.symm)) (absurd (Finset.mem_univ v))

variable [IsProbabilityMeasure μ]

/-- The speaker breaks her silence with a probability logistic in the surprisal of the situation
less the extra cost of speaking, so that atypical situations are the likelier to be mentioned. -/
theorem spoke_real_true (hα : 0 < α) {v : W} (hv : μ {v} ≠ 0) :
    (spoke μ α cs cn v).real {true} =
      Real.sigmoid (α * ((surprisal μ v).toReal - (cs - cn))) := by
  rw [measureReal_def, spoke_apply_true μ α cs cn hα, ← measureReal_def, S,
    speaker_listener_truthful_dirac_real_singleton_of_eq_singleton hα _ μ extension hv
      (Option.some_ne_none v) rfl rfl, toReal_surprisal prob_le_one]
  · simp only [Option.elim]
    ring_nf
  · rintro (_ | w) h
    exacts [.inr rfl, .inl (by rw [show v = w from h])]

theorem spoke_apply_true_eq_zero_iff (hα : 0 < α) {v : W} :
    spoke μ α cs cn v {true} = 0 ↔ μ {v} = 0 := by
  rw [spoke_apply_true μ α cs cn hα, ← not_iff_not, ← ne_eq, S,
    speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα _ μ extension]
  exact and_iff_right rfl

/-! ### The listener -/

/-- Told only that the speaker spoke, the listener expects content at least as surprising as the
prior's entropy: the decision to speak cues informative content. -/
theorem measureEntropy_le_integral_surprisal (hα : 0 < α) :
    Hm[μ] ≤ ∫ v, (surprisal μ v).toReal ∂listener μ (spoke μ α cs cn) true := by
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun v ↦ μ {v}) (by rw [sum_measure_singleton, Finset.coe_univ, measure_univ]; simp)
  have : Nonempty W := ⟨v⟩
  have hx : (spoke μ α cs cn ∘ₘ μ) {true} ≠ 0 :=
    Measure.comp_apply_singleton_ne_zero _ _ hv
      ((spoke_apply_true_eq_zero_iff μ α cs cn hα).not.2 hv)
  rw [measureEntropy_eq_integral_surprisal μ (.of_finite), listener_apply_eq_posterior _ _ hx]
  refine integral_le_integral_posterior _ _ hx fun i j hij ↦ ?_
  dsimp only at hij
  rcases eq_or_ne (μ {i}) 0 with hi | hi
  · rw [surprisal_eq_top_iff.2 hi, ENNReal.toReal_top]
    exact ENNReal.toReal_nonneg
  rcases eq_or_ne (μ {j}) 0 with hj | hj
  · rw [measureReal_def (μ := spoke μ α cs cn j),
      (spoke_apply_true_eq_zero_iff μ α cs cn hα).2 hj, ENNReal.toReal_zero] at hij
    exact absurd hij measureReal_nonneg.not_gt
  rw [spoke_real_true μ α cs cn hα hi, spoke_real_true μ α cs cn hα hj, Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left hα, sub_lt_sub_iff_right] at hij
  exact hij.le

omit [Fintype W] [DiscreteMeasurableSpace W] in
private theorem surprisal_lt_surprisal {a t : W} (ha : μ {a} ≠ 0) (h : μ {a} < μ {t}) :
    (surprisal μ t).toReal < (surprisal μ a).toReal := by
  rw [toReal_surprisal prob_le_one, toReal_surprisal prob_le_one, neg_lt_neg_iff]
  exact Real.log_lt_log (ENNReal.toReal_pos ha (measure_ne_top _ _))
    ((ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 h)

omit [Fintype W] [DiscreteMeasurableSpace W] in
private theorem odds_pos {a t : W} (ha : μ {a} ≠ 0) (h : μ {a} < μ {t}) :
    0 < μ.real {a} / μ.real {t} :=
  div_pos (ENNReal.toReal_pos ha (measure_ne_top _ _))
    (ENNReal.toReal_pos (pos_of_gt h).ne' (measure_ne_top _ _))

/-- Of the two values offered, learning that the speaker spoke raises the odds of the less probable
one, as announcing does over thinking (p. 122) and speaking out of the blue over answering
(p. 124). -/
theorem prior_odds_lt_listener_odds (hα : 0 < α) {t a : W} (ha : μ {a} ≠ 0)
    (h : μ {a} < μ {t}) :
    μ.real {a} / μ.real {t} <
      (listener μ (spoke μ α cs cn) true).real {a} /
        (listener μ (spoke μ α cs cn) true).real {t} := by
  rw [listener_real_singleton_div, mul_div_mul_comm, spoke_real_true μ α cs cn hα ha,
    spoke_real_true μ α cs cn hα (pos_of_gt h).ne']
  refine lt_mul_of_one_lt_right (odds_pos μ ha h)
    ((one_lt_div (Real.sigmoid_pos _)).2 (Real.sigmoid_lt ?_))
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right (surprisal_lt_surprisal μ ha h) _) hα

-- The ratio of the logistic at two points rises as both are lowered alike.
private theorem sigmoid_div_sigmoid_lt {k x y d₁ d₂ : ℝ} (hk : 0 < k) (hxy : y < x)
    (hd : d₁ < d₂) :
    Real.sigmoid (k * (x - d₁)) / Real.sigmoid (k * (y - d₁)) <
      Real.sigmoid (k * (x - d₂)) / Real.sigmoid (k * (y - d₂)) := by
  have hD := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hd hk)
  have hP := Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left hxy hk)
  simp only [Real.sigmoid_def, inv_div_inv, mul_sub, neg_sub, Real.exp_sub]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  field_simp
  nlinarith [mul_pos (sub_pos.2 hD) (sub_pos.2 hP), Real.exp_pos (k * x), Real.exp_pos (k * y),
    Real.exp_pos (k * d₁), Real.exp_pos (k * d₂)]

/-- The cheaper silence is relative to speaking, the more the listener favours the atypical value,
as when the speaker addresses a crowd rather than one person (p. 125). -/
theorem listener_odds_lt_of_silence_lt (hα : 0 < α) {cn₁ cn₂ : ℝ} (hcn : cn₂ < cn₁) {t a : W}
    (ha : μ {a} ≠ 0) (h : μ {a} < μ {t}) :
    (listener μ (spoke μ α cs cn₁) true).real {a} /
        (listener μ (spoke μ α cs cn₁) true).real {t} <
      (listener μ (spoke μ α cs cn₂) true).real {a} /
        (listener μ (spoke μ α cs cn₂) true).real {t} := by
  have ht : μ {t} ≠ 0 := (pos_of_gt h).ne'
  rw [listener_real_singleton_div, listener_real_singleton_div, mul_div_mul_comm,
    mul_div_mul_comm, spoke_real_true μ α cs cn₁ hα ha, spoke_real_true μ α cs cn₁ hα ht,
    spoke_real_true μ α cs cn₂ hα ha, spoke_real_true μ α cs cn₂ hα ht]
  exact mul_lt_mul_of_pos_left
    (sigmoid_div_sigmoid_lt hα (surprisal_lt_surprisal μ ha h) (sub_lt_sub_left hcn cs))
    (odds_pos μ ha h)

/-- A speaker who was asked cannot stay silent, so that she spoke tells the listener nothing and
her guess is the prior, as for a thought (p. 124). -/
theorem listener_asked_eq_prior (hα : 0 < α) :
    listener μ ((askedS μ α cs).map fun _ ↦ true) true = μ := by
  have h1 (v : W) : (askedS μ α cs).map (fun _ ↦ true) v {true} * μ {v} = μ {v} := by
    rcases eq_or_ne (μ {v}) 0 with hv | hv
    · rw [hv, mul_zero]
    have := isProbabilityMeasure_speaker_dirac hα.le (fun _ ↦ cs)
      (listener μ (truthful fun v ↦ ({v} : Set W))) (w := v)
      ⟨v, by rw [listener_truthful_apply_singleton_of_eq_singleton μ _ rfl hv]; exact one_ne_zero⟩
    rw [Kernel.map_apply' _ measurable_const _ (.singleton true),
      Set.preimage_const_of_mem (Set.mem_singleton true), askedS, measure_univ, one_mul]
  refine Measure.ext_of_singleton fun w ↦ ?_
  rw [listener_apply_singleton, h1, Finset.sum_congr rfl fun v _ ↦ h1 v, sum_measure_singleton,
    Finset.coe_univ, measure_univ, div_one]

end RohdeEtAl2022
