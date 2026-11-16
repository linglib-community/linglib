module

public import Linglib.Pragmatics.Probabilistic.Listener
public import Linglib.Pragmatics.Probabilistic.Speaker

/-!
# The speaker against the literal listener

Against the literal listener the speaker [sees her belief only through the utterances it
entails](##RSA.speaker_literalListener_apply_eq_iff), and when she knows the state she [produces
exactly the utterances true there](##RSA.speaker_literalListener_dirac_apply_singleton_ne_zero_iff).
The pragmatic listener is the listener of this speaker.

## References

* [M. C. Frank and N. D. Goodman, *Predicting Pragmatic Reasoning in Language Games*
  (2012)][frank-goodman-2012]
* [J. Degen, *The Rational Speech Act Framework* (2023)][degen-2023]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

/-! #### The speaker against a graded meaning

The listener of a graded meaning reweights the prior by the meaning of the utterance. The prior,
which no utterance changes, cancels from the speaker's choice, and she weighs an utterance by the
geometric mean of its meaning over her belief against the meaning's prior mass. -/

section Graded

variable [Fintype W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [Countable O] [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {b : O → Measure W} {o : O}
  {μ : Measure W} {m : U → W → ℝ≥0∞}

private theorem geomMean_ofDensity (β : Measure W) [IsProbabilityMeasure β] (u : U) :
    β.geomMean (fun w ↦ Kernel.ofDensity μ m u {w}) =
      β.geomMean (fun w ↦ μ {w}) * (β.geomMean (m u) * (∑ w, m u w * μ {w})⁻¹) := by
  simp only [Kernel.ofDensity_apply_singleton, div_eq_mul_inv, Measure.geomMean_mul,
    Measure.geomMean_const]
  ring

variable [IsFiniteMeasure μ]

/-- Against the listener of a graded meaning the speaker weighs an utterance by the geometric mean
of its meaning over her belief and by the inverse of the meaning's prior mass. -/
theorem speaker_ofDensity_apply_singleton (hα : 0 ≤ α) [IsProbabilityMeasure (b o)]
    (hb : b o ≪ μ) (u : U) :
    speaker α C (Kernel.ofDensity μ m) b o {u} =
      (b o).geomMean (m u) ^ α * ((∑ w, m u w * μ {w})⁻¹ ^ α *
          ENNReal.ofReal (Real.exp (-(α * C u)))) /
        ∑ u', (b o).geomMean (m u') ^ α * ((∑ w, m u' w * μ {w})⁻¹ ^ α *
          ENNReal.ofReal (Real.exp (-(α * C u')))) := by
  have h0 : (b o).geomMean (fun w ↦ μ {w}) ^ α ≠ 0 :=
    ENNReal.rpow_ne_zero_of_ne_zero hα (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ))
  have htop : (b o).geomMean (fun w ↦ μ {w}) ^ α ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hα
    (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)
  simp only [speaker_apply_singleton, geomMean_ofDensity,
    ENNReal.mul_rpow_of_nonneg _ _ hα, mul_assoc]
  rw [← Finset.mul_sum, ENNReal.mul_div_mul_left _ _ h0 htop]

theorem speaker_ofDensity_apply_congr (hα : 0 ≤ α) {o₁ o₂ : O}
    [IsProbabilityMeasure (b o₁)] [IsProbabilityMeasure (b o₂)] (h₁ : b o₁ ≪ μ) (h₂ : b o₂ ≪ μ)
    (h : ∀ u, (b o₂).geomMean (m u) = (b o₁).geomMean (m u)) :
    speaker α C (Kernel.ofDensity μ m) b o₂ = speaker α C (Kernel.ofDensity μ m) b o₁ :=
  Measure.ext_of_singleton fun u ↦ by
    simp only [speaker_ofDensity_apply_singleton hα h₂,
      speaker_ofDensity_apply_singleton hα h₁, h]

end Graded

/-! #### The speaker against the literal listener

The literal listener gives a state at which an utterance is true the prior's mass there over the
prior mass of the utterance's extension. A speaker who addresses her therefore produces exactly the
utterances her belief entails, weighs each by the inverse of its extension's prior mass to the power
`α` and by its cost, and sees her belief only through the utterances it entails. -/

section Literal

variable [Fintype W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [Countable O] [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} {b : O → Measure W} {o : O}
  {μ : Measure W} {sem : U → Set W} {u u' : U}

private theorem geomMean_literalListener (β : Measure W) [IsProbabilityMeasure β] (u : U) :
    β.geomMean (fun w ↦ literalListener μ sem u {w}) =
      β.geomMean (fun w ↦ μ {w}) * (β.geomMean ((sem u).indicator 1) * (μ (sem u))⁻¹) := by
  rw [literalListener_eq_ofDensity, geomMean_ofDensity]
  congr 3
  rw [← lintegral_fintype, lintegral_indicator_one .of_discrete]

variable [IsFiniteMeasure μ]

theorem speaker_literalListener_apply_singleton_eq_zero_iff (hα : 0 < α) [IsFiniteMeasure (b o)]
    (hb : b o ≪ μ) :
    speaker α C (literalListener μ sem) b o {u} = 0 ↔ ¬ ∀ᵐ w ∂b o, w ∈ sem u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, ae_iff_of_countable, not_forall]
  refine exists_congr fun w ↦ ?_
  rw [Classical.not_imp]
  refine and_congr_right fun hw ↦ ?_
  rw [← not_iff_not, not_not, ← ne_eq, literalListener_apply_singleton_ne_zero_iff]
  exact and_iff_left fun h ↦ hw (hb h)

/-- Against the literal listener the speaker's mass on an utterance her belief entails is its
weight, the inverse of its extension's prior mass to the power `α` times the cost weight, over the
sum of the weights of the utterances her belief entails. -/
theorem speaker_literalListener_apply_singleton (hα : 0 < α) [IsProbabilityMeasure (b o)]
    (hb : b o ≪ μ) (u : U) :
    speaker α C (literalListener μ sem) b o {u} =
      {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) u /
        ∑ v, {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v := by
  classical
  have key (v : U) : (b o).geomMean (fun w ↦ literalListener μ sem v {w}) ^ α *
        ENNReal.ofReal (Real.exp (-(α * C v))) =
      (b o).geomMean (fun w ↦ μ {w}) ^ α * {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
        (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v := by
    rw [geomMean_literalListener, Measure.geomMean_indicator_one]
    by_cases hv : ∀ᵐ w ∂b o, w ∈ sem v
    · rw [ite_eq_left hv, Set.indicator_of_mem (show v ∈ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hv),
        one_mul, ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc]
    · rw [ite_eq_right hv, Set.indicator_of_notMem (show v ∉ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hv),
        zero_mul, mul_zero, ENNReal.zero_rpow_of_pos hα, zero_mul, mul_zero]
  rw [speaker_apply_singleton, key, Finset.sum_congr rfl fun v _ ↦ key v, ← Finset.mul_sum,
    ENNReal.mul_div_mul_left _ _
      (ENNReal.rpow_ne_zero_of_ne_zero hα.le (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ)))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _))]

variable {O' : Type*} [MeasurableSpace O'] [Countable O'] [MeasurableSingletonClass O']
  {b' : O' → Measure W} {o' : O'}

/-- Against the literal listener two beliefs yield the same speaker exactly when they entail the
same utterances. -/
theorem speaker_literalListener_apply_eq_iff (hα : 0 < α) [IsProbabilityMeasure (b o)]
    [IsProbabilityMeasure (b' o')] (hb : b o ≪ μ) (hb' : b' o' ≪ μ) :
    speaker α C (literalListener μ sem) b' o' = speaker α C (literalListener μ sem) b o ↔
      ∀ u, (∀ᵐ w ∂b' o', w ∈ sem u) ↔ ∀ᵐ w ∂b o, w ∈ sem u := by
  refine ⟨fun h u ↦ ?_, fun h ↦ Measure.ext_of_singleton fun u ↦ ?_⟩
  · rw [← not_iff_not, ← speaker_literalListener_apply_singleton_eq_zero_iff hα hb' (C := C),
      ← speaker_literalListener_apply_singleton_eq_zero_iff hα hb (C := C), h]
  · simp only [speaker_literalListener_apply_singleton hα hb,
      speaker_literalListener_apply_singleton hα hb', h]

/-- An utterance a belief entails loses mass to a belief that entails at least as much, whose
speaker has more to choose from. -/
theorem speaker_literalListener_apply_singleton_le (hα : 0 < α) [IsProbabilityMeasure (b o)]
    [IsProbabilityMeasure (b' o')] (hb : b o ≪ μ) (hb' : b' o' ≪ μ)
    (h : ∀ v, (∀ᵐ w ∂b o, w ∈ sem v) → ∀ᵐ w ∂b' o', w ∈ sem v) (hu : ∀ᵐ w ∂b o, w ∈ sem u) :
    speaker α C (literalListener μ sem) b' o' {u} ≤
      speaker α C (literalListener μ sem) b o {u} := by
  rw [speaker_literalListener_apply_singleton hα hb,
    speaker_literalListener_apply_singleton hα hb',
    Set.indicator_of_mem (show u ∈ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hu),
    Set.indicator_of_mem (show u ∈ {v | ∀ᵐ w ∂b' o', w ∈ sem v} from h u hu)]
  exact ENNReal.div_le_div_left (Finset.sum_le_sum fun v _ ↦
    Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le) v) _

/-- Among the utterances her belief entails, the speaker at no cost prefers the one of smaller
prior mass. -/
theorem speaker_zero_literalListener_real_singleton_lt_iff (hα : 0 < α)
    [IsProbabilityMeasure (b o)] (hb : b o ≪ μ) (hu : ∀ᵐ w ∂b o, w ∈ sem u)
    (hu' : ∀ᵐ w ∂b o, w ∈ sem u') :
    (speaker α 0 (literalListener μ sem) b o).real {u} <
        (speaker α 0 (literalListener μ sem) b o).real {u'} ↔
      μ (sem u') < μ (sem u) := by
  classical
  have h1 (v : U) (hv : ∀ᵐ w ∂b o, w ∈ sem v) : (b o).geomMean ((sem v).indicator 1) = 1 := by
    rw [Measure.geomMean_indicator_one, ite_eq_left hv]
  rw [speaker_real_singleton_lt_iff hα.le]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [ENNReal.rpow_lt_rpow_iff hα, geomMean_literalListener, geomMean_literalListener, h1 u hu,
    h1 u' hu', one_mul, one_mul,
    ENNReal.mul_lt_mul_iff_right (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ))
      (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _), ENNReal.inv_lt_inv]

end Literal

section Dirac

variable [MeasurableSingletonClass W]

private theorem ae_dirac_mem_iff {w : W} {t : Set W} : (∀ᵐ x ∂Measure.dirac w, x ∈ t) ↔ w ∈ t := by
  rw [ae_dirac_eq, Filter.eventually_pure]

variable [Fintype W] [Fintype U] {α : ℝ} {C : U → ℝ} {L : Kernel U W} {w : W} {u : U}

private theorem dirac_absolutelyContinuous {μ : Measure W} (h : μ {w} ≠ 0) :
    Measure.dirac w ≪ μ :=
  Measure.absolutelyContinuous_of_forall_singleton fun _ hw' ↦ of_not_not fun hd ↦
    h (Measure.eq_of_dirac_apply_singleton_ne_zero hd ▸ hw')

variable [MeasurableSingletonClass U]

theorem speaker_literalListener_dirac_eq_one (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    (hmem : w ∈ sem u) (hother : ∀ u' ≠ u, w ∉ sem u') :
    speaker α C (literalListener μ sem) Measure.dirac w {u} = 1 :=
  speaker_dirac_apply_singleton_eq_one hα
    (by
      rw [literalListener_apply_singleton μ sem hmem]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
    fun u' hu' ↦ literalListener_apply_singleton_of_notMem μ sem (hother u' hu')

theorem speaker_literalListener_dirac_apply_singleton_ne_zero_iff (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (u : U) (w : W) :
    speaker α C (literalListener μ sem) Measure.dirac w {u} ≠ 0
      ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  rw [speaker_dirac_apply_singleton_ne_zero_iff hα,
    literalListener_apply_singleton_ne_zero_iff μ sem u w]

theorem speaker_literalListener_dirac_apply_singleton_eq_zero (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) (h : w ∉ sem u) :
    speaker α C (literalListener μ sem) Measure.dirac w {u} = 0 :=
  speaker_dirac_apply_singleton_eq_zero hα (literalListener_apply_singleton_of_notMem μ sem h)

/-- A speaker who knows the state says only what is true there. -/
theorem ae_speaker_literalListener_dirac_mem (hα : 0 < α) (C : U → ℝ) (μ : Measure W)
    (sem : U → Set W) (w : W) :
    ∀ᵐ u ∂speaker α C (literalListener μ sem) Measure.dirac w, w ∈ sem u :=
  ae_iff_of_countable.2 fun _ hu ↦
    by_contra fun h ↦ hu (speaker_literalListener_dirac_apply_singleton_eq_zero hα C μ sem h)

theorem speaker_literalListener_dirac_real_singleton_eq_zero (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) (h : w ∉ sem u) :
    (speaker α C (literalListener μ sem) Measure.dirac w).real {u} = 0 := by
  rw [measureReal_def, speaker_literalListener_dirac_apply_singleton_eq_zero hα C μ sem h,
    ENNReal.toReal_zero]

section SingletonUniv

variable (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsProbabilityMeasure μ] (sem : U → Set W)
  (hμ : μ {w} ≠ 0) {u' : U} (huu' : u ≠ u') (hu : sem u = {w}) (hu' : sem u' = Set.univ)
  (hsupp : ∀ v, w ∈ sem v → v = u ∨ v = u')
include hα hμ huu' hu hu' hsupp

/-- A speaker who knows the state and can say only what is true there alone or what is true
everywhere says the first with the logistic probability of the cost it adds, less the log prior
of the state, discounted. -/
theorem speaker_literalListener_dirac_real_singleton_of_eq_singleton :
    (speaker α C (literalListener μ sem) Measure.dirac w).real {u} =
      Real.sigmoid (α * (C u' - C u - Real.log (μ.real {w}))) := by
  have h1 := literalListener_apply_singleton_of_eq_singleton μ sem hu hμ
  have h2 := literalListener_apply_singleton_of_eq_univ μ sem hu' w
  rw [speaker_dirac_real_singleton_of_pair hα huu' (h1 ▸ one_ne_zero) (h2 ▸ hμ) fun v hv ↦
      hsupp v ((literalListener_apply_singleton_ne_zero_iff μ sem v w).1 hv).1,
    h1, h2, ENNReal.toReal_one, Real.log_one, ← measureReal_def]
  congr 1; ring

theorem speaker_literalListener_dirac_real_singleton_of_eq_univ :
    (speaker α C (literalListener μ sem) Measure.dirac w).real {u'} =
      Real.sigmoid (α * (C u - C u' + Real.log (μ.real {w}))) := by
  have h1 := literalListener_apply_singleton_of_eq_singleton μ sem hu hμ
  have h2 := literalListener_apply_singleton_of_eq_univ μ sem hu' w
  rw [speaker_dirac_real_singleton_of_pair hα huu'.symm (h2 ▸ hμ) (h1 ▸ one_ne_zero) fun v hv ↦
      (hsupp v ((literalListener_apply_singleton_ne_zero_iff μ sem v w).1 hv).1).symm,
    h1, h2, ENNReal.toReal_one, Real.log_one, ← measureReal_def]
  congr 1; ring

end SingletonUniv

theorem speaker_literalListener_dirac_congr (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w w' : W} (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (h : ∀ u, w ∈ sem u ↔ w' ∈ sem u) :
    speaker α C (literalListener μ sem) Measure.dirac w'
      = speaker α C (literalListener μ sem) Measure.dirac w :=
  (speaker_literalListener_apply_eq_iff hα (dirac_absolutelyContinuous hw)
    (dirac_absolutelyContinuous hw')).2 fun u ↦ by
      rw [ae_dirac_mem_iff, ae_dirac_mem_iff, h u]

theorem speaker_literalListener_dirac_le_of_subset (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {w w' : W}
    (hw : μ {w} ≠ 0) (hsub : ∀ u, w ∈ sem u → w' ∈ sem u) {u : U} (hu : w ∈ sem u) :
    speaker α C (literalListener μ sem) Measure.dirac w' {u}
      ≤ speaker α C (literalListener μ sem) Measure.dirac w {u} := by
  rcases eq_or_ne (μ {w'}) 0 with hw' | hw'
  · rw [speaker_dirac_apply_singleton_eq_zero hα (not_not.mp fun h ↦
      ((literalListener_apply_singleton_ne_zero_iff μ sem u w').mp h).2 hw')]
    exact zero_le
  · exact speaker_literalListener_apply_singleton_le hα (dirac_absolutelyContinuous hw)
      (dirac_absolutelyContinuous hw')
      (fun v hv ↦ ae_dirac_mem_iff.2 (hsub v (ae_dirac_mem_iff.1 hv))) (ae_dirac_mem_iff.2 hu)

theorem speaker_literalListener_dirac_zero_real_singleton_of_pair (hα : 0 < α)
    (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    {u u' : U} (huu' : u ≠ u') (hu : w ∈ sem u) (hu' : w ∈ sem u')
    (hsupp : ∀ v, w ∈ sem v → v = u ∨ v = u') :
    (speaker α 0 (literalListener μ sem) Measure.dirac w).real {u} =
      μ.real (sem u') ^ α / (μ.real (sem u) ^ α + μ.real (sem u') ^ α) := by
  have hx : 0 < μ.real {w} := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  have hpos {v : U} (hv : w ∈ sem v) : 0 < μ.real (sem v) :=
    hx.trans_le (measureReal_mono (Set.singleton_subset_iff.2 hv))
  have hterm {v : U} (hv : w ∈ sem v) : (literalListener μ sem v {w} ^ α).toReal =
      μ.real {w} ^ α / μ.real (sem v) ^ α := by
    rw [← ENNReal.toReal_rpow, ← measureReal_def, literalListener_real_singleton μ sem hv,
      Real.div_rpow hx.le (hpos hv).le]
  rw [speaker_dirac_zero_real_singleton hα.le, Finset.sum_eq_add u u' huu' (fun v _ hv ↦ ?_)
      (by simp) (by simp), hterm hu, hterm hu']
  · have := hpos hu
    have := hpos hu'
    field_simp
    ring
  · rw [literalListener_apply_singleton_of_notMem μ sem fun h ↦ (hsupp v h).elim hv.1 hv.2,
      ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero]

end Dirac

/-! #### Pragmatic listeners

The pragmatic listener (eq. 3) is the listener of a speaker. -/

section Listener

variable [Fintype W] [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSingletonClass U]

theorem listener_speaker_literalListener_apply_singleton_of_notMem {α : ℝ} (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) {u : U} {w : W} (hw : w ∉ sem u) :
    listener μ (speaker α C (literalListener μ sem) Measure.dirac) u {w} = 0 :=
  listener_apply_singleton_eq_zero (speaker_dirac_apply_singleton_eq_zero hα
    (literalListener_apply_singleton_of_notMem μ sem hw))

end Listener

end Pipeline

end RSA
