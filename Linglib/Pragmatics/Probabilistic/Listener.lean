module

public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Core.Probability.Kernel.OfDensity
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.UniformOn

/-!
# The listener of the Rational Speech Act model

Frank and Goodman's Rational Speech Act model, the Bayesian member of the family Franke and Jäger
call probabilistic pragmatics, in mathlib's probability vocabulary. The
[listener](##RSA.listener) reweights a prior by the mass each state's measure gives the utterance
heard. At the channel of a speaker who is only [truthful](##RSA.truthful) she is the [literal
listener](##RSA.literalListener), who [conditions the prior on the
extension](##RSA.literalListener_apply), and at a
speaker the pragmatic listener, [mathlib's posterior](##RSA.listener_apply_eq_posterior). Where
the speaker gives an utterance one mass throughout an event, the listener who conditions on the
event [holds the prior conditioned on it](##RSA.cond_listener_apply).

## Implementation notes

* Equation numbers are those of Degen's review (eqs. 1–4) and of Franke and Bergen's comparison of
  latent-variable variants (eqs. 5–22).
* Meaning and prior are arguments, so findings quantify over them.

## References

* [M. C. Frank and N. D. Goodman, *Predicting Pragmatic Reasoning in Language Games*
  (2012)][frank-goodman-2012]
* [J. Degen, *The Rational Speech Act Framework* (2023)][degen-2023]
* [M. Franke and L. Bergen, *Theory-Driven Statistical Modeling for Semantics and Pragmatics: A
  Case Study on Grammatically Generated Implicature Readings* (2020)][franke-bergen-2020]
* [franke-jager-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

section Truthful

variable {W U : Type*} [MeasurableSpace U]

/-- The channel of a speaker who is only required to be truthful. The denotation `sem` gives each
utterance the set of states it is true at, and the channel puts mass one on each utterance true at
the state. For utterances that denote sets of states, `sem` is `fun u ↦ ⟦u⟧`, and its value at a
lexicon, a threshold or a context when the denotation depends on one. -/
noncomputable def truthful (sem : U → Set W) (w : W) : Measure U :=
  Measure.count.restrict {u | w ∈ sem u}

instance [Finite U] (sem : U → Set W) (w : W) : IsFiniteMeasure (truthful sem w) :=
  inferInstanceAs (IsFiniteMeasure (Measure.count.restrict _))

theorem truthful_apply_singleton [MeasurableSingletonClass U] (sem : U → Set W) (w : W) (u : U) :
    truthful sem w {u} = (sem u).indicator 1 w := by
  rw [truthful, Measure.restrict_apply (.singleton u)]
  by_cases h : w ∈ sem u
  · rw [Set.indicator_of_mem h, Set.inter_eq_left.2 (by simpa using h), Measure.count_singleton,
      Pi.one_apply]
  · rw [Set.indicator_of_notMem h, Set.singleton_inter_eq_empty.2 (by simpa using h),
      measure_empty]

end Truthful

section Pipeline

variable {W U O : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSpace O]

private theorem sum_mul_eq_comp_apply_singleton [Fintype W] [MeasurableSingletonClass W]
    [MeasurableSingletonClass U] (μ : Measure W) (κ : Kernel W U) (u : U) :
    ∑ w, κ w {u} * μ {w} = (κ ∘ₘ μ) {u} := by
  rw [Measure.comp_apply_singleton]
  exact Finset.sum_congr rfl fun w _ ↦ mul_comm _ _

/-! #### The listener

A listener holds a prior over states and takes the utterance to come from a channel, a measure on
utterances at each state. She reweights the prior by the mass each state's measure gives the
utterance she hears and normalizes, which is Bayes' rule with the zero measure at an utterance no
state she entertains produces. The literal listener (eq. 1) takes the speaker to be truthful and
no more, and so conditions the prior on the denotation of the utterance. The pragmatic listener
(eq. 3) takes the channel of a speaker, and is mathlib's posterior wherever the utterance is
heard. -/

section Listener

variable [Countable U] [MeasurableSingletonClass U]

/-- The listener reweights the prior `μ` by the mass each state's measure `S w` gives the
utterance heard, and normalizes. Her row at an utterance that no state of positive prior produces
is the zero measure. -/
noncomputable def listener (μ : Measure W) (S : W → Measure U) : Kernel U W :=
  Kernel.ofDensity μ fun u w ↦ S w {u}

section

variable (μ : Measure W) (S : W → Measure U)

theorem listener_apply (u : U) :
    listener μ S u = (μ.withDensity fun w ↦ S w {u})[|Set.univ] := rfl

instance (u : U) : IsZeroOrProbabilityMeasure (listener μ S u) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.ofDensity μ _ u))

instance : IsFiniteKernel (listener μ S) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity μ _))

/-- Bayes' rule ignores a constant factor in the likelihood: the listener reads two utterances
alike when, at every state, the mass of one is a positive multiple of the mass of the other. -/
theorem listener_apply_eq_of_apply_singleton_eq_mul {μ : Measure W} {S : W → Measure U}
    {u u' : U} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ w, S w {u'} = c * S w {u}) :
    listener μ S u' = listener μ S u :=
  Kernel.ofDensity_apply_eq_of_eq_mul μ (f := fun _ w ↦ S w {u}) hc0 hc h

/-- **Sufficiency.** Where the speaker gives the utterance one positive mass throughout an event,
the listener who conditions on the event holds the prior conditioned on it: within the event the
utterance tells her nothing. -/
theorem cond_listener_apply {μ : Measure W} {S : W → Measure U} {u : U} {s : Set W}
    (hs : MeasurableSet s) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (h : ∀ w ∈ s, S w {u} = c)
    (hfin : ∫⁻ w, S w {u} ∂μ ≠ ∞) : (listener μ S u)[|s] = μ[|s] := by
  rw [listener_apply, cond_cond_eq_cond_inter' .univ hs
    (by rwa [withDensity_apply _ .univ, Measure.restrict_univ]), Set.univ_inter]
  exact cond_withDensity_of_forall_mem_eq μ hs hc0 hc h

/-- The listener who conditions on an event of positive prior holds the prior conditioned on it
exactly when the speaker's mass on the utterance is almost surely one positive constant on the
event. -/
theorem cond_listener_apply_eq_iff {μ : Measure W} [IsFiniteMeasure μ] {S : W → Measure U} {u : U}
    {s : Set W} (hs : MeasurableSet s) (hS : AEMeasurable (fun w ↦ S w {u}) (μ.restrict s))
    (h0 : μ s ≠ 0) (hfin : ∫⁻ w, S w {u} ∂μ ≠ ∞) :
    (listener μ S u)[|s] = μ[|s] ↔ ∃ c, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ᵐ w ∂μ.restrict s, S w {u} = c := by
  rw [listener_apply, cond_cond_eq_cond_inter' .univ hs
    (by rwa [withDensity_apply _ .univ, Measure.restrict_univ]), Set.univ_inter]
  exact cond_withDensity_eq_cond_iff μ hs hS h0 (measure_ne_top _ _)

/-- An utterance does not raise the probability of an event when the speaker's mass on it,
integrated over the event and weighted by the prior of the complement, is at most her mass
integrated over the complement and weighted by the prior of the event. -/
theorem listener_apply_le_of_setLIntegral_mul_le {μ : Measure W} [IsProbabilityMeasure μ]
    {S : W → Measure U} {u : U} {E : Set W} (hE : MeasurableSet E)
    (h : (∫⁻ w in E, S w {u} ∂μ) * μ Eᶜ ≤ (∫⁻ w in Eᶜ, S w {u} ∂μ) * μ E) :
    listener μ S u E ≤ μ E := by
  rw [listener_apply, cond_apply .univ, Set.univ_inter, withDensity_apply _ .univ,
    withDensity_apply _ hE, Measure.restrict_univ, ← lintegral_add_compl _ hE,
    ← ENNReal.div_eq_inv_mul]
  refine ENNReal.div_le_of_le_mul ?_
  calc ∫⁻ w in E, S w {u} ∂μ
      = (∫⁻ w in E, S w {u} ∂μ) * μ E + (∫⁻ w in E, S w {u} ∂μ) * μ Eᶜ := by
        rw [← mul_add, prob_add_prob_compl hE, mul_one]
    _ ≤ (∫⁻ w in E, S w {u} ∂μ) * μ E + (∫⁻ w in Eᶜ, S w {u} ∂μ) * μ E := by gcongr
    _ = μ E * ((∫⁻ w in E, S w {u} ∂μ) + ∫⁻ w in Eᶜ, S w {u} ∂μ) := by ring

variable [MeasurableSingletonClass W]

theorem listener_apply_singleton' (u : U) (w : W) :
    listener μ S u {w} = S w {u} * μ {w} / ∫⁻ w', S w' {u} ∂μ :=
  Kernel.ofDensity_apply_singleton' μ _ u w

variable [Fintype W]

theorem listener_apply_singleton (u : U) (w : W) :
    listener μ S u {w} = S w {u} * μ {w} / ∑ w', S w' {u} * μ {w'} :=
  Kernel.ofDensity_apply_singleton μ _ u w

theorem listener_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W'] [MeasurableSpace U']
    [Countable U'] [MeasurableSingletonClass U'] [Fintype W'] [MeasurableSingletonClass W']
    (e : W ≃ W') {μ' : Measure W'} {S' : W' → Measure U'} {u : U} {u' : U'}
    (hμ : ∀ w, μ' {e w} = μ {w}) (hS : ∀ w, S' (e w) {u'} = S w {u}) (w : W) :
    listener μ' S' u' {e w} = listener μ S u {w} :=
  Kernel.ofDensity_apply_singleton_of_equiv e hμ hS w

variable {μ S} {u : U} {w : W}

theorem listener_apply_singleton_eq_zero (h : S w {u} = 0) : listener μ S u {w} = 0 := by
  rw [listener_apply_singleton, h, zero_mul, ENNReal.zero_div]

theorem ne_zero_of_listener_apply_singleton_ne_zero (h : listener μ S u {w} ≠ 0) :
    μ {w} ≠ 0 ∧ S w {u} ≠ 0 := by
  rw [listener_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or] at h
  exact ⟨right_ne_zero_of_mul h.1, left_ne_zero_of_mul h.1⟩

variable [IsFiniteMeasure μ] [∀ w, IsFiniteMeasure (S w)]

theorem listener_apply_singleton_ne_zero (hμ : μ {w} ≠ 0) (hS : S w {u} ≠ 0) :
    listener μ S u {w} ≠ 0 := by
  rw [listener_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨mul_ne_zero hS hμ,
    ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)⟩

theorem listener_apply_singleton_ne_zero_iff :
    listener μ S u {w} ≠ 0 ↔ μ {w} ≠ 0 ∧ S w {u} ≠ 0 :=
  ⟨ne_zero_of_listener_apply_singleton_ne_zero, fun h ↦ listener_apply_singleton_ne_zero h.1 h.2⟩

end

/-! ##### Events

Bayes' rule on reals, for the mass of a state and of a finite event. It holds at every utterance,
since an utterance that no state of positive prior produces gives the zero row and a zero
normalizer. -/

section Event

variable [Fintype W] [MeasurableSingletonClass W] (μ : Measure W) (S : W → Measure U)

theorem listener_apply_singleton_congr {u : U} {w₁ w₂ : W} (hS : S w₁ {u} = S w₂ {u})
    (hμ : μ {w₁} = μ {w₂}) : listener μ S u {w₁} = listener μ S u {w₂} := by
  rw [listener_apply_singleton, listener_apply_singleton, hS, hμ]

/-- Bayes' rule keeps the prior odds of two states that give the utterance the same mass. -/
theorem listener_apply_singleton_mul_eq_of_apply_eq {u : U} {w₁ w₂ : W}
    (hS : S w₁ {u} = S w₂ {u}) : listener μ S u {w₁} * μ {w₂} = listener μ S u {w₂} * μ {w₁} := by
  rw [listener_apply_singleton, listener_apply_singleton, hS, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul]
  ring

theorem listener_apply_finset (u : U) (E : Finset W) :
    listener μ S u ↑E = (∑ w ∈ E, S w {u} * μ {w}) / ∑ w, S w {u} * μ {w} := by
  rw [listener, Kernel.ofDensity_eq_ofWeights, Kernel.ofWeights_apply_finset]

variable [IsFiniteMeasure μ] [∀ w, IsFiniteMeasure (S w)]

theorem isProbabilityMeasure_listener_of_ne_zero {u : U} {w : W} (hμ : μ {w} ≠ 0)
    (hS : S w {u} ≠ 0) : IsProbabilityMeasure (listener μ S u) := by
  refine Kernel.isProbabilityMeasure_ofDensity μ _ u ?_ ?_ <;> rw [lintegral_fintype]
  · exact fun h ↦ mul_ne_zero hS hμ (Finset.sum_eq_zero_iff.1 h w (Finset.mem_univ w))
  · exact ENNReal.sum_ne_top.2 fun _ _ ↦
      ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

theorem listener_real_finset (u : U) (E : Finset W) :
    (listener μ S u).real ↑E =
      (∑ w ∈ E, μ.real {w} * (S w).real {u}) / ∑ w, μ.real {w} * (S w).real {u} := by
  rw [listener, Kernel.ofDensity_eq_ofWeights, Kernel.ofWeights_real_finset]
  · simp only [ENNReal.toReal_mul, measureReal_def, mul_comm]
  · exact fun _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

theorem listener_real_singleton (u : U) (w : W) :
    (listener μ S u).real {w} =
      μ.real {w} * (S w).real {u} / ∑ w', μ.real {w'} * (S w').real {u} := by
  simpa using listener_real_finset μ S u {w}

/-- Bayes' rule in odds form: the posterior odds of two states are their prior odds times the ratio
of the masses they give the utterance, at every utterance, heard or not. -/
theorem listener_real_singleton_div (u : U) (w₁ w₂ : W) :
    (listener μ S u).real {w₁} / (listener μ S u).real {w₂} =
      μ.real {w₁} * (S w₁).real {u} / (μ.real {w₂} * (S w₂).real {u}) := by
  rw [listener_real_singleton, listener_real_singleton]
  rcases eq_or_ne (∑ w, μ.real {w} * (S w).real {u}) 0 with h | h
  · have h0 (w : W) : μ.real {w} * (S w).real {u} = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ mul_nonneg measureReal_nonneg
        measureReal_nonneg).1 h w (Finset.mem_univ w)
    simp only [h0, zero_div]
  · exact div_div_div_cancel_right₀ h _ _

/-- The listener prefers the event with the greater prior-weighted production probability, at
every utterance, heard or not. -/
theorem listener_real_finset_lt_iff (u : U) (E₁ E₂ : Finset W) :
    (listener μ S u).real ↑E₁ < (listener μ S u).real ↑E₂ ↔
      ∑ w ∈ E₁, μ.real {w} * (S w).real {u} < ∑ w ∈ E₂, μ.real {w} * (S w).real {u} := by
  have hnn (w : W) : 0 ≤ μ.real {w} * (S w).real {u} :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  rw [listener_real_finset, listener_real_finset]
  rcases (Finset.sum_nonneg fun w _ ↦ hnn w : 0 ≤ ∑ w, μ.real {w} * (S w).real {u}).eq_or_lt
    with h | h
  · have h0 (E : Finset W) : ∑ w ∈ E, μ.real {w} * (S w).real {u} = 0 :=
      Finset.sum_eq_zero fun w _ ↦
        (Finset.sum_eq_zero_iff_of_nonneg fun w _ ↦ hnn w).1 h.symm w (Finset.mem_univ w)
    simp only [h0, zero_div]
  · exact div_lt_div_iff_of_pos_right h

/-- The listener prefers the state with the greater prior mass times production probability, at
every utterance, heard or not. -/
theorem listener_real_singleton_lt_iff (u : U) (w₁ w₂ : W) :
    (listener μ S u).real {w₁} < (listener μ S u).real {w₂} ↔
      μ.real {w₁} * (S w₁).real {u} < μ.real {w₂} * (S w₂).real {u} := by
  simpa using listener_real_finset_lt_iff μ S u {w₁} {w₂}

theorem listener_real_lt_of_certain {u : U} {E₁ E₂ : Finset W} {w₀ : W} (hw₀ : w₀ ∈ E₂)
    (hle : ∀ w, (S w).real {u} ≤ 1) (hs : S w₀ {u} = 1)
    (hlt : ∑ w ∈ E₁, μ.real {w} < μ.real {w₀}) :
    (listener μ S u).real ↑E₁ < (listener μ S u).real ↑E₂ := by
  rw [listener_real_finset_lt_iff]
  calc ∑ w ∈ E₁, μ.real {w} * (S w).real {u}
      ≤ ∑ w ∈ E₁, μ.real {w} :=
        Finset.sum_le_sum fun w _ ↦ mul_le_of_le_one_right measureReal_nonneg (hle w)
    _ < μ.real {w₀} := hlt
    _ = μ.real {w₀} * (S w₀).real {u} := by
        rw [measureReal_def (μ := S w₀), hs, ENNReal.toReal_one, mul_one]
    _ ≤ ∑ w ∈ E₂, μ.real {w} * (S w).real {u} :=
        Finset.single_le_sum (f := fun w ↦ μ.real {w} * (S w).real {u})
          (fun w _ ↦ mul_nonneg measureReal_nonneg measureReal_nonneg) hw₀

theorem listener_real_singleton_lt_iff_of_forall_eq (hμeq : ∀ w w', μ {w} = μ {w'})
    (hμ0 : ∀ w, μ {w} ≠ 0) (u : U) (w₁ w₂ : W) :
    (listener μ S u).real {w₁} < (listener μ S u).real {w₂} ↔
      (S w₁).real {u} < (S w₂).real {u} := by
  rw [listener_real_singleton_lt_iff,
    show μ.real {w₂} = μ.real {w₁} by rw [measureReal_def, measureReal_def, hμeq],
    mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real _ from ENNReal.toReal_pos (hμ0 _) (measure_ne_top _ _))]

end Event

/-! ##### The uniform prior

Against the uniform prior the prior cancels, and the listener's mass on a state is its share of
the production probability of the utterance. -/

section Uniform

variable [Fintype W] [MeasurableSingletonClass W] (S : W → Measure U)

theorem listener_uniformOn_univ_apply_singleton [Nonempty W] (u : U) (w : W) :
    listener (uniformOn Set.univ) S u {w} = S w {u} / ∑ w', S w' {u} :=
  Kernel.ofDensity_uniformOn_apply_singleton _ u w

variable [∀ w, IsFiniteMeasure (S w)]

theorem listener_uniformOn_univ_real_finset [Nonempty W] (u : U) (E : Finset W) :
    (listener (uniformOn Set.univ) S u).real ↑E =
      (∑ w ∈ E, (S w).real {u}) / ∑ w, (S w).real {u} := by
  rw [listener, Kernel.ofDensity_uniformOn_univ, Kernel.ofWeights_real_finset]
  · rfl
  · exact fun _ ↦ measure_ne_top _ _

theorem listener_uniformOn_real_lt_iff (u : U) (w₁ w₂ : W) :
    (listener (uniformOn Set.univ) S u).real {w₁} < (listener (uniformOn Set.univ) S u).real {w₂} ↔
      (S w₁).real {u} < (S w₂).real {u} :=
  listener_real_singleton_lt_iff_of_forall_eq _ S uniformOn_univ_singleton_eq
    uniformOn_univ_singleton_ne_zero u w₁ w₂

theorem listener_uniformOn_real_le_iff (u : U) (w₁ w₂ : W) :
    (listener (uniformOn Set.univ) S u).real {w₁} ≤ (listener (uniformOn Set.univ) S u).real {w₂} ↔
      (S w₁).real {u} ≤ (S w₂).real {u} :=
  not_lt.symm.trans ((not_congr (listener_uniformOn_real_lt_iff S u w₂ w₁)).trans not_lt)

theorem listener_uniformOn_real_finset_lt_iff (u : U) (E₁ E₂ : Finset W) :
    (listener (uniformOn Set.univ) S u).real ↑E₁ < (listener (uniformOn Set.univ) S u).real ↑E₂ ↔
      ∑ w ∈ E₁, (S w).real {u} < ∑ w ∈ E₂, (S w).real {u} := by
  rcases isEmpty_or_nonempty W with hW | hW
  · simp [Finset.eq_empty_of_isEmpty]
  · simp_rw [listener_real_finset_lt_iff, uniformOn_univ_real_singleton, ← Finset.mul_sum]
    exact mul_lt_mul_iff_right₀ (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

end Uniform

/-! ##### The listener of a kernel

When the channel is a kernel, the normalizer is the marginal probability of the utterance, the
listener is a probability measure exactly at the utterances that are heard, and there she is
mathlib's posterior. -/

section Kernel

variable [Fintype W] [MeasurableSingletonClass W] (μ : Measure W) (κ : Kernel W U)

theorem listener_apply_singleton_eq_div (u : U) (w : W) :
    listener μ κ u {w} = μ {w} * κ w {u} / (κ ∘ₘ μ) {u} := by
  rw [listener_apply_singleton, sum_mul_eq_comp_apply_singleton, mul_comm]

variable [IsFiniteMeasure μ] [IsFiniteKernel κ]

theorem isProbabilityMeasure_listener {u : U} (hu : (κ ∘ₘ μ) {u} ≠ 0) :
    IsProbabilityMeasure (listener μ κ u) := by
  refine Kernel.isProbabilityMeasure_ofDensity μ _ u ?_ ?_ <;>
    rw [lintegral_fintype, sum_mul_eq_comp_apply_singleton]
  exacts [hu, measure_ne_top _ _]

theorem isMarkovKernel_listener (h : ∀ u, (κ ∘ₘ μ) {u} ≠ 0) : IsMarkovKernel (listener μ κ) :=
  ⟨fun u ↦ isProbabilityMeasure_listener μ κ (h u)⟩

theorem comp_real_mul_listener_real (u : U) (w : W) :
    (κ ∘ₘ μ).real {u} * (listener μ κ u).real {w} = μ.real {w} * (κ w).real {u} := by
  rw [measureReal_def, measureReal_def, measureReal_def, measureReal_def,
    listener_apply_singleton_eq_div]
  rcases eq_or_ne ((κ ∘ₘ μ) {u}) 0 with h | h
  · have h0 : μ {w} * κ w {u} = 0 := by
      rw [Measure.comp_apply_singleton] at h
      exact Finset.sum_eq_zero_iff.1 h w (Finset.mem_univ w)
    rw [h, ENNReal.toReal_zero, zero_mul, ← ENNReal.toReal_mul, h0, ENNReal.toReal_zero]
  · rw [← ENNReal.toReal_mul, ENNReal.mul_div_cancel h (measure_ne_top _ _), ENNReal.toReal_mul]

theorem listener_apply_eq_posterior [StandardBorelSpace W] [Nonempty W] {u : U}
    (hu : (κ ∘ₘ μ) {u} ≠ 0) : listener μ κ u = (κ†μ) u :=
  Kernel.ofDensity_apply_eq_posterior κ μ hu

end Kernel

theorem listener_dirac_apply (μ : Measure W) {f : W → U} (hf : Measurable f) (u : U) :
    listener μ (fun w ↦ Measure.dirac (f w)) u = μ[|f ⁻¹' {u}] := by
  rw [← Kernel.ofDensity_indicator_one_apply μ (fun u ↦ f ⁻¹' {u}) u (hf (.singleton u))]
  exact congrArg (Kernel.ofDensity μ · u) (funext fun u ↦ funext fun w ↦
    Measure.dirac_apply' _ (.singleton u))

/-! ##### The listener of a truthful speaker -/

section Truthful

/-- The literal listener is the listener of a speaker who is only truthful: she conditions the
prior on the denotation of the utterance. -/
noncomputable abbrev literalListener (μ : Measure W) (sem : U → Set W) : Kernel U W :=
  listener μ (truthful sem)

theorem literalListener_eq_ofDensity (μ : Measure W) (sem : U → Set W) :
    literalListener μ sem = Kernel.ofDensity μ fun u ↦ (sem u).indicator 1 :=
  congrArg (Kernel.ofDensity μ) (funext fun u ↦ funext fun w ↦ truthful_apply_singleton sem w u)

/-- The listener of a truthful speaker (eq. 1) conditions the prior on the denotation of the
utterance. -/
theorem literalListener_apply' (μ : Measure W) (sem : U → Set W) (u : U)
    (hs : MeasurableSet (sem u)) : literalListener μ sem u = μ[|sem u] := by
  rw [literalListener_eq_ofDensity]
  exact Kernel.ofDensity_indicator_one_apply μ sem u hs

theorem literalListener_apply [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)
    (u : U) : literalListener μ sem u = μ[|sem u] :=
  literalListener_apply' μ sem u .of_discrete

theorem literalListener_apply_univ [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)
    [IsFiniteMeasure μ] {u : U} (h : μ (sem u) ≠ 0) : literalListener μ sem u Set.univ = 1 := by
  rw [literalListener_apply]
  have := cond_isProbabilityMeasure (μ := μ) h
  exact measure_univ

section Boolean

variable [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)

theorem literalListener_apply_singleton {u : U} {w : W} (h : w ∈ sem u) :
    literalListener μ sem u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [literalListener_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

theorem literalListener_apply_singleton_of_notMem {u : U} {w : W} (h : w ∉ sem u) :
    literalListener μ sem u {w} = 0 := by
  rw [literalListener_apply, cond_apply .of_discrete, Set.inter_comm,
    Set.singleton_inter_eq_empty.mpr h, measure_empty, mul_zero]

theorem literalListener_real_singleton {u : U} {w : W} (h : w ∈ sem u) :
    (literalListener μ sem u).real {w} = μ.real {w} / μ.real (sem u) := by
  rw [measureReal_def, literalListener_apply_singleton μ sem h, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_inv_mul, measureReal_def, measureReal_def]

theorem literalListener_apply_singleton_of_eq_univ [IsProbabilityMeasure μ] {u : U}
    (h : sem u = Set.univ) (w : W) : literalListener μ sem u {w} = μ {w} := by
  rw [literalListener_apply_singleton μ sem (by rw [h]; exact Set.mem_univ w), h, measure_univ,
    inv_one, one_mul]

theorem literalListener_apply_singleton_of_eq_singleton [IsFiniteMeasure μ] {u : U} {w : W}
    (h : sem u = {w}) (hμ : μ {w} ≠ 0) : literalListener μ sem u {w} = 1 := by
  rw [literalListener_apply_singleton μ sem (by rw [h]; exact Set.mem_singleton w), h,
    ENNReal.inv_mul_cancel hμ (measure_ne_top _ _)]

theorem literalListener_apply_singleton_ne_zero_iff [IsFiniteMeasure μ] (u : U) (w : W) :
    literalListener μ sem u {w} ≠ 0 ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  by_cases h : w ∈ sem u
  · rw [literalListener_apply_singleton μ sem h]
    exact ⟨fun h' ↦ ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      fun h' ↦ mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [literalListener_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (fun h' ↦ h' rfl) fun h' ↦ h h'.1

theorem literalListener_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [DiscreteMeasurableSpace W'] [MeasurableSpace U'] [Countable U'] [MeasurableSingletonClass U']
    [Fintype W] [Fintype W'] (e : W ≃ W') {μ : Measure W} {μ' : Measure W'} {sem : U → Set W}
    {sem' : U' → Set W'} {u : U} {u' : U'} (hμ : ∀ w, μ' {e w} = μ {w})
    (hsem : ∀ w, e w ∈ sem' u' ↔ w ∈ sem u) (w : W) :
    literalListener μ' sem' u' {e w} = literalListener μ sem u {w} := by
  rw [literalListener_eq_ofDensity, literalListener_eq_ofDensity]
  refine Kernel.ofDensity_apply_singleton_of_equiv e hμ (fun w ↦ ?_) w
  by_cases h : w ∈ sem u
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsem w).2 h), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (hsem w).1 h)]

end Boolean

end Truthful

end Listener

end Pipeline

/-! ### Answers and coordinates -/

section Map

variable {W U X : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A literal listener's probability of an answer is the prior mass of the states with that
answer where the utterance is true, over the prior mass of the states where it is true. -/
theorem literalListener_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] (μ : Measure W) (sem : U → Set W) (q : W → X) (u : U) (x : X) :
    (literalListener μ sem).map q u {x} = μ (sem u ∩ q ⁻¹' {x}) / μ (sem u) := by
  rw [Kernel.map_apply_singleton, literalListener_apply, cond_apply .of_discrete,
    ENNReal.div_eq_inv_mul]

/-- Within a finite context set, a literal listener's probability of an answer is the prior mass
of the states of the set where the utterance is true and that have the answer, over the prior
mass of the states of the set where it is true. -/
theorem listener_restrict_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] [DecidableEq X] (μ : Measure W) (C : Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (q : W → X) (u : U) (x : X) :
    (literalListener (μ.restrict ↑C) sem).map q u {x} =
      μ ↑((C.filter (· ∈ sem u)).filter (q · = x)) / μ ↑(C.filter (· ∈ sem u)) := by
  rw [literalListener_map_apply_singleton, Measure.restrict_apply .of_discrete,
    Measure.restrict_apply .of_discrete]
  congr 2 <;> ext <;> simp [and_comm, and_left_comm]

end Map

section Coordinate

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [DiscreteMeasurableSpace A]
  [Countable A] (π π' : Measure A) [IsFiniteMeasure π]
  [IsFiniteMeasure π'] (κ : Kernel A B) [IsMarkovKernel κ]

omit [IsFiniteMeasure π'] in
/-- At a prior that composes a prior over the coordinate named with a kernel to the rest, the
literal listener of an utterance that names a value of positive prior believes that value and the
kernel there. -/
theorem literalListener_preimage_fst_compProd {a : A} (ha : π {a} ≠ 0) :
    literalListener (π ⊗ₘ κ) (fun a : A ↦ (Prod.fst ⁻¹' {a} : Set (A × B))) a =
      Measure.dirac a ⊗ₘ κ := by
  rw [literalListener_apply' (π ⊗ₘ κ) _ a (measurable_fst (measurableSet_singleton a))]
  exact Measure.cond_preimage_fst_singleton_compProd π κ ha (measure_ne_top _ _)

/-- The literal listener of utterances that name a coordinate does not depend on the prior over
that coordinate, so long as it leaves every value possible. -/
theorem literalListener_preimage_fst_compProd_congr (hπ : ∀ a, π {a} ≠ 0)
    (hπ' : ∀ a, π' {a} ≠ 0) :
    literalListener (π ⊗ₘ κ) (fun a : A ↦ (Prod.fst ⁻¹' {a} : Set (A × B))) =
      literalListener (π' ⊗ₘ κ) (fun a : A ↦ (Prod.fst ⁻¹' {a} : Set (A × B))) :=
  Kernel.ext fun a ↦ by
    rw [literalListener_preimage_fst_compProd π κ (hπ a),
      literalListener_preimage_fst_compProd π' κ (hπ' a)]

end Coordinate

end RSA
