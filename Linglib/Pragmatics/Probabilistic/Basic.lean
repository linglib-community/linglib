module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.MeasureTheory.Function.EssSup
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.GeomMean
public import Linglib.Core.MeasureTheory.Measure.Prod
public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Core.Probability.Kernel.OfDensity
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Posterior
public import Linglib.Core.Probability.Kernel.Softmax
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Data.EReal.BigOperators

/-!
# The Rational Speech Act pipeline on probability kernels

Frank and Goodman's Rational Speech Act model, the Bayesian member of the family Franke and Jäger
call probabilistic pragmatics, in mathlib's probability vocabulary. The
[listener](##RSA.listener) reweights a prior by the mass each state's measure gives the utterance
heard: at the channel of a speaker who is only truthful she is the literal listener, who
[conditions the prior on the extension](##RSA.listener_truthful_apply), and at a speaker the
pragmatic listener, [mathlib's posterior](##RSA.listener_apply_eq_posterior). The
[speaker](##RSA.speaker) believes a measure on states and is the softmax of her
[utility](##RSA.utility), the expected log of the listener's mass less a cost; against the literal
listener she [sees her belief only through the utterances it
entails](##RSA.speaker_listener_truthful_apply_eq_iff).

## Implementation notes

* Equation numbers are those of Degen's review (eqs. 1–4) and of Franke and Bergen's comparison of
  latent-variable variants (eqs. 5–22).
* Rationality, cost, meaning and prior are arguments, so findings quantify over them.
* A latent the speaker also knows is a coordinate of the state, and so is her choice when the
  listener hears only its form: the prior is then the joint of the world prior and the speaker.
* The decision rule is `Kernel.softmax`, so a speaker whose utility is not an expected
  log-probability, such as a question- or politeness-weighted one, is that rule at her own score,
  with `⊥` marking the utterances she cannot use.
* Boolean meanings at a uniform prior on finitely many states, where masses reduce to counting, are
  treated in `Linglib.Pragmatics.Probabilistic.Uniform`, and a latent whose prior is independent of
  the state's in `Linglib.Pragmatics.Probabilistic.LexicalUncertainty`.

## References

* [M. C. Frank and N. D. Goodman, *Predicting Pragmatic Reasoning in Language Games*
  (2012)][frank-goodman-2012]
* [J. Degen, *The Rational Speech Act Framework* (2023)][degen-2023]
* [L. Bergen, R. Levy and N. D. Goodman, *Pragmatic Reasoning through Semantic Inference*
  (2016)][bergen-levy-goodman-2016]
* [M. Franke and L. Bergen, *Theory-Driven Statistical Modeling for Semantics and Pragmatics: A
  Case Study on Grammatically Generated Implicature Readings* (2020)][franke-bergen-2020]
* [spector-2025]
* [goodman-stuhlmuller-2013]
* [franke-jager-2016]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The RSA pipeline -/

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

/-! ##### Marginals of a listener over a product

A latent the speaker also knows, a lexicon or a threshold or a question, is a coordinate of the
state: the speaker at a pair is `fun p ↦ speaker α C (L p.2) Measure.dirac p.1`, addressing that
latent's listener, and her listener holds a prior over pairs. Its marginals pool the
prior-weighted production probabilities over the other coordinate. When the prior over pairs is a
product, this is lexical uncertainty (`Linglib.Pragmatics.Probabilistic.LexicalUncertainty`). -/

section Prod

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Fintype A] [Fintype B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B] (μ : Measure (A × B))
  (S : A × B → Measure U) [IsFiniteMeasure μ] [∀ p, IsFiniteMeasure (S p)]

theorem listener_fst_apply_singleton_ne_zero_iff (u : U) (a : A) :
    (listener μ S u).fst {a} ≠ 0 ↔ ∃ b, μ {(a, b)} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  rw [Measure.fst_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, listener_apply_singleton_ne_zero_iff]

theorem listener_snd_apply_singleton_ne_zero_iff (u : U) (b : B) :
    (listener μ S u).snd {b} ≠ 0 ↔ ∃ a, μ {(a, b)} ≠ 0 ∧ S (a, b) {u} ≠ 0 := by
  rw [Measure.snd_apply_singleton, ne_eq, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, not_forall, listener_apply_singleton_ne_zero_iff]

theorem listener_fst_real_singleton (u : U) (a : A) :
    (listener μ S u).fst.real {a} =
      (∑ b, μ.real {(a, b)} * (S (a, b)).real {u}) / ∑ p, μ.real {p} * (S p).real {u} := by
  rw [Measure.fst_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun b _ ↦ listener_real_singleton μ S u (a, b)

theorem listener_snd_real_singleton (u : U) (b : B) :
    (listener μ S u).snd.real {b} =
      (∑ a, μ.real {(a, b)} * (S (a, b)).real {u}) / ∑ p, μ.real {p} * (S p).real {u} := by
  rw [Measure.snd_real_singleton_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ ↦ listener_real_singleton μ S u (a, b)

theorem listener_fst_real_lt_iff (u : U) (a₁ a₂ : A) :
    (listener μ S u).fst.real {a₁} < (listener μ S u).fst.real {a₂} ↔
      ∑ b, μ.real {(a₁, b)} * (S (a₁, b)).real {u} <
        ∑ b, μ.real {(a₂, b)} * (S (a₂, b)).real {u} := by
  have key (a : A) : (listener μ S u).fst.real {a} =
      (listener μ S u).real ↑(({a} : Finset A) ×ˢ (Finset.univ : Finset B)) := by
    rw [measureReal_def, measureReal_def, Measure.fst_apply (measurableSet_singleton a)]
    congr 2
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [key, key, listener_real_finset_lt_iff, Finset.sum_product, Finset.sum_product,
    Finset.sum_singleton, Finset.sum_singleton]

theorem listener_snd_real_lt_iff (u : U) (b₁ b₂ : B) :
    (listener μ S u).snd.real {b₁} < (listener μ S u).snd.real {b₂} ↔
      ∑ a, μ.real {(a, b₁)} * (S (a, b₁)).real {u} <
        ∑ a, μ.real {(a, b₂)} * (S (a, b₂)).real {u} := by
  have key (b : B) : (listener μ S u).snd.real {b} =
      (listener μ S u).real ↑((Finset.univ : Finset A) ×ˢ ({b} : Finset B)) := by
    rw [measureReal_def, measureReal_def, Measure.snd_apply (measurableSet_singleton b)]
    congr 2
    ext ⟨x, y⟩
    simp [eq_comm]
  rw [key, key, listener_real_finset_lt_iff, Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton]

section Flat

variable (hμeq : ∀ p q : A × B, μ {p} = μ {q}) (hμ0 : ∀ p, μ {p} ≠ 0)
include hμeq hμ0

/-- At a prior giving every pair the same positive mass, the first marginal of the listener
prefers the point with the greater production probability summed over the second coordinate. -/
theorem listener_fst_real_lt_iff_of_forall_eq (u : U) (a₁ a₂ : A) :
    (listener μ S u).fst.real {a₁} < (listener μ S u).fst.real {a₂} ↔
      ∑ b, (S (a₁, b)).real {u} < ∑ b, (S (a₂, b)).real {u} := by
  rcases isEmpty_or_nonempty B with hB | ⟨⟨b₀⟩⟩
  · simp [Measure.fst_real_singleton_eq_sum]
  · have key (a : A) : ∑ b, μ.real {(a, b)} * (S (a, b)).real {u} =
        μ.real {(a₁, b₀)} * ∑ b, (S (a, b)).real {u} := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ ↦ by
        rw [show μ.real {(a, b)} = μ.real {(a₁, b₀)} by rw [measureReal_def, measureReal_def, hμeq]]
    rw [listener_fst_real_lt_iff, key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real _ from ENNReal.toReal_pos (hμ0 _) (measure_ne_top _ _))]

/-- At a prior giving every pair the same positive mass, the second marginal of the listener
prefers the point with the greater production probability summed over the first coordinate. -/
theorem listener_snd_real_lt_iff_of_forall_eq (u : U) (b₁ b₂ : B) :
    (listener μ S u).snd.real {b₁} < (listener μ S u).snd.real {b₂} ↔
      ∑ a, (S (a, b₁)).real {u} < ∑ a, (S (a, b₂)).real {u} := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
  · simp [Measure.snd_real_singleton_eq_sum]
  · have key (b : B) : ∑ a, μ.real {(a, b)} * (S (a, b)).real {u} =
        μ.real {(a₀, b₁)} * ∑ a, (S (a, b)).real {u} := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ by
        rw [show μ.real {(a, b)} = μ.real {(a₀, b₁)} by rw [measureReal_def, measureReal_def, hμeq]]
    rw [listener_snd_real_lt_iff, key, key, mul_lt_mul_iff_right₀
      (show (0 : ℝ) < μ.real _ from ENNReal.toReal_pos (hμ0 _) (measure_ne_top _ _))]

end Flat

end Prod

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

theorem listener_truthful_eq_ofDensity (μ : Measure W) (sem : U → Set W) :
    listener μ (truthful sem) = Kernel.ofDensity μ fun u ↦ (sem u).indicator 1 :=
  congrArg (Kernel.ofDensity μ) (funext fun u ↦ funext fun w ↦ truthful_apply_singleton sem w u)

/-- The listener of a truthful speaker (eq. 1) conditions the prior on the denotation of the
utterance. -/
theorem listener_truthful_apply' (μ : Measure W) (sem : U → Set W) (u : U)
    (hs : MeasurableSet (sem u)) : listener μ (truthful sem) u = μ[|sem u] := by
  rw [listener_truthful_eq_ofDensity]
  exact Kernel.ofDensity_indicator_one_apply μ sem u hs

theorem listener_truthful_apply [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)
    (u : U) : listener μ (truthful sem) u = μ[|sem u] :=
  listener_truthful_apply' μ sem u .of_discrete

theorem listener_truthful_apply_univ [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)
    [IsFiniteMeasure μ] {u : U} (h : μ (sem u) ≠ 0) : listener μ (truthful sem) u Set.univ = 1 := by
  rw [listener_truthful_apply]
  have := cond_isProbabilityMeasure (μ := μ) h
  exact measure_univ

section Boolean

variable [DiscreteMeasurableSpace W] (μ : Measure W) (sem : U → Set W)

theorem listener_truthful_apply_singleton {u : U} {w : W} (h : w ∈ sem u) :
    listener μ (truthful sem) u {w} = (μ (sem u))⁻¹ * μ {w} := by
  rw [listener_truthful_apply, cond_apply .of_discrete,
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]

theorem listener_truthful_apply_singleton_of_notMem {u : U} {w : W} (h : w ∉ sem u) :
    listener μ (truthful sem) u {w} = 0 := by
  rw [listener_truthful_apply, cond_apply .of_discrete, Set.inter_comm,
    Set.singleton_inter_eq_empty.mpr h, measure_empty, mul_zero]

theorem listener_truthful_real_singleton {u : U} {w : W} (h : w ∈ sem u) :
    (listener μ (truthful sem) u).real {w} = μ.real {w} / μ.real (sem u) := by
  rw [measureReal_def, listener_truthful_apply_singleton μ sem h, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_inv_mul, measureReal_def, measureReal_def]

theorem listener_truthful_apply_singleton_of_eq_univ [IsProbabilityMeasure μ] {u : U}
    (h : sem u = Set.univ) (w : W) : listener μ (truthful sem) u {w} = μ {w} := by
  rw [listener_truthful_apply_singleton μ sem (by rw [h]; exact Set.mem_univ w), h, measure_univ,
    inv_one, one_mul]

theorem listener_truthful_apply_singleton_of_eq_singleton [IsFiniteMeasure μ] {u : U} {w : W}
    (h : sem u = {w}) (hμ : μ {w} ≠ 0) : listener μ (truthful sem) u {w} = 1 := by
  rw [listener_truthful_apply_singleton μ sem (by rw [h]; exact Set.mem_singleton w), h,
    ENNReal.inv_mul_cancel hμ (measure_ne_top _ _)]

theorem listener_truthful_apply_singleton_ne_zero_iff [IsFiniteMeasure μ] (u : U) (w : W) :
    listener μ (truthful sem) u {w} ≠ 0 ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  by_cases h : w ∈ sem u
  · rw [listener_truthful_apply_singleton μ sem h]
    exact ⟨fun h' ↦ ⟨h, (mul_ne_zero_iff.mp h').2⟩,
      fun h' ↦ mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) h'.2⟩
  · rw [listener_truthful_apply_singleton_of_notMem μ sem h]
    exact iff_of_false (fun h' ↦ h' rfl) fun h' ↦ h h'.1

theorem listener_truthful_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [DiscreteMeasurableSpace W'] [MeasurableSpace U'] [Countable U'] [MeasurableSingletonClass U']
    [Fintype W] [Fintype W'] (e : W ≃ W') {μ : Measure W} {μ' : Measure W'} {sem : U → Set W}
    {sem' : U' → Set W'} {u : U} {u' : U'} (hμ : ∀ w, μ' {e w} = μ {w})
    (hsem : ∀ w, e w ∈ sem' u' ↔ w ∈ sem u) (w : W) :
    listener μ' (truthful sem') u' {e w} = listener μ (truthful sem) u {w} := by
  rw [listener_truthful_eq_ofDensity, listener_truthful_eq_ofDensity]
  refine Kernel.ofDensity_apply_singleton_of_equiv e hμ (fun w ↦ ?_) w
  by_cases h : w ∈ sem u
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsem w).2 h), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt (hsem w).1 h)]

end Boolean

end Truthful

end Listener

/-! #### The speaker

A speaker believes a measure on states and addresses a listener. Her weight for an utterance is
the exponential of the rationality times its utility: the expected log of the listener's mass
under her belief, less a real cost. Written without logarithms, the weight is the geometric mean
of the listener's mass over her belief, to the power of the rationality, times the cost weight
`exp (-(α * C u))`. -/

private theorem ofReal_exp_ne_zero (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

private theorem rpow_ne_zero_of_ne_zero {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ 0) :
    x ^ α ≠ 0 := by
  rw [ne_eq, ENNReal.rpow_eq_zero_iff, not_or]
  exact ⟨fun h ↦ hx h.1, fun h ↦ absurd hα (not_le.mpr h.2)⟩

private theorem weight_ne_top {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ ∞) (c : ℝ) :
    x ^ α * ENNReal.ofReal (Real.exp c) ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα hx) ENNReal.ofReal_ne_top

private theorem weight_ne_zero {x : ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) (hx : x ≠ 0) (c : ℝ) :
    x ^ α * ENNReal.ofReal (Real.exp c) ≠ 0 :=
  mul_ne_zero (rpow_ne_zero_of_ne_zero hα hx) (ofReal_exp_ne_zero c)

private theorem weight_toReal {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ∞) (α c : ℝ) :
    (x ^ α * ENNReal.ofReal (Real.exp (-(α * c)))).toReal =
      Real.exp (α * (Real.log x.toReal - c)) := by
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.rpow_def_of_pos (ENNReal.toReal_pos hx0 hx),
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add]
  congr 1; ring

private theorem geomMean_weight_ne_top [Fintype W] {β ν : Measure W} [IsFiniteMeasure ν] {α : ℝ}
    (hα : 0 ≤ α) (c : ℝ) : β.geomMean (fun w ↦ ν {w}) ^ α * ENNReal.ofReal (Real.exp c) ≠ ∞ :=
  weight_ne_top hα (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _) c

section Speaker

variable [Fintype W] [Fintype U] [Countable O] [MeasurableSingletonClass O]

/-- The utility of an utterance to a speaker who believes `β` is the expected log of its listener's
mass under `β`, less its cost: [bergen-levy-goodman-2016]'s equation (3), and with no cost the
expectation in [goodman-stuhlmuller-2013]'s equation (2) of their utility (3). A state she
entertains and the listener rules out makes it `⊥`. -/
noncomputable def utility (C : U → ℝ) (L : U → Measure W) (β : Measure W) (u : U) : EReal :=
  ∑ w, (β.real {w} : EReal) * ENNReal.log (L u {w}) - (C u : EReal)

/-- The speaker at rationality `α` soft-maximizes her utility against the listener `L`, believing
`b o` at `o`: the decision rule of [goodman-stuhlmuller-2013]'s equation (2). -/
noncomputable def speaker (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    Kernel O U :=
  Kernel.softmax fun o u ↦ α * utility C L (b o) u

/-- Her weight for an utterance is the geometric mean of its listener's mass over her belief, to the
power `α`, times the cost weight. -/
theorem speaker_eq_ofWeights (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    speaker α C L b = Kernel.ofWeights fun o u ↦
      (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) := by
  rw [Kernel.ofWeights_rpow_mul_eq_softmax]
  simp_rw [speaker, utility, ← Measure.log_geomMean, EReal.coe_mul_sub_coe, sub_eq_add_neg,
    EReal.coe_neg]

section

variable (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) (o : O)

instance : IsFiniteKernel (speaker α C L b) := inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance : IsZeroOrProbabilityMeasure (speaker α C L b o) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.softmax _ o))

theorem speaker_apply_univ_le_one : speaker α C L b o Set.univ ≤ 1 := by
  rw [speaker_eq_ofWeights]
  exact prob_le_one

theorem speaker_real_singleton_le_one (u : U) : (speaker α C L b o).real {u} ≤ 1 := by
  rw [measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ _)).trans (speaker_apply_univ_le_one α C L b o))

variable [MeasurableSingletonClass U]

theorem speaker_apply_singleton (u : U) :
    speaker α C L b o {u} =
      (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) /
        ∑ u', (b o).geomMean (fun w ↦ L u' {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  rw [speaker_eq_ofWeights]
  exact Kernel.ofWeights_apply_singleton _ o u

theorem sum_speaker_real_singleton_le_one (S : Finset U) :
    ∑ u ∈ S, (speaker α C L b o).real {u} ≤ 1 := by
  rw [sum_measureReal_singleton, measureReal_def, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ _)).trans (speaker_apply_univ_le_one α C L b o))

variable {α C L b o} in
theorem speaker_real_singleton_lt_one [DecidableEq U] {u u' : U} (hne : u' ≠ u)
    (h : speaker α C L b o {u'} ≠ 0) : (speaker α C L b o).real {u} < 1 := by
  have hsum := sum_speaker_real_singleton_le_one α C L b o {u, u'}
  rw [Finset.sum_pair hne.symm] at hsum
  linarith [ENNReal.toReal_pos h (measure_ne_top _ _), measureReal_def (speaker α C L b o) {u'}]

end

variable {α : ℝ} {C : U → ℝ} {L : U → Measure W} {b : O → Measure W} {o : O} {u : U}

/-- The speaker weighs two utterances that her listener interprets alike by their costs alone:
the mass of one is the mass of the other times the exponential of the rationality times the
difference in cost. -/
theorem speaker_apply_singleton_eq_mul_of_apply_eq [MeasurableSingletonClass U] {u' : U}
    (h : L u = L u') :
    speaker α C L b o {u'} =
      ENNReal.ofReal (Real.exp (α * (C u - C u'))) * speaker α C L b o {u} := by
  have hC : ENNReal.ofReal (Real.exp (-(α * C u'))) =
      ENNReal.ofReal (Real.exp (α * (C u - C u'))) * ENNReal.ofReal (Real.exp (-(α * C u))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [speaker_apply_singleton, speaker_apply_singleton, h, hC]
  simp only [div_eq_mul_inv]
  ring

variable [∀ u, IsFiniteMeasure (L u)]

omit [MeasurableSpace U] [Fintype U] in
/-- When the listener dominates the belief, the utility is real. -/
theorem utility_of_absolutelyContinuous {β : Measure W} (h : β ≪ L u) :
    utility C L β u = ((∑ w, β.real {w} * Real.log ((L u).real {w}) - C u : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_finsetSum, utility]
  refine congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ ?_) rfl
  rw [EReal.coe_mul]
  rcases eq_or_ne (β {w}) 0 with h0 | h0
  · simp [measureReal_def, h0]
  · rw [ENNReal.log_pos_real (fun hL ↦ h0 (h hL)) (measure_ne_top _ _), measureReal_def (L u)]

/-- When every listener dominates every belief, the speaker's score is real. -/
theorem speaker_eq_softmax_sum_log (h : ∀ o u, b o ≪ L u) :
    speaker α C L b = Kernel.softmax fun o u ↦
      ((α * (∑ w, (b o).real {w} * Real.log ((L u).real {w}) - C u) : ℝ) : EReal) := by
  simp only [speaker, utility_of_absolutelyContinuous (h _ _), EReal.coe_mul]

theorem isProbabilityMeasure_speaker (hα : 0 ≤ α)
    (h0 : ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) : IsProbabilityMeasure (speaker α C L b o) :=
  speaker_eq_ofWeights α C L b ▸ Kernel.isProbabilityMeasure_ofWeights
    (h0.imp fun _ hu ↦ weight_ne_zero hα (Measure.geomMean_ne_zero hu) _)
    fun _ ↦ geomMean_weight_ne_top hα _

theorem isMarkovKernel_speaker (hα : 0 ≤ α)
    (h0 : ∀ o, ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) : IsMarkovKernel (speaker α C L b) :=
  ⟨fun o ↦ isProbabilityMeasure_speaker hα (h0 o)⟩

variable [MeasurableSingletonClass U]

theorem speaker_apply_singleton_ne_zero (hα : 0 ≤ α) (h : ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) :
    speaker α C L b o {u} ≠ 0 :=
  speaker_eq_ofWeights α C L b ▸ Kernel.ofWeights_apply_singleton_ne_zero
    (weight_ne_zero hα (Measure.geomMean_ne_zero h) _)
    fun _ ↦ geomMean_weight_ne_top hα _

/-- Row preference of the speaker compares the weights; the normalization cancels. -/
theorem speaker_real_singleton_lt_iff (hα : 0 ≤ α) (h0 : ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0)
    {u u' : U} :
    (speaker α C L b o).real {u} < (speaker α C L b o).real {u'} ↔
      (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) <
        (b o).geomMean (fun w ↦ L u' {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  speaker_eq_ofWeights α C L b ▸ Kernel.ofWeights_real_singleton_lt_iff o
    (fun h ↦ let ⟨u₀, hu₀⟩ := h0
      weight_ne_zero hα (Measure.geomMean_ne_zero hu₀) _
        (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ geomMean_weight_ne_top hα _)

/-- The odds of two utterances under the speaker are the odds of the geometric means of their
listeners' masses over her belief, to the power `α`, times the exponential of the cost
difference. -/
theorem speaker_real_singleton_div (hα : 0 ≤ α) (h : ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) (u' : U) :
    (speaker α C L b o).real {u'} / (speaker α C L b o).real {u} =
      (((b o).geomMean fun w ↦ L u' {w}).toReal / ((b o).geomMean fun w ↦ L u {w}).toReal) ^ α *
        Real.exp (-(α * (C u' - C u))) := by
  have hu := Measure.geomMean_ne_zero h
  have hpos : 0 < ((b o).geomMean fun w ↦ L u {w}).toReal :=
    ENNReal.toReal_pos hu (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _)
  have hZ : (0 : ℝ) < ∑ v, ((b o).geomMean (fun w ↦ L v {w}) ^ α *
      ENNReal.ofReal (Real.exp (-(α * C v)))).toReal :=
    Finset.sum_pos' (fun _ _ ↦ ENNReal.toReal_nonneg) ⟨u, Finset.mem_univ u,
      ENNReal.toReal_pos (weight_ne_zero hα hu _) (geomMean_weight_ne_top hα _)⟩
  rw [speaker_eq_ofWeights,
    Kernel.ofWeights_real_singleton _ _ (fun _ ↦ geomMean_weight_ne_top hα _),
    Kernel.ofWeights_real_singleton _ _ (fun _ ↦ geomMean_weight_ne_top hα _),
    div_div_div_cancel_right₀ hZ.ne', ENNReal.toReal_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.div_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg, mul_sub, neg_sub, Real.exp_sub,
    Real.exp_neg, Real.exp_neg]
  have := Real.rpow_pos_of_pos hpos α
  field_simp

/-- The speaker never produces an utterance whose listener rules out a state she entertains. -/
theorem speaker_apply_singleton_eq_zero_iff [IsFiniteMeasure (b o)] (hα : 0 < α) :
    speaker α C L b o {u} = 0 ↔ ∃ w, b o {w} ≠ 0 ∧ L u {w} = 0 := by
  rw [speaker_apply_singleton, ENNReal.div_eq_zero_iff,
    or_iff_left (ENNReal.sum_ne_top.2 fun _ _ ↦ geomMean_weight_ne_top hα.le _),
    mul_eq_zero, or_iff_left (ofReal_exp_ne_zero _), ENNReal.rpow_eq_zero_iff_of_pos hα,
    Measure.geomMean_eq_zero_iff]

theorem speaker_apply_singleton_eq_zero_iff_not_ac [IsFiniteMeasure (b o)] (hα : 0 < α) :
    speaker α C L b o {u} = 0 ↔ ¬ b o ≪ L u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, Measure.absolutelyContinuous_iff_forall_singleton,
    not_forall]
  exact exists_congr fun w ↦ by rw [Classical.not_imp, and_comm]

end Speaker

/-! #### The MaxiMin speaker

A speaker who is maximally averse to the risk of being misread values an utterance by its least
utility over the states she entertains, the MaxiMin rule, instead of by its expected utility. Her
weight puts the essential infimum of the listener's mass over her belief where the expected-utility
speaker puts its geometric mean. She produces the utterances that speaker produces, and is that
speaker when her belief is a point mass, but she depends on her belief only through the states
it entertains, not through their probabilities. -/

private theorem essInf_ne_top [Countable W] {β ν : Measure W} [IsFiniteMeasure ν]
    (hβ : ∃ w, β {w} ≠ 0) : essInf (fun w ↦ ν {w}) β ≠ ∞ := by
  obtain ⟨w, hw⟩ := hβ
  rw [essInf_eq_biInf]
  exact ne_top_of_le_ne_top (measure_ne_top ν {w}) (iInf₂_le w hw)

section MaxiMin

variable [Fintype U] [Countable O] [MeasurableSingletonClass O]

/-- The MaxiMin speaker at rationality `α` and cost `C` addresses the listener `L` and at `o`
believes `b o`. Her weight for an utterance is the essential infimum of its listener's mass over
her belief, to the power `α`, times the cost weight. -/
noncomputable def maximinSpeaker (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    Kernel O U :=
  Kernel.ofWeights fun o u ↦
    essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))

instance (α : ℝ) (C : U → ℝ) (L : U → Measure W) (b : O → Measure W) :
    IsFiniteKernel (maximinSpeaker α C L b) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- The MaxiMin speaker who knows the state is the speaker who knows it. -/
theorem maximinSpeaker_dirac [Fintype W] [MeasurableSingletonClass W] (α : ℝ) (C : U → ℝ)
    (L : U → Measure W) : maximinSpeaker α C L Measure.dirac = speaker α C L Measure.dirac := by
  simp only [maximinSpeaker, speaker_eq_ofWeights, essInf_dirac, Measure.geomMean_dirac]

variable [MeasurableSingletonClass U] {α : ℝ} {C : U → ℝ} {L : U → Measure W} {b : O → Measure W}
  {o : O} {u : U}

theorem maximinSpeaker_apply_singleton (u : U) :
    maximinSpeaker α C L b o {u} =
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) /
        ∑ u', essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_apply_singleton _ o u

/-- The MaxiMin speaker depends on her belief only through its null sets. -/
theorem maximinSpeaker_congr_belief {b' : O → Measure W} (h : ae (b o) = ae (b' o)) :
    maximinSpeaker α C L b o = maximinSpeaker α C L b' o :=
  Measure.ext_of_singleton fun u ↦ by simp only [maximinSpeaker_apply_singleton, essInf, h]

variable [Fintype W] [∀ u, IsFiniteMeasure (L u)]

/-- The MaxiMin speaker never produces an utterance whose listener rules out a state she
entertains. -/
theorem maximinSpeaker_apply_singleton_eq_zero_iff (hα : 0 < α) (hb : ∃ w, b o {w} ≠ 0) :
    maximinSpeaker α C L b o {u} = 0 ↔ ∃ w, b o {w} ≠ 0 ∧ L u {w} = 0 := by
  rw [maximinSpeaker_apply_singleton, ENNReal.div_eq_zero_iff,
    or_iff_left (ENNReal.sum_ne_top.2 fun _ _ ↦ weight_ne_top hα.le (essInf_ne_top hb) _),
    mul_eq_zero, or_iff_left (ofReal_exp_ne_zero _), ENNReal.rpow_eq_zero_iff_of_pos hα,
    ENNReal.essInf_eq_zero_iff]

/-- The MaxiMin speaker produces exactly the utterances the expected-utility speaker produces. -/
theorem maximinSpeaker_apply_singleton_eq_zero_iff_speaker [IsFiniteMeasure (b o)] (hα : 0 < α)
    (hb : ∃ w, b o {w} ≠ 0) : maximinSpeaker α C L b o {u} = 0 ↔ speaker α C L b o {u} = 0 := by
  rw [maximinSpeaker_apply_singleton_eq_zero_iff hα hb, speaker_apply_singleton_eq_zero_iff hα]

/-- Row preference of the MaxiMin speaker compares the weights; the normalization cancels. -/
theorem maximinSpeaker_real_singleton_lt_iff (hα : 0 ≤ α) (hb : ∃ w, b o {w} ≠ 0)
    (h0 : ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) {u u' : U} :
    (maximinSpeaker α C L b o).real {u} < (maximinSpeaker α C L b o).real {u'} ↔
      essInf (fun w ↦ L u {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) <
        essInf (fun w ↦ L u' {w}) (b o) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  Kernel.ofWeights_real_singleton_lt_iff o
    (fun h ↦ let ⟨u₀, hu₀⟩ := h0
      weight_ne_zero hα (fun h' ↦ (ENNReal.essInf_eq_zero_iff.1 h').elim fun w ⟨hw, hL⟩ ↦
        hu₀ w hw hL) _
        (Finset.sum_eq_zero_iff.mp h u₀ (Finset.mem_univ _)))
    (ENNReal.sum_ne_top.mpr fun _ _ ↦ weight_ne_top hα (essInf_ne_top hb) _)

end MaxiMin

/-! #### Uncertainty about the parse

A speaker unsure how the listener will parse her utterance addresses the literal listeners of the
parses as one listener on pairs of a parse and a state. Knowing the state `w` and holding a prior
`ν` over the parses, she believes `ν.prod (dirac w)`: the expected-utility speaker then weighs the
parses' listeners by their geometric mean under `ν`, the MaxiMin speaker by their least value over
the parses `ν` allows, and neither uses an utterance that one of those parses rules out at `w`. -/

section Parse

variable {ι : Type*} [MeasurableSpace ι]

/-- The literal listeners of a family of parses, as one listener on pairs of a parse and a
state. -/
noncomputable def parseListener (L : ι → U → Measure W) (u : U) : Measure (ι × W) :=
  Measure.sum fun i ↦ (L i u).map (Prod.mk i)

instance [Fintype ι] (L : ι → U → Measure W) [∀ i u, IsFiniteMeasure (L i u)] (u : U) :
    IsFiniteMeasure (parseListener L u) := by
  unfold parseListener; infer_instance

variable [MeasurableSingletonClass ι] [MeasurableSingletonClass W] {L : ι → U → Measure W}
  {ν : Measure ι} {u : U} {w : W}

omit [MeasurableSpace U] in
@[simp] theorem parseListener_apply_singleton (L : ι → U → Measure W) (u : U) (i : ι) (w : W) :
    parseListener L u {(i, w)} = L i u {w} := by
  rw [parseListener, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single i]
  · rw [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
    congr 1; ext; simp
  · intro j hji
    rw [Measure.map_apply measurable_prodMk_left (measurableSet_singleton _)]
    convert measure_empty (μ := L j u)
    ext; simp [hji]

omit [MeasurableSpace U] in
/-- Under the belief `ν.prod (dirac w)` the geometric mean of the listener's mass is that of the
parses' listeners at `w` under `ν`. -/
theorem geomMean_prod_dirac_parseListener [Fintype ι] [Fintype W] :
    (ν.prod (Measure.dirac w)).geomMean (fun p ↦ parseListener L u {p}) =
      ν.geomMean fun i ↦ L i u {w} := by
  simp only [Measure.geomMean_prod, Measure.geomMean_dirac, parseListener_apply_singleton]

omit [MeasurableSpace U] in
/-- Under the belief `ν.prod (dirac w)` the essential infimum of the listener's mass is the least
value of the parses' listeners at `w` over the parses `ν` allows. -/
theorem essInf_prod_dirac_parseListener [Countable ι] [Countable W] :
    essInf (fun p ↦ parseListener L u {p}) (ν.prod (Measure.dirac w)) =
      ⨅ (i) (_ : ν {i} ≠ 0), L i u {w} := by
  rw [essInf_eq_biInf]
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_) (le_iInf₂ fun p hp ↦ ?_)
  · rw [← parseListener_apply_singleton L u i w]
    exact iInf₂_le (f := fun p (_ : ν.prod (Measure.dirac w) {p} ≠ 0) ↦ parseListener L u {p})
      (i, w) ((Measure.prod_dirac_apply_singleton_ne_zero_iff ν w (i, w)).2 ⟨hi, rfl⟩)
  · obtain ⟨i, v⟩ := p
    obtain ⟨hi, rfl⟩ := (Measure.prod_dirac_apply_singleton_ne_zero_iff ν w (i, v)).1 hp
    rw [parseListener_apply_singleton]
    exact iInf₂_le (f := fun i (_ : ν {i} ≠ 0) ↦ L i u {v}) i hi

omit [MeasurableSpace U] in
private theorem exists_prod_dirac_parseListener_eq_zero_iff :
    (∃ p, ν.prod (Measure.dirac w) {p} ≠ 0 ∧ parseListener L u {p} = 0) ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {w} = 0 := by
  refine ⟨fun ⟨⟨i, v⟩, hp, hL⟩ ↦ ?_, fun ⟨i, hi, hL⟩ ↦
    ⟨(i, w), (Measure.prod_dirac_apply_singleton_ne_zero_iff ν w _).2 ⟨hi, rfl⟩, by simpa⟩⟩
  obtain ⟨hi, rfl⟩ := (Measure.prod_dirac_apply_singleton_ne_zero_iff ν w (i, v)).1 hp
  exact ⟨i, hi, by simpa using hL⟩

variable [Fintype ι] [Fintype W] [Fintype U] [MeasurableSingletonClass U] [Countable O]
  [MeasurableSingletonClass O] {α : ℝ} {C : U → ℝ} [∀ i u, IsFiniteMeasure (L i u)] {o : O}

/-- The expected-utility speaker never uses an utterance that a parse her prior allows rules out
at her state. -/
theorem speaker_parseListener_apply_singleton_eq_zero_iff [IsFiniteMeasure ν] (f : O → W)
    (hα : 0 < α) :
    speaker α C (parseListener L) (fun o ↦ ν.prod (Measure.dirac (f o))) o {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {f o} = 0 := by
  rw [speaker_apply_singleton_eq_zero_iff hα, exists_prod_dirac_parseListener_eq_zero_iff]

/-- Nor does the MaxiMin speaker. -/
theorem maximinSpeaker_parseListener_apply_singleton_eq_zero_iff (f : O → W) (hα : 0 < α)
    (hν : ∃ i, ν {i} ≠ 0) :
    maximinSpeaker α C (parseListener L) (fun o ↦ ν.prod (Measure.dirac (f o))) o {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ L i u {f o} = 0 := by
  obtain ⟨i, hi⟩ := hν
  rw [maximinSpeaker_apply_singleton_eq_zero_iff (b := fun o ↦ ν.prod (Measure.dirac (f o))) hα
      ⟨(i, f o), (Measure.prod_dirac_apply_singleton_ne_zero_iff ν _ _).2 ⟨hi, rfl⟩⟩,
    exists_prod_dirac_parseListener_eq_zero_iff]

end Parse

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
    rpow_ne_zero_of_ne_zero hα (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ))
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

private theorem geomMean_listener_truthful (β : Measure W) [IsProbabilityMeasure β] (u : U) :
    β.geomMean (fun w ↦ listener μ (truthful sem) u {w}) =
      β.geomMean (fun w ↦ μ {w}) * (β.geomMean ((sem u).indicator 1) * (μ (sem u))⁻¹) := by
  rw [listener_truthful_eq_ofDensity, geomMean_ofDensity]
  congr 3
  rw [← lintegral_fintype, lintegral_indicator_one .of_discrete]

variable [IsFiniteMeasure μ]

theorem speaker_listener_truthful_apply_singleton_eq_zero_iff (hα : 0 < α) [IsFiniteMeasure (b o)]
    (hb : b o ≪ μ) :
    speaker α C (listener μ (truthful sem)) b o {u} = 0 ↔ ¬ ∀ᵐ w ∂b o, w ∈ sem u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, ae_iff_of_countable, not_forall]
  refine exists_congr fun w ↦ ?_
  rw [Classical.not_imp]
  refine and_congr_right fun hw ↦ ?_
  rw [← not_iff_not, not_not, ← ne_eq, listener_truthful_apply_singleton_ne_zero_iff]
  exact and_iff_left fun h ↦ hw (hb h)

/-- Against the literal listener the speaker's mass on an utterance her belief entails is its
weight, the inverse of its extension's prior mass to the power `α` times the cost weight, over the
sum of the weights of the utterances her belief entails. -/
theorem speaker_listener_truthful_apply_singleton (hα : 0 < α) [IsProbabilityMeasure (b o)]
    (hb : b o ≪ μ) (u : U) :
    speaker α C (listener μ (truthful sem)) b o {u} =
      {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) u /
        ∑ v, {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
          (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v := by
  classical
  have key (v : U) : (b o).geomMean (fun w ↦ listener μ (truthful sem) v {w}) ^ α *
        ENNReal.ofReal (Real.exp (-(α * C v))) =
      (b o).geomMean (fun w ↦ μ {w}) ^ α * {v | ∀ᵐ w ∂b o, w ∈ sem v}.indicator
        (fun v ↦ (μ (sem v))⁻¹ ^ α * ENNReal.ofReal (Real.exp (-(α * C v)))) v := by
    rw [geomMean_listener_truthful, Measure.geomMean_indicator_one]
    by_cases hv : ∀ᵐ w ∂b o, w ∈ sem v
    · rw [ite_eq_left hv, Set.indicator_of_mem (show v ∈ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hv),
        one_mul, ENNReal.mul_rpow_of_nonneg _ _ hα.le, mul_assoc]
    · rw [ite_eq_right hv, Set.indicator_of_notMem (show v ∉ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hv),
        zero_mul, mul_zero, ENNReal.zero_rpow_of_pos hα, zero_mul, mul_zero]
  rw [speaker_apply_singleton, key, Finset.sum_congr rfl fun v _ ↦ key v, ← Finset.mul_sum,
    ENNReal.mul_div_mul_left _ _
      (rpow_ne_zero_of_ne_zero hα.le (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ)))
      (ENNReal.rpow_ne_top_of_nonneg hα.le (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _))]

variable {O' : Type*} [MeasurableSpace O'] [Countable O'] [MeasurableSingletonClass O']
  {b' : O' → Measure W} {o' : O'}

/-- Against the literal listener two beliefs yield the same speaker exactly when they entail the
same utterances. -/
theorem speaker_listener_truthful_apply_eq_iff (hα : 0 < α) [IsProbabilityMeasure (b o)]
    [IsProbabilityMeasure (b' o')] (hb : b o ≪ μ) (hb' : b' o' ≪ μ) :
    speaker α C (listener μ (truthful sem)) b' o' = speaker α C (listener μ (truthful sem)) b o ↔
      ∀ u, (∀ᵐ w ∂b' o', w ∈ sem u) ↔ ∀ᵐ w ∂b o, w ∈ sem u := by
  refine ⟨fun h u ↦ ?_, fun h ↦ Measure.ext_of_singleton fun u ↦ ?_⟩
  · rw [← not_iff_not, ← speaker_listener_truthful_apply_singleton_eq_zero_iff hα hb' (C := C),
      ← speaker_listener_truthful_apply_singleton_eq_zero_iff hα hb (C := C), h]
  · simp only [speaker_listener_truthful_apply_singleton hα hb,
      speaker_listener_truthful_apply_singleton hα hb', h]

/-- An utterance a belief entails loses mass to a belief that entails at least as much, whose
speaker has more to choose from. -/
theorem speaker_listener_truthful_apply_singleton_le (hα : 0 < α) [IsProbabilityMeasure (b o)]
    [IsProbabilityMeasure (b' o')] (hb : b o ≪ μ) (hb' : b' o' ≪ μ)
    (h : ∀ v, (∀ᵐ w ∂b o, w ∈ sem v) → ∀ᵐ w ∂b' o', w ∈ sem v) (hu : ∀ᵐ w ∂b o, w ∈ sem u) :
    speaker α C (listener μ (truthful sem)) b' o' {u} ≤
      speaker α C (listener μ (truthful sem)) b o {u} := by
  rw [speaker_listener_truthful_apply_singleton hα hb,
    speaker_listener_truthful_apply_singleton hα hb',
    Set.indicator_of_mem (show u ∈ {v | ∀ᵐ w ∂b o, w ∈ sem v} from hu),
    Set.indicator_of_mem (show u ∈ {v | ∀ᵐ w ∂b' o', w ∈ sem v} from h u hu)]
  exact ENNReal.div_le_div_left (Finset.sum_le_sum fun v _ ↦
    Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le) v) _

/-- Among the utterances her belief entails, the speaker at no cost prefers the one of smaller
prior mass. -/
theorem speaker_zero_listener_truthful_real_singleton_lt_iff (hα : 0 < α)
    [IsProbabilityMeasure (b o)] (hb : b o ≪ μ) (hu : ∀ᵐ w ∂b o, w ∈ sem u)
    (hu' : ∀ᵐ w ∂b o, w ∈ sem u') :
    (speaker α 0 (listener μ (truthful sem)) b o).real {u} <
        (speaker α 0 (listener μ (truthful sem)) b o).real {u'} ↔
      μ (sem u') < μ (sem u) := by
  classical
  have h1 (v : U) (hv : ∀ᵐ w ∂b o, w ∈ sem v) : (b o).geomMean ((sem v).indicator 1) = 1 := by
    rw [Measure.geomMean_indicator_one, ite_eq_left hv]
  rw [speaker_real_singleton_lt_iff hα.le ⟨u, fun w hw ↦
    (listener_truthful_apply_singleton_ne_zero_iff μ sem u w).2
      ⟨ae_iff_of_countable.1 hu w hw, fun hμ ↦ hw (hb hμ)⟩⟩]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [ENNReal.rpow_lt_rpow_iff hα, geomMean_listener_truthful, geomMean_listener_truthful, h1 u hu,
    h1 u' hu', one_mul, one_mul,
    ENNReal.mul_lt_mul_iff_right (Measure.geomMean_ne_zero fun _ hw hμ ↦ hw (hb hμ))
      (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _), ENNReal.inv_lt_inv]

end Literal

/-! #### The speaker who knows the state

The speaker of eqs. 2/6–7 knows the state, so she believes the point mass there, and her weight
for an utterance is the listener's mass at the state to the power `α`, times the cost weight. -/

section Dirac

variable [MeasurableSingletonClass W]

private theorem eq_of_dirac_apply_singleton_ne_zero {w w' : W} (h : Measure.dirac w {w'} ≠ 0) :
    w' = w := by
  rw [Measure.dirac_apply' w (measurableSet_singleton w')] at h
  exact (Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h)).symm

private theorem ae_dirac_mem_iff {w : W} {t : Set W} : (∀ᵐ x ∂Measure.dirac w, x ∈ t) ↔ w ∈ t := by
  rw [ae_dirac_eq, Filter.eventually_pure]

variable [Fintype W] [Fintype U] {α : ℝ} {C : U → ℝ} {L : Kernel U W} {w : W} {u : U}

private theorem dirac_absolutelyContinuous {μ : Measure W} (h : μ {w} ≠ 0) :
    Measure.dirac w ≪ μ :=
  Measure.absolutelyContinuous_of_forall_singleton fun _ hw' ↦ of_not_not fun hd ↦
    h (eq_of_dirac_apply_singleton_ne_zero hd ▸ hw')

/-- A speaker who knows the state weights an utterance by its listener's mass there to the power
`α`, times the cost weight `exp (-(α * C u))`. -/
theorem speaker_dirac_eq_ofWeights (α : ℝ) (C : U → ℝ) (L : U → Measure W) :
    speaker α C L Measure.dirac =
      Kernel.ofWeights fun w u ↦ L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) := by
  simp only [speaker_eq_ofWeights, Measure.geomMean_dirac]

omit [MeasurableSpace U] [Fintype U] in
theorem utility_dirac (C : U → ℝ) (L : U → Measure W) (w : W) (u : U) :
    utility C L (Measure.dirac w) u = ENNReal.log (L u {w}) - (C u : EReal) := by
  rw [utility, ← Measure.log_geomMean, Measure.geomMean_dirac]

theorem speaker_dirac_eq_softmax (α : ℝ) (C : U → ℝ) (L : U → Measure W) :
    speaker α C L Measure.dirac = Kernel.softmax fun w u ↦
      α * (ENNReal.log (L u {w}) - (C u : EReal)) := by
  simp only [speaker, utility_dirac]

theorem isProbabilityMeasure_speaker_dirac (hα : 0 ≤ α) (C : U → ℝ) (L : Kernel U W)
    [IsFiniteKernel L] (h0 : ∃ u, L u {w} ≠ 0) :
    IsProbabilityMeasure (speaker α C L Measure.dirac w) :=
  isProbabilityMeasure_speaker hα (h0.imp fun _ hu _ hw' ↦
    eq_of_dirac_apply_singleton_ne_zero hw' ▸ hu)

theorem isMarkovKernel_speaker_dirac (hα : 0 ≤ α) (C : U → ℝ) (L : Kernel U W) [IsFiniteKernel L]
    (h0 : ∀ w, ∃ u, L u {w} ≠ 0) : IsMarkovKernel (speaker α C L Measure.dirac) :=
  ⟨fun w ↦ isProbabilityMeasure_speaker_dirac hα C L (h0 w)⟩

variable [MeasurableSingletonClass U]

@[simp] theorem speaker_dirac_apply_singleton (α : ℝ) (C : U → ℝ) (L : U → Measure W)
    (w : W) (u : U) :
    speaker α C L Measure.dirac w {u} = L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
      / ∑ u', L u' {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  rw [speaker_dirac_eq_ofWeights, Kernel.ofWeights_apply_singleton]

theorem speaker_dirac_zero_apply_singleton (α : ℝ) (L : U → Measure W) (w : W) (u : U) :
    speaker α 0 L Measure.dirac w {u} = L u {w} ^ α / ∑ u', L u' {w} ^ α := by
  rw [speaker_dirac_apply_singleton]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]

theorem speaker_dirac_apply_singleton_of_equiv {W' U' : Type*} [MeasurableSpace W']
    [MeasurableSpace U'] [Fintype W'] [MeasurableSingletonClass W'] [Fintype U']
    [MeasurableSingletonClass U'] (τ : U ≃ U') (α : ℝ) (C : U' → ℝ) {L : Kernel U W}
    {L' : Kernel U' W'} {w : W} {w' : W'} (h : ∀ v, L' (τ v) {w'} = L v {w}) (u : U) :
    speaker α C L' Measure.dirac w' {τ u} = speaker α (C ∘ τ) L Measure.dirac w {u} := by
  rw [speaker_dirac_apply_singleton, speaker_dirac_apply_singleton, h, ← τ.sum_comp]
  simp only [h, Function.comp_apply]

theorem speaker_dirac_apply_singleton_eq_zero (hα : 0 < α) (h : L u {w} = 0) :
    speaker α C L Measure.dirac w {u} = 0 := by
  rw [speaker_dirac_eq_ofWeights]
  exact Kernel.ofWeights_apply_singleton_eq_zero (by rw [h, ENNReal.zero_rpow_of_pos hα, zero_mul])

theorem speaker_dirac_apply_singleton_ne_zero [IsFiniteKernel L] (hα : 0 ≤ α) (h : L u {w} ≠ 0) :
    speaker α C L Measure.dirac w {u} ≠ 0 :=
  speaker_apply_singleton_ne_zero hα fun _ hw' ↦ eq_of_dirac_apply_singleton_ne_zero hw' ▸ h

theorem speaker_dirac_apply_singleton_ne_zero_iff [IsFiniteKernel L] (hα : 0 < α) :
    speaker α C L Measure.dirac w {u} ≠ 0 ↔ L u {w} ≠ 0 :=
  ⟨fun h h' ↦ h (speaker_dirac_apply_singleton_eq_zero hα h'),
    speaker_dirac_apply_singleton_ne_zero hα.le⟩

theorem speaker_dirac_apply_singleton_eq_one [IsFiniteKernel L] (hα : 0 < α) (h : L u {w} ≠ 0)
    (hother : ∀ u' ≠ u, L u' {w} = 0) : speaker α C L Measure.dirac w {u} = 1 := by
  rw [speaker_dirac_apply_singleton, Finset.sum_eq_single u
    (fun u' _ hu' ↦ by rw [hother u' hu', ENNReal.zero_rpow_of_pos hα, zero_mul])
    (fun hu ↦ absurd (Finset.mem_univ u) hu)]
  exact ENNReal.div_self (weight_ne_zero hα.le h _) (weight_ne_top hα.le (measure_ne_top _ _) _)

theorem speaker_dirac_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α C L Measure.dirac w).real {u}
      = (L u {w} ^ α).toReal * Real.exp (-(α * C u))
        / ∑ u', (L u' {w} ^ α).toReal * Real.exp (-(α * C u')) := by
  rw [measureReal_def, speaker_dirac_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun u' _ ↦ weight_ne_top hα (measure_ne_top _ _) _]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem speaker_dirac_zero_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α 0 L Measure.dirac w).real {u} =
      (L u {w} ^ α).toReal / ∑ u', (L u' {w} ^ α).toReal := by
  rw [speaker_dirac_real_singleton hα]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- Row-preference of the speaker reduces to comparing the weighted listener values; the
normalization cancels. -/
theorem speaker_dirac_real_singleton_lt_iff [IsFiniteKernel L] (hα : 0 ≤ α) (h0 : ∃ u, L u {w} ≠ 0)
    {u u' : U} :
    (speaker α C L Measure.dirac w).real {u} < (speaker α C L Measure.dirac w).real {u'} ↔
      L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        < L u' {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  have := speaker_real_singleton_lt_iff (C := C) (L := L) (b := Measure.dirac) (o := w) (u := u)
    (u' := u') hα
    (h0.imp fun _ hu _ hw' ↦ eq_of_dirac_apply_singleton_ne_zero hw' ▸ hu)
  simpa only [Measure.geomMean_dirac] using this

theorem speaker_dirac_real_singleton_div [IsFiniteKernel L] (hα : 0 ≤ α) (h : L u {w} ≠ 0)
    (u' : U) :
    (speaker α C L Measure.dirac w).real {u'} / (speaker α C L Measure.dirac w).real {u} =
      ((L u' {w}).toReal / (L u {w}).toReal) ^ α * Real.exp (-(α * (C u' - C u))) := by
  simpa only [Measure.geomMean_dirac] using speaker_real_singleton_div (C := C) (L := L)
    (b := Measure.dirac) (o := w) hα (fun _ hw' ↦ eq_of_dirac_apply_singleton_ne_zero hw' ▸ h) u'

/-- Of two utterances with listener mass at the state, the speaker prefers the one of greater
utility, the log of the listener's mass less the cost. -/
theorem speaker_dirac_real_singleton_lt_iff_log [IsFiniteKernel L] (hα : 0 < α) {u' : U}
    (hu : L u {w} ≠ 0) (hu' : L u' {w} ≠ 0) :
    (speaker α C L Measure.dirac w).real {u} < (speaker α C L Measure.dirac w).real {u'} ↔
      Real.log (L u {w}).toReal - C u < Real.log (L u' {w}).toReal - C u' := by
  rw [speaker_dirac_real_singleton_lt_iff hα.le ⟨u, hu⟩,
    ← ENNReal.toReal_lt_toReal (weight_ne_top hα.le (measure_ne_top _ _) _)
      (weight_ne_top hα.le (measure_ne_top _ _) _),
    weight_toReal hu (measure_ne_top _ _), weight_toReal hu' (measure_ne_top _ _),
    Real.exp_lt_exp, mul_lt_mul_iff_of_pos_left hα]

theorem speaker_dirac_real_singleton_of_pair [IsFiniteKernel L] (hα : 0 < α) {u' : U}
    (huu' : u ≠ u') (hu : L u {w} ≠ 0) (hu' : L u' {w} ≠ 0)
    (hsupp : ∀ v, L v {w} ≠ 0 → v = u ∨ v = u') :
    (speaker α C L Measure.dirac w).real {u} = Real.sigmoid
      (α * ((Real.log (L u {w}).toReal - C u) - (Real.log (L u' {w}).toReal - C u'))) := by
  rw [speaker_dirac_eq_ofWeights, Kernel.ofWeights_real_singleton_of_pair w huu'
      (fun v ↦ weight_ne_top hα.le (measure_ne_top _ _) _)
      (fun v hv ↦ hsupp v fun h ↦ hv (by rw [h, ENNReal.zero_rpow_of_pos hα, zero_mul])),
    weight_toReal hu (measure_ne_top _ _), weight_toReal hu' (measure_ne_top _ _),
    Real.exp_div_add_exp_eq_sigmoid, ← mul_sub]

theorem speaker_listener_truthful_dirac_eq_one (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    (hmem : w ∈ sem u) (hother : ∀ u' ≠ u, w ∉ sem u') :
    speaker α C (listener μ (truthful sem)) Measure.dirac w {u} = 1 :=
  speaker_dirac_apply_singleton_eq_one hα
    (by
      rw [listener_truthful_apply_singleton μ sem hmem]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hμ)
    fun u' hu' ↦ listener_truthful_apply_singleton_of_notMem μ sem (hother u' hu')

theorem speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (u : U) (w : W) :
    speaker α C (listener μ (truthful sem)) Measure.dirac w {u} ≠ 0
      ↔ w ∈ sem u ∧ μ {w} ≠ 0 := by
  rw [speaker_dirac_apply_singleton_ne_zero_iff hα,
    listener_truthful_apply_singleton_ne_zero_iff μ sem u w]

theorem speaker_listener_truthful_dirac_apply_singleton_eq_zero (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) (h : w ∉ sem u) :
    speaker α C (listener μ (truthful sem)) Measure.dirac w {u} = 0 :=
  speaker_dirac_apply_singleton_eq_zero hα (listener_truthful_apply_singleton_of_notMem μ sem h)

/-- A speaker who knows the state says only what is true there. -/
theorem ae_speaker_listener_truthful_dirac_mem (hα : 0 < α) (C : U → ℝ) (μ : Measure W)
    (sem : U → Set W) (w : W) :
    ∀ᵐ u ∂speaker α C (listener μ (truthful sem)) Measure.dirac w, w ∈ sem u :=
  ae_iff_of_countable.2 fun _ hu ↦
    by_contra fun h ↦ hu (speaker_listener_truthful_dirac_apply_singleton_eq_zero hα C μ sem h)

theorem speaker_listener_truthful_dirac_real_singleton_eq_zero (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) (h : w ∉ sem u) :
    (speaker α C (listener μ (truthful sem)) Measure.dirac w).real {u} = 0 := by
  rw [measureReal_def, speaker_listener_truthful_dirac_apply_singleton_eq_zero hα C μ sem h,
    ENNReal.toReal_zero]

section SingletonUniv

variable (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsProbabilityMeasure μ] (sem : U → Set W)
  (hμ : μ {w} ≠ 0) {u' : U} (huu' : u ≠ u') (hu : sem u = {w}) (hu' : sem u' = Set.univ)
  (hsupp : ∀ v, w ∈ sem v → v = u ∨ v = u')
include hα hμ huu' hu hu' hsupp

/-- A speaker who knows the state and can say only what is true there alone or what is true
everywhere says the first with the logistic probability of the cost it adds, less the log prior
of the state, discounted. -/
theorem speaker_listener_truthful_dirac_real_singleton_of_eq_singleton :
    (speaker α C (listener μ (truthful sem)) Measure.dirac w).real {u} =
      Real.sigmoid (α * (C u' - C u - Real.log (μ.real {w}))) := by
  have h1 := listener_truthful_apply_singleton_of_eq_singleton μ sem hu hμ
  have h2 := listener_truthful_apply_singleton_of_eq_univ μ sem hu' w
  rw [speaker_dirac_real_singleton_of_pair hα huu' (h1 ▸ one_ne_zero) (h2 ▸ hμ) fun v hv ↦
      hsupp v ((listener_truthful_apply_singleton_ne_zero_iff μ sem v w).1 hv).1,
    h1, h2, ENNReal.toReal_one, Real.log_one, ← measureReal_def]
  congr 1; ring

theorem speaker_listener_truthful_dirac_real_singleton_of_eq_univ :
    (speaker α C (listener μ (truthful sem)) Measure.dirac w).real {u'} =
      Real.sigmoid (α * (C u - C u' + Real.log (μ.real {w}))) := by
  have h1 := listener_truthful_apply_singleton_of_eq_singleton μ sem hu hμ
  have h2 := listener_truthful_apply_singleton_of_eq_univ μ sem hu' w
  rw [speaker_dirac_real_singleton_of_pair hα huu'.symm (h2 ▸ hμ) (h1 ▸ one_ne_zero) fun v hv ↦
      (hsupp v ((listener_truthful_apply_singleton_ne_zero_iff μ sem v w).1 hv).1).symm,
    h1, h2, ENNReal.toReal_one, Real.log_one, ← measureReal_def]
  congr 1; ring

end SingletonUniv

theorem speaker_listener_truthful_dirac_congr (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W)
    {w w' : W} (hw : μ {w} ≠ 0) (hw' : μ {w'} ≠ 0) (h : ∀ u, w ∈ sem u ↔ w' ∈ sem u) :
    speaker α C (listener μ (truthful sem)) Measure.dirac w'
      = speaker α C (listener μ (truthful sem)) Measure.dirac w :=
  (speaker_listener_truthful_apply_eq_iff hα (dirac_absolutelyContinuous hw)
    (dirac_absolutelyContinuous hw')).2 fun u ↦ by
      rw [ae_dirac_mem_iff, ae_dirac_mem_iff, h u]

theorem speaker_listener_truthful_dirac_le_of_subset (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) {w w' : W}
    (hw : μ {w} ≠ 0) (hsub : ∀ u, w ∈ sem u → w' ∈ sem u) {u : U} (hu : w ∈ sem u) :
    speaker α C (listener μ (truthful sem)) Measure.dirac w' {u}
      ≤ speaker α C (listener μ (truthful sem)) Measure.dirac w {u} := by
  rcases eq_or_ne (μ {w'}) 0 with hw' | hw'
  · rw [speaker_dirac_apply_singleton_eq_zero hα (not_not.mp fun h ↦
      ((listener_truthful_apply_singleton_ne_zero_iff μ sem u w').mp h).2 hw')]
    exact zero_le
  · exact speaker_listener_truthful_apply_singleton_le hα (dirac_absolutelyContinuous hw)
      (dirac_absolutelyContinuous hw')
      (fun v hv ↦ ae_dirac_mem_iff.2 (hsub v (ae_dirac_mem_iff.1 hv))) (ae_dirac_mem_iff.2 hu)

omit [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U] in
private theorem exp_utility_dirac (C : U → ℝ) (L : U → Measure W) (w : W) (u : U) :
    EReal.exp (utility C L (Measure.dirac w) u) = L u {w} * ENNReal.ofReal (Real.exp (-C u)) := by
  rw [utility_dirac, sub_eq_add_neg, EReal.exp_add, ENNReal.exp_log, ← EReal.coe_neg,
    EReal.exp_coe]

omit [Fintype U] [MeasurableSingletonClass U] in
private theorem utility_dirac_ne_top [IsFiniteKernel L] (C : U → ℝ) (w : W) (u : U) :
    utility C L (Measure.dirac w) u ≠ ⊤ := by
  rw [ne_eq, ← EReal.exp_eq_top_iff, exp_utility_dirac]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

open Filter Topology in
/-- As rationality grows, the speaker puts all her mass on the utterance whose listener mass,
discounted by its cost, is greatest at `w`, so the fully rational speaker maximizes the utility. -/
theorem tendsto_speaker_dirac_real_singleton_atTop [IsFiniteKernel L] (hu : L u {w} ≠ 0)
    (hmax : ∀ u' ≠ u, (L u' {w}).toReal * Real.exp (-C u') < (L u {w}).toReal * Real.exp (-C u)) :
    Tendsto (fun α ↦ (speaker α C L Measure.dirac w).real {u}) atTop (𝓝 1) := by
  refine Kernel.tendsto_softmax_mul_real_singleton_atTop
    (V := fun w u ↦ utility C L (Measure.dirac w) u) (w := w) ?_ (utility_dirac_ne_top C w u)
    fun v hv ↦ ?_
  · rw [ne_eq, ← EReal.exp_eq_zero_iff, exp_utility_dirac]
    exact mul_ne_zero hu (ofReal_exp_ne_zero _)
  · have hne (x : U) : L x {w} * ENNReal.ofReal (Real.exp (-C x)) ≠ ∞ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    rw [← EReal.exp_lt_exp_iff, exp_utility_dirac, exp_utility_dirac,
      ← ENNReal.toReal_lt_toReal (hne v) (hne u), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    exact hmax v hv

open Filter Topology in
/-- As rationality vanishes, the speaker who knows the state chooses evenly among the utterances
her listener can interpret there, whatever their costs. -/
theorem tendsto_speaker_dirac_real_singleton_nhdsGT_zero [IsFiniteKernel L] (C : U → ℝ) (w : W)
    (u : U) : Tendsto (fun α ↦ (speaker α C L Measure.dirac w).real {u}) (𝓝[>] 0)
      (𝓝 ((uniformOn {v | L v {w} ≠ 0}).real {u})) := by
  have hset : {v | utility C L (Measure.dirac w) v ≠ ⊥} = {v | L v {w} ≠ 0} := Set.ext fun v ↦ by
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ne_eq, ← EReal.exp_eq_zero_iff, exp_utility_dirac,
      mul_eq_zero, not_or]
    exact and_iff_left (ofReal_exp_ne_zero _)
  rw [← hset]
  exact Kernel.tendsto_softmax_mul_real_singleton_nhdsGT_zero
    (V := fun w u ↦ utility C L (Measure.dirac w) u) (utility_dirac_ne_top C w) u

theorem speaker_listener_truthful_dirac_zero_real_singleton_of_pair (hα : 0 < α)
    (μ : Measure W) [IsFiniteMeasure μ] (sem : U → Set W) (hμ : μ {w} ≠ 0)
    {u u' : U} (huu' : u ≠ u') (hu : w ∈ sem u) (hu' : w ∈ sem u')
    (hsupp : ∀ v, w ∈ sem v → v = u ∨ v = u') :
    (speaker α 0 (listener μ (truthful sem)) Measure.dirac w).real {u} =
      μ.real (sem u') ^ α / (μ.real (sem u) ^ α + μ.real (sem u') ^ α) := by
  have hx : 0 < μ.real {w} := ENNReal.toReal_pos hμ (measure_ne_top _ _)
  have hpos {v : U} (hv : w ∈ sem v) : 0 < μ.real (sem v) :=
    hx.trans_le (measureReal_mono (Set.singleton_subset_iff.2 hv))
  have hterm {v : U} (hv : w ∈ sem v) : (listener μ (truthful sem) v {w} ^ α).toReal =
      μ.real {w} ^ α / μ.real (sem v) ^ α := by
    rw [← ENNReal.toReal_rpow, ← measureReal_def, listener_truthful_real_singleton μ sem hv,
      Real.div_rpow hx.le (hpos hv).le]
  rw [speaker_dirac_zero_real_singleton hα.le, Finset.sum_eq_add u u' huu' (fun v _ hv ↦ ?_)
      (by simp) (by simp), hterm hu, hterm hu']
  · have := hpos hu
    have := hpos hu'
    field_simp
    ring
  · rw [listener_truthful_apply_singleton_of_notMem μ sem fun h ↦ (hsupp v h).elim hv.1 hv.2,
      ENNReal.zero_rpow_of_pos hα, ENNReal.toReal_zero]

end Dirac

/-! #### The heard form

When the listener hears only the form `obs u` of the speaker's choice `u` (eqs. 18b/21b), her
state is the pair of the world and the choice, her prior the joint of the world prior and the
speaker, and her channel the point mass at the form. Her first marginal is her belief about the
world and her second her belief about the choice. -/

private theorem compProd_real_mul_dirac_real [MeasurableSingletonClass W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass O] [DecidableEq O] (μ : Measure W)
    [SFinite μ] (κ : Kernel W U) [IsSFiniteKernel κ] (obs : U → O) (o : O) (w : W) (u : U) :
    (μ ⊗ₘ κ).real {(w, u)} * (Measure.dirac (obs u)).real {o} =
      if obs u = o then μ.real {w} * (κ w).real {u} else 0 := by
  rw [measureReal_def, measureReal_def, Measure.compProd_apply_singleton, ENNReal.toReal_mul,
    Measure.dirac_apply' _ (measurableSet_singleton o), ← measureReal_def, ← measureReal_def]
  split_ifs with h <;> simp [h]

section Form

variable [Fintype W] [MeasurableSingletonClass W] [Fintype U] [MeasurableSingletonClass U]
  [Countable O] [MeasurableSingletonClass O] (μ : Measure W) [IsFiniteMeasure μ] (κ : Kernel W U)
  [IsFiniteKernel κ] (obs : U → O)

theorem listener_compProd_dirac_apply_singleton_ne_zero_iff (o : O) (w : W) (u : U) :
    listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o {(w, u)} ≠ 0 ↔
      obs u = o ∧ μ {w} ≠ 0 ∧ κ w {u} ≠ 0 := by
  rw [listener_apply_singleton_ne_zero_iff, Measure.compProd_apply_singleton, mul_ne_zero_iff,
    Measure.dirac_apply' _ (measurableSet_singleton o)]
  by_cases h : obs u = o <;> simp [h]

variable [DecidableEq O]

/-- The listener of the form prefers the state with the greater prior-weighted production
probability pooled over the choices with the form heard. -/
theorem listener_compProd_dirac_fst_real_lt_iff (o : O) (w₁ w₂ : W) :
    (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₁} <
        (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₂} ↔
      ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₁} * (κ w₁).real {u} <
        ∑ u ∈ Finset.univ.filter (obs · = o), μ.real {w₂} * (κ w₂).real {u} := by
  rw [listener_fst_real_lt_iff]
  simp only [compProd_real_mul_dirac_real, Finset.sum_filter]

/-- Between two choices with the form heard, the listener of the form prefers the one with the
greater prior-weighted production probability pooled over the states. -/
theorem listener_compProd_dirac_snd_real_lt_iff {o : O} {u₁ u₂ : U} (h₁ : obs u₁ = o)
    (h₂ : obs u₂ = o) :
    (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₁} <
        (listener (μ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₂} ↔
      ∑ w, μ.real {w} * (κ w).real {u₁} < ∑ w, μ.real {w} * (κ w).real {u₂} := by
  rw [listener_snd_real_lt_iff]
  simp only [compProd_real_mul_dirac_real, ite_eq_left h₁, ite_eq_left h₂]

/-- At a uniform prior the listener of the form prefers the state likelier to produce a choice
with the form heard. -/
theorem listener_uniformOn_compProd_dirac_fst_real_lt_iff (o : O) (w₁ w₂ : W) :
    (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₁} <
        (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).fst.real {w₂} ↔
      (κ w₁).real ↑(Finset.univ.filter (obs · = o)) <
        (κ w₂).real ↑(Finset.univ.filter (obs · = o)) := by
  have : Nonempty W := ⟨w₁⟩
  simp_rw [listener_compProd_dirac_fst_real_lt_iff, uniformOn_univ_real_singleton,
    ← Finset.mul_sum, sum_measureReal_singleton]
  exact mul_lt_mul_iff_right₀ (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

/-- At a uniform prior the listener of the form prefers, of two choices with the form heard, the
one the states together are likelier to produce. -/
theorem listener_uniformOn_compProd_dirac_snd_real_lt_iff {o : O} {u₁ u₂ : U} (h₁ : obs u₁ = o)
    (h₂ : obs u₂ = o) :
    (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₁} <
        (listener (uniformOn Set.univ ⊗ₘ κ) (fun p ↦ Measure.dirac (obs p.2)) o).snd.real {u₂} ↔
      ∑ w, (κ w).real {u₁} < ∑ w, (κ w).real {u₂} := by
  rcases isEmpty_or_nonempty W with hW | hW
  · simp [listener_compProd_dirac_snd_real_lt_iff _ κ obs h₁ h₂]
  · simp_rw [listener_compProd_dirac_snd_real_lt_iff _ κ obs h₁ h₂, uniformOn_univ_real_singleton,
      ← Finset.mul_sum]
    exact mul_lt_mul_iff_right₀ (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

end Form

/-! #### Pragmatic listeners

The pragmatic listener (eq. 3) is the listener of a speaker. -/

section Listener

variable [Fintype W] [DiscreteMeasurableSpace W] [Fintype U] [MeasurableSingletonClass U]

theorem listener_speaker_listener_truthful_apply_singleton_of_notMem {α : ℝ} (hα : 0 < α)
    (C : U → ℝ) (μ : Measure W) (sem : U → Set W) {u : U} {w : W} (hw : w ∉ sem u) :
    listener μ (speaker α C (listener μ (truthful sem)) Measure.dirac) u {w} = 0 :=
  listener_apply_singleton_eq_zero (speaker_dirac_apply_singleton_eq_zero hα
    (listener_truthful_apply_singleton_of_notMem μ sem hw))

end Listener

end Pipeline

end RSA
