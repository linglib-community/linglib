module

public import Linglib.Core.Analysis.SpecialFunctions.Pow.NNReal
public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.MeasureTheory.Measure.AbsolutelyContinuous
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.MeasureTheory.Measure.GeomMean
public import Linglib.Core.Probability.Kernel.OfWeights
public import Linglib.Core.Probability.Kernel.Softmax
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Data.EReal.BigOperators

/-!
# The speaker of the Rational Speech Act model

The [speaker](##RSA.speaker) believes a measure on states, addresses a listener, and is the
softmax of her [utility](##RSA.utility), the expected log of the listener's mass under her belief
less a cost. Written without logarithms, [her weight for an utterance](##RSA.speaker_eq_ofWeights)
is the geometric mean of the listener's mass over her belief, to the power of the rationality,
times the cost weight. A speaker who knows the state believes the point mass there and [weighs an
utterance by the listener's mass at the state](##RSA.speaker_dirac_eq_ofWeights).

## Implementation notes

* Rationality and cost are arguments, so findings quantify over them.
* The decision rule is `Kernel.softmax`, so a speaker whose utility is not an expected
  log-probability, such as a question- or politeness-weighted one, is that rule at her own score,
  with `⊥` marking the utterances she cannot use.

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

/-! #### The speaker

A speaker believes a measure on states and addresses a listener. Her weight for an utterance is
the exponential of the rationality times its utility: the expected log of the listener's mass
under her belief, less a real cost. Written without logarithms, the weight is the geometric mean
of the listener's mass over her belief, to the power of the rationality, times the cost weight
`exp (-(α * C u))`. -/

private theorem geomMean_weight_ne_top [Fintype W] {β ν : Measure W} [IsFiniteMeasure ν] {α : ℝ}
    (hα : 0 ≤ α) (c : ℝ) : β.geomMean (fun w ↦ ν {w}) ^ α * ENNReal.ofReal (Real.exp c) ≠ ∞ :=
  ENNReal.rpow_mul_ofReal_exp_ne_top hα (Measure.geomMean_ne_top fun _ _ ↦ measure_ne_top _ _) c

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
    (h0.imp fun _ hu ↦ ENNReal.rpow_mul_ofReal_exp_ne_zero hα (Measure.geomMean_ne_zero hu) _)
    fun _ ↦ geomMean_weight_ne_top hα _

theorem isMarkovKernel_speaker (hα : 0 ≤ α)
    (h0 : ∀ o, ∃ u, ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) : IsMarkovKernel (speaker α C L b) :=
  ⟨fun o ↦ isProbabilityMeasure_speaker hα (h0 o)⟩

variable [MeasurableSingletonClass U]

theorem speaker_apply_singleton_ne_zero (hα : 0 ≤ α) (h : ∀ w, b o {w} ≠ 0 → L u {w} ≠ 0) :
    speaker α C L b o {u} ≠ 0 :=
  speaker_eq_ofWeights α C L b ▸ Kernel.ofWeights_apply_singleton_ne_zero
    (ENNReal.rpow_mul_ofReal_exp_ne_zero hα (Measure.geomMean_ne_zero h) _)
    fun _ ↦ geomMean_weight_ne_top hα _

/-- Of two utterances the speaker prefers the one of greater weight; the normalization cancels. -/
theorem speaker_real_singleton_lt_iff (hα : 0 ≤ α) {u u' : U} :
    (speaker α C L b o).real {u} < (speaker α C L b o).real {u'} ↔
      (b o).geomMean (fun w ↦ L u {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u))) <
        (b o).geomMean (fun w ↦ L u' {w}) ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) :=
  speaker_eq_ofWeights α C L b ▸ Kernel.ofWeights_real_singleton_lt_iff o
    fun _ ↦ geomMean_weight_ne_top hα _

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
      ENNReal.toReal_pos (ENNReal.rpow_mul_ofReal_exp_ne_zero hα hu _)
        (geomMean_weight_ne_top hα _)⟩
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
    mul_eq_zero, or_iff_left (ENNReal.ofReal_exp_ne_zero _), ENNReal.rpow_eq_zero_iff_of_pos hα,
    Measure.geomMean_eq_zero_iff]

theorem speaker_apply_singleton_eq_zero_iff_not_ac [IsFiniteMeasure (b o)] (hα : 0 < α) :
    speaker α C L b o {u} = 0 ↔ ¬ b o ≪ L u := by
  rw [speaker_apply_singleton_eq_zero_iff hα, Measure.absolutelyContinuous_iff_forall_singleton,
    not_forall]
  exact exists_congr fun w ↦ by rw [Classical.not_imp, and_comm]

end Speaker

/-! #### The speaker who knows the state

The speaker of eqs. 2/6–7 knows the state, so she believes the point mass there, and her weight
for an utterance is the listener's mass at the state to the power `α`, times the cost weight. -/

section Dirac

variable [MeasurableSingletonClass W]

variable [Fintype W] [Fintype U] {α : ℝ} {C : U → ℝ} {L : Kernel U W} {w : W} {u : U}

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
    Measure.eq_of_dirac_apply_singleton_ne_zero hw' ▸ hu)

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

/-- Relabelling the states by `e` and the utterances by `τ` relabels the speaker who knows the
state: she is the speaker of the relabelled listener, at the relabelled costs. -/
theorem speaker_dirac_relabel {W' U' : Type*} [MeasurableSpace W'] [Fintype W']
    [MeasurableSingletonClass W'] [MeasurableSpace U'] [Fintype U'] [MeasurableSingletonClass U']
    (e : W ≃ W') (τ : U ≃ U') (α : ℝ) (C : U → ℝ) (L : U → Measure W) :
    ((speaker α C L Measure.dirac).comap e.symm .of_discrete).map τ =
      speaker α (C ∘ τ.symm) (fun u' ↦ (L (τ.symm u')).map e) Measure.dirac := by
  rw [speaker_dirac_eq_softmax, speaker_dirac_eq_softmax, Kernel.softmax_comap,
    Kernel.softmax_map_equiv]
  congr 1
  funext w' u'
  rw [Measure.map_apply .of_discrete (.singleton w'), ← Equiv.image_symm_eq_preimage,
    Set.image_singleton]
  rfl

theorem speaker_dirac_apply_singleton_eq_zero (hα : 0 < α) (h : L u {w} = 0) :
    speaker α C L Measure.dirac w {u} = 0 := by
  rw [speaker_dirac_eq_ofWeights]
  exact Kernel.ofWeights_apply_singleton_eq_zero (by rw [h, ENNReal.zero_rpow_of_pos hα, zero_mul])

theorem speaker_dirac_apply_singleton_ne_zero [IsFiniteKernel L] (hα : 0 ≤ α) (h : L u {w} ≠ 0) :
    speaker α C L Measure.dirac w {u} ≠ 0 :=
  speaker_apply_singleton_ne_zero hα fun _ hw' ↦ Measure.eq_of_dirac_apply_singleton_ne_zero hw' ▸ h

theorem speaker_dirac_apply_singleton_ne_zero_iff [IsFiniteKernel L] (hα : 0 < α) :
    speaker α C L Measure.dirac w {u} ≠ 0 ↔ L u {w} ≠ 0 :=
  ⟨fun h h' ↦ h (speaker_dirac_apply_singleton_eq_zero hα h'),
    speaker_dirac_apply_singleton_ne_zero hα.le⟩

theorem speaker_dirac_apply_singleton_eq_one [IsFiniteKernel L] (hα : 0 < α) (h : L u {w} ≠ 0)
    (hother : ∀ u' ≠ u, L u' {w} = 0) : speaker α C L Measure.dirac w {u} = 1 := by
  rw [speaker_dirac_apply_singleton, Finset.sum_eq_single u
    (fun u' _ hu' ↦ by rw [hother u' hu', ENNReal.zero_rpow_of_pos hα, zero_mul])
    (fun hu ↦ absurd (Finset.mem_univ u) hu)]
  exact ENNReal.div_self (ENNReal.rpow_mul_ofReal_exp_ne_zero hα.le h _)
    (ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (measure_ne_top _ _) _)

theorem speaker_dirac_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α C L Measure.dirac w).real {u}
      = (L u {w} ^ α).toReal * Real.exp (-(α * C u))
        / ∑ u', (L u' {w} ^ α).toReal * Real.exp (-(α * C u')) := by
  rw [measureReal_def, speaker_dirac_apply_singleton, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun u' _ ↦ ENNReal.rpow_mul_ofReal_exp_ne_top hα (measure_ne_top _ _) _]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem speaker_dirac_zero_real_singleton [IsFiniteKernel L] (hα : 0 ≤ α) (u : U) :
    (speaker α 0 L Measure.dirac w).real {u} =
      (L u {w} ^ α).toReal / ∑ u', (L u' {w} ^ α).toReal := by
  rw [speaker_dirac_real_singleton hα]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- Of two utterances the speaker who knows the state prefers the one of greater weight; the
normalization cancels. -/
theorem speaker_dirac_real_singleton_lt_iff [IsFiniteKernel L] (hα : 0 ≤ α) {u u' : U} :
    (speaker α C L Measure.dirac w).real {u} < (speaker α C L Measure.dirac w).real {u'} ↔
      L u {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u)))
        < L u' {w} ^ α * ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  have := speaker_real_singleton_lt_iff (C := C) (L := L) (b := Measure.dirac) (o := w) (u := u)
    (u' := u') hα
  simpa only [Measure.geomMean_dirac] using this

theorem speaker_dirac_real_singleton_div [IsFiniteKernel L] (hα : 0 ≤ α) (h : L u {w} ≠ 0)
    (u' : U) :
    (speaker α C L Measure.dirac w).real {u'} / (speaker α C L Measure.dirac w).real {u} =
      ((L u' {w}).toReal / (L u {w}).toReal) ^ α * Real.exp (-(α * (C u' - C u))) := by
  simpa only [Measure.geomMean_dirac] using speaker_real_singleton_div (C := C) (L := L)
    (b := Measure.dirac) (o := w) hα
    (fun _ hw' ↦ Measure.eq_of_dirac_apply_singleton_ne_zero hw' ▸ h) u'

/-- Of two utterances with listener mass at the state, the speaker prefers the one of greater
utility, the log of the listener's mass less the cost. -/
theorem speaker_dirac_real_singleton_lt_iff_log [IsFiniteKernel L] (hα : 0 < α) {u' : U}
    (hu : L u {w} ≠ 0) (hu' : L u' {w} ≠ 0) :
    (speaker α C L Measure.dirac w).real {u} < (speaker α C L Measure.dirac w).real {u'} ↔
      Real.log (L u {w}).toReal - C u < Real.log (L u' {w}).toReal - C u' := by
  rw [speaker_dirac_real_singleton_lt_iff hα.le,
    ← ENNReal.toReal_lt_toReal (ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (measure_ne_top _ _) _)
      (ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (measure_ne_top _ _) _),
    ENNReal.toReal_rpow_mul_ofReal_exp hu (measure_ne_top _ _),
    ENNReal.toReal_rpow_mul_ofReal_exp hu' (measure_ne_top _ _),
    Real.exp_lt_exp, mul_lt_mul_iff_of_pos_left hα]

theorem speaker_dirac_real_singleton_of_pair [IsFiniteKernel L] (hα : 0 < α) {u' : U}
    (huu' : u ≠ u') (hu : L u {w} ≠ 0) (hu' : L u' {w} ≠ 0)
    (hsupp : ∀ v, L v {w} ≠ 0 → v = u ∨ v = u') :
    (speaker α C L Measure.dirac w).real {u} = Real.sigmoid
      (α * ((Real.log (L u {w}).toReal - C u) - (Real.log (L u' {w}).toReal - C u'))) := by
  rw [speaker_dirac_eq_ofWeights, Kernel.ofWeights_real_singleton_of_pair w huu'
      (fun v ↦ ENNReal.rpow_mul_ofReal_exp_ne_top hα.le (measure_ne_top _ _) _)
      (fun v hv ↦ hsupp v fun h ↦ hv (by rw [h, ENNReal.zero_rpow_of_pos hα, zero_mul])),
    ENNReal.toReal_rpow_mul_ofReal_exp hu (measure_ne_top _ _),
    ENNReal.toReal_rpow_mul_ofReal_exp hu' (measure_ne_top _ _),
    Real.exp_div_add_exp_eq_sigmoid, ← mul_sub]
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
    exact mul_ne_zero hu (ENNReal.ofReal_exp_ne_zero _)
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
    exact and_iff_left (ENNReal.ofReal_exp_ne_zero _)
  rw [← hset]
  exact Kernel.tendsto_softmax_mul_real_singleton_nhdsGT_zero
    (V := fun w u ↦ utility C L (Measure.dirac w) u) (utility_dirac_ne_top C w) u

end Dirac

end Pipeline

end RSA
