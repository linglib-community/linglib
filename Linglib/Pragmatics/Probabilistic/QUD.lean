module

public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Pragmatics.Probabilistic.Latent
public import Linglib.Pragmatics.Probabilistic.Literal

/-!
# Speakers who address a question

A question under discussion is a function `q : W → X` from states to answers. In the models of
Kao and colleagues [the speaker](##RSA.qudSpeaker) knows the answer `q w` at her state and is
informative about the answer alone: she addresses the pushforward `L.map q` of the listener's
belief about the state. At the identity question she is [the speaker who knows the
state](##RSA.qudSpeaker_id), at a constant one she [only weighs costs](##RSA.qudSpeaker_const),
and [a coarser question lets her say more](##RSA.qudSpeaker_apply_singleton_ne_zero_of_coarser).
Under a literal listener she [produces an utterance exactly when it is true at a state of positive
prior with her answer](##RSA.qudSpeaker_literalListener_apply_singleton_ne_zero_iff), whether or
not it is true at hers. A listener unsure of the question holds it as a latent coordinate of the
state, as in lexical uncertainty, and such an utterance leads her to states where it is false,
which is how the models derive hyperbole, metaphor and irony. The question is [sufficient for the
listener](##RSA.cond_listener_qudSpeaker_preimage): she learns the speaker's answer, and given the
answer, [or the question and the answer when she is unsure of the
question](##RSA.cond_listener_prod_qudSpeaker_preimage), she believes what the prior does. In
these models an utterance names one coordinate of the state, and at a prior that factors through
that coordinate [the literal listener does not depend on its
marginal](##RSA.literalListener_preimage_fst_compProd_congr).

## References

* [kao-etal-2014-hyperbole]
* [kao-etal-2014-metaphor]
* [kao-goodman-2015]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U X : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace X] [MeasurableSingletonClass X]

omit [MeasurableSingletonClass U] in
/-- A coarser question raises the listener's probability of the answer at a state. -/
theorem map_apply_singleton_le_of_coarser {X' : Type*} [MeasurableSpace X']
    [MeasurableSingletonClass X'] [Countable W] [MeasurableSingletonClass W] (L : Kernel U W)
    {q : W → X} {q' : W → X'} {w : W} (h : ∀ w', q w' = q w → q' w' = q' w) (u : U) :
    L.map q u {q w} ≤ L.map q' u {q' w} := by
  rw [Kernel.map_apply' _ .of_discrete _ (.singleton _),
    Kernel.map_apply' _ .of_discrete _ (.singleton _)]
  exact measure_mono fun w' hw' ↦ h w' hw'

/-! ### The speaker -/

variable [Fintype U] [Fintype X] {α : ℝ}

/-- The speaker who addresses the question `q`. At the state `w` she knows the answer `q w` and
soft-maximizes the log of the listener's probability of that answer, less the cost. -/
noncomputable def qudSpeaker (α : ℝ) (C : U → ℝ) (L : Kernel U W) (q : W → X) (w : W) :
    Measure U :=
  speaker α C (L.map q) Measure.dirac (q w)

section

variable (C : U → ℝ) (L : Kernel U W) (q : W → X)

instance (w : W) : IsZeroOrProbabilityMeasure (qudSpeaker α C L q w) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (speaker α C (L.map q) Measure.dirac (q w)))

omit [MeasurableSingletonClass U] in
variable {q} in
theorem qudSpeaker_eq_of_eq {w w' : W} (h : q w = q w') :
    qudSpeaker α C L q w = qudSpeaker α C L q w' := by
  rw [qudSpeaker, qudSpeaker, h]

omit [MeasurableSingletonClass U] in
/-- At the identity question she is the speaker who knows the state. -/
theorem qudSpeaker_id (L : Kernel U X) (x : X) :
    qudSpeaker α C L id x = speaker α C L Measure.dirac x := by
  rw [qudSpeaker, Kernel.map_id, id]

/-- At a constant question the answer tells the listener nothing and she only weighs costs. -/
theorem qudSpeaker_const [Countable W] [MeasurableSingletonClass W] [IsMarkovKernel L] (x : X)
    (w : W) (u : U) :
    qudSpeaker α C L (fun _ ↦ x) w {u} =
      ENNReal.ofReal (Real.exp (-(α * C u))) / ∑ u', ENNReal.ofReal (Real.exp (-(α * C u'))) := by
  have h (v : U) : L.map (fun _ ↦ x) v {x} = 1 := by
    rw [Kernel.map_apply' _ .of_discrete _ (.singleton _),
      Set.preimage_const_of_mem (Set.mem_singleton x), measure_univ]
  simp only [qudSpeaker, speaker_dirac_apply_singleton, h, ENNReal.one_rpow, one_mul]

variable {C L q} in
/-- A coarser question lets her say more: an utterance she can produce addressing a question she
can produce addressing any question that identifies at least the states it does. -/
theorem qudSpeaker_apply_singleton_ne_zero_of_coarser {X' : Type*} [MeasurableSpace X']
    [MeasurableSingletonClass X'] [Fintype X'] [Countable W] [MeasurableSingletonClass W]
    [IsFiniteKernel L] (hα : 0 < α) {q' : W → X'} {w : W}
    (h : ∀ w', q w' = q w → q' w' = q' w) {u : U} (hu : qudSpeaker α C L q w {u} ≠ 0) :
    qudSpeaker α C L q' w {u} ≠ 0 := by
  rw [qudSpeaker, speaker_dirac_apply_singleton_ne_zero_iff hα] at hu ⊢
  exact fun h0 ↦ hu (le_antisymm ((map_apply_singleton_le_of_coarser L h u).trans h0.le) zero_le)

end

/-- **Nonliteral production.** The speaker who addresses a question to a literal listener
produces an utterance exactly when it is true at a state of positive prior with the same answer as
hers, whether or not it is true at her own state. -/
theorem qudSpeaker_literalListener_apply_singleton_ne_zero_iff [Fintype W]
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (q : W → X) (w : W) (u : U) :
    qudSpeaker α C (literalListener μ sem) q w {u} ≠ 0 ↔
      ∃ w', q w' = q w ∧ w' ∈ sem u ∧ μ {w'} ≠ 0 := by
  simp only [qudSpeaker, speaker_dirac_apply_singleton_ne_zero_iff hα]
  rw [Kernel.map_apply' _ .of_discrete _ (.singleton _), ne_eq,
    measure_null_iff_singleton (Set.to_countable _)]
  simp [literalListener_apply_singleton_ne_zero_iff]

/-! ### The listener -/

/-- A meaning under uncertainty about the question is possible after an utterance exactly when it
has positive prior and, under some question of positive prior, shares its answer with a state of
positive prior where the utterance is true. -/
theorem listener_prod_fst_qudSpeaker_literalListener_apply_singleton_ne_zero_iff [Fintype W]
    {B : Type*} [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (ν : Measure B) [IsFiniteMeasure ν] (sem : U → Set W) (q : B → W → X) (u : U) (w : W) :
    (listener (μ.prod ν) (fun p ↦ qudSpeaker α C (literalListener μ sem) (q p.2) p.1) u).fst
        {w} ≠ 0 ↔
      μ {w} ≠ 0 ∧ ∃ b, ν {b} ≠ 0 ∧ ∃ w', q b w' = q b w ∧ w' ∈ sem u ∧ μ {w'} ≠ 0 := by
  rw [listener_prod_fst_apply_singleton_ne_zero_iff]
  simp only [qudSpeaker_literalListener_apply_singleton_ne_zero_iff hα]

/-- **A question is sufficient for the listener.** Against a speaker who addresses a question, the
listener who learns the speaker's answer, at a state where the speaker can produce the utterance,
holds the prior conditioned on that answer. -/
theorem cond_listener_qudSpeaker_preimage [DiscreteMeasurableSpace W] (C : U → ℝ)
    (L : Kernel U W) (μ : Measure W) [IsFiniteMeasure μ] (q : W → X) {u : U} {w : W}
    (h : qudSpeaker α C L q w {u} ≠ 0) :
    (listener μ (qudSpeaker α C L q) u)[|q ⁻¹' {q w}] = μ[|q ⁻¹' {q w}] := by
  refine cond_listener_apply .of_discrete h (measure_ne_top _ _)
    (fun w' hw' ↦ by rw [qudSpeaker_eq_of_eq C L hw'])
    (ne_top_of_le_ne_top (measure_ne_top μ Set.univ) ?_)
  calc ∫⁻ w, qudSpeaker α C L q w {u} ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun _ ↦ prob_le_one
    _ = μ Set.univ := by rw [lintegral_one]

/-- A listener unsure of the question who learns the question and the speaker's answer to it, at
a state where the speaker can produce the utterance, holds the prior conditioned on them. -/
theorem cond_listener_prod_qudSpeaker_preimage {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] [DiscreteMeasurableSpace W] (C : U → ℝ) (L : Kernel U W)
    (μ : Measure W) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν] (q : B → W → X) {u : U}
    {b : B} {w : W} (h : qudSpeaker α C L (q b) w {u} ≠ 0) :
    (listener (μ.prod ν) (fun p ↦ qudSpeaker α C L (q p.2) p.1) u)[|
        (q b ⁻¹' {q b w}) ×ˢ {b}] = (μ.prod ν)[|(q b ⁻¹' {q b w}) ×ˢ {b}] := by
  refine cond_listener_apply (MeasurableSet.of_discrete.prod (measurableSet_singleton b)) h
    (measure_ne_top _ _) (fun p hp ↦ ?_)
    (ne_top_of_le_ne_top (measure_ne_top (μ.prod ν) Set.univ) ?_)
  · obtain ⟨hx, rfl⟩ : q b p.1 = q b w ∧ p.2 = b := hp
    exact congrArg (· {u}) (qudSpeaker_eq_of_eq C L hx)
  · calc ∫⁻ p, qudSpeaker α C L (q p.2) p.1 {u} ∂μ.prod ν ≤ ∫⁻ _, 1 ∂μ.prod ν :=
          lintegral_mono fun _ ↦ prob_le_one
      _ = (μ.prod ν) Set.univ := by rw [lintegral_one]

end RSA
