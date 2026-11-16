module

public import Linglib.Core.Probability.Kernel.Basic
public import Linglib.Pragmatics.Probabilistic.LexicalUncertainty

/-!
# Speakers who address a question

A question under discussion is a function `q : W → X` from states to answers. In the models of
Kao and colleagues the speaker knows the answer `q w` at her state and is informative about the
answer alone: she addresses the pushforward `L.map q` of the listener's belief about the state.
Under a literal listener this pushforward gives an answer [the prior's share of the states with
that answer where the utterance is true](##listener_truthful_map_apply_singleton), so the speaker
[produces an utterance exactly when it is true at a state of positive prior with her
answer](##speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff), whether or not it is
true at hers. A listener unsure of the question holds it as a latent coordinate of the state, as
in lexical uncertainty, and such an utterance leads her to states where it is false, which is how
the models derive hyperbole, metaphor and irony. The question is [sufficient for the
listener](##cond_listener_speaker_map_dirac_preimage): she learns the speaker's answer, and given
the answer, [or the question and the answer when she is unsure of the
question](##cond_listener_prod_speaker_map_dirac_preimage), she believes what the prior does. In these models an utterance names one coordinate of
the state, and at a prior that factors through that coordinate [the literal listener does not
depend on its marginal](##listener_truthful_preimage_fst_compProd).

## References

* [kao-etal-2014-hyperbole]
* [kao-etal-2014-metaphor]
* [kao-goodman-2015]
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RSA

variable {W U X : Type*} [MeasurableSpace W] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A literal listener's probability of an answer is the prior mass of the states with that
answer where the utterance is true, over the prior mass of the states where it is true. -/
theorem listener_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] (μ : Measure W) (sem : U → Set W) (q : W → X) (u : U) (x : X) :
    (listener μ (truthful sem)).map q u {x} = μ (sem u ∩ q ⁻¹' {x}) / μ (sem u) := by
  rw [Kernel.map_apply_singleton, listener_truthful_apply, cond_apply .of_discrete,
    ENNReal.div_eq_inv_mul]

/-- Within a finite context set, a literal listener's probability of an answer is the prior mass
of the states of the set where the utterance is true and that have the answer, over the prior
mass of the states of the set where it is true. -/
theorem listener_restrict_truthful_map_apply_singleton [Countable W] [DiscreteMeasurableSpace W]
    [Countable U] [DecidableEq X] (μ : Measure W) (C : Finset W) (sem : U → Set W)
    [∀ u, DecidablePred (· ∈ sem u)] (q : W → X) (u : U) (x : X) :
    (listener (μ.restrict ↑C) (truthful sem)).map q u {x} =
      μ ↑((C.filter (· ∈ sem u)).filter (q · = x)) / μ ↑(C.filter (· ∈ sem u)) := by
  rw [listener_truthful_map_apply_singleton, Measure.restrict_apply .of_discrete,
    Measure.restrict_apply .of_discrete]
  congr 2 <;> ext <;> simp [and_comm, and_left_comm]

variable [Fintype W] [Fintype U] [Fintype X] {α : ℝ}

/-- **Nonliteral production.** The speaker who addresses a question to a literal listener
produces an utterance exactly when it is true at a state of positive prior with the same answer as
hers, whether or not it is true at her own state. -/
theorem speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (sem : U → Set W) (q : W → X) (w : W) (u : U) :
    speaker α C ((listener μ (truthful sem)).map q) Measure.dirac (q w) {u} ≠ 0 ↔
      ∃ w', q w' = q w ∧ w' ∈ sem u ∧ μ {w'} ≠ 0 := by
  simp only [speaker_dirac_apply_singleton_ne_zero_iff hα, Kernel.map_apply_singleton_ne_zero_iff,
    listener_truthful_apply_singleton_ne_zero_iff]

/-- A meaning under uncertainty about the question is possible after an utterance exactly when it
has positive prior and, under some question of positive prior, shares its answer with a state of
positive prior where the utterance is true. -/
theorem listener_prod_fst_speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff
    {B : Type*} [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [DiscreteMeasurableSpace W] (hα : 0 < α) (C : U → ℝ) (μ : Measure W) [IsFiniteMeasure μ]
    (ν : Measure B) [IsFiniteMeasure ν] (sem : U → Set W) (q : B → W → X) (u : U) (w : W) :
    (listener (μ.prod ν) (fun p ↦ speaker α C ((listener μ (truthful sem)).map (q p.2))
        Measure.dirac (q p.2 p.1)) u).fst {w} ≠ 0 ↔
      μ {w} ≠ 0 ∧ ∃ b, ν {b} ≠ 0 ∧ ∃ w', q b w' = q b w ∧ w' ∈ sem u ∧ μ {w'} ≠ 0 := by
  rw [listener_prod_fst_apply_singleton_ne_zero_iff]
  simp only [speaker_listener_truthful_map_dirac_apply_singleton_ne_zero_iff hα]

omit [Fintype W] in
/-- **A question is sufficient for the listener.** Against a speaker who addresses a question, the
listener who learns the speaker's answer, at an answer where the speaker can produce the
utterance, holds the prior conditioned on that answer. -/
theorem cond_listener_speaker_map_dirac_preimage [DiscreteMeasurableSpace W] (C : U → ℝ)
    (L : Kernel U W) (μ : Measure W) [IsFiniteMeasure μ] (q : W → X) {u : U} {x : X}
    (h : speaker α C (L.map q) Measure.dirac x {u} ≠ 0) :
    (listener μ (fun w ↦ speaker α C (L.map q) Measure.dirac (q w)) u)[|q ⁻¹' {x}] =
      μ[|q ⁻¹' {x}] := by
  refine cond_listener_apply .of_discrete h (measure_ne_top _ _)
    (fun w hw ↦ by rw [show q w = x from hw]) (ne_top_of_le_ne_top (measure_ne_top μ Set.univ) ?_)
  calc ∫⁻ w, speaker α C (L.map q) Measure.dirac (q w) {u} ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono fun w ↦ (measure_mono (Set.subset_univ _)).trans
          (speaker_apply_univ_le_one ..)
    _ = μ Set.univ := by rw [lintegral_one]

omit [Fintype W] in
/-- A listener unsure of the question who learns the question and the speaker's answer to it, at
an answer where the speaker can produce the utterance, holds the prior conditioned on them. -/
theorem cond_listener_prod_speaker_map_dirac_preimage {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] [DiscreteMeasurableSpace W] (C : U → ℝ) (L : Kernel U W)
    (μ : Measure W) [IsFiniteMeasure μ] (ν : Measure B) [IsFiniteMeasure ν] (q : B → W → X) {u : U}
    {b : B} {x : X} (h : speaker α C (L.map (q b)) Measure.dirac x {u} ≠ 0) :
    (listener (μ.prod ν) (fun p ↦ speaker α C (L.map (q p.2)) Measure.dirac (q p.2 p.1)) u)[|
        (q b ⁻¹' {x}) ×ˢ {b}] = (μ.prod ν)[|(q b ⁻¹' {x}) ×ˢ {b}] := by
  refine cond_listener_apply (MeasurableSet.of_discrete.prod (measurableSet_singleton b)) h
    (measure_ne_top _ _) (fun p hp ↦ ?_)
    (ne_top_of_le_ne_top (measure_ne_top (μ.prod ν) Set.univ) ?_)
  · obtain ⟨hx, rfl⟩ : q b p.1 = x ∧ p.2 = b := hp
    rw [hx]
  · calc ∫⁻ p, speaker α C (L.map (q p.2)) Measure.dirac (q p.2 p.1) {u} ∂μ.prod ν
        ≤ ∫⁻ _, 1 ∂μ.prod ν := lintegral_mono fun p ↦
          (measure_mono (Set.subset_univ _)).trans (speaker_apply_univ_le_one ..)
      _ = (μ.prod ν) Set.univ := by rw [lintegral_one]

/-! ### Utterances that name a coordinate -/

/-- At a prior that composes a prior over the coordinate named with a kernel to the rest, the
literal listener of an utterance that names a value of positive prior believes that value and the
kernel there, whatever the prior over the coordinate. -/
theorem listener_truthful_preimage_fst_compProd {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] [Countable A]
    (π : Measure A) [IsFiniteMeasure π] (κ : Kernel A B) [IsMarkovKernel κ] {a : A}
    (ha : π {a} ≠ 0) :
    listener (π ⊗ₘ κ) (truthful fun a : A ↦ (Prod.fst ⁻¹' {a} : Set (A × B))) a =
      Measure.dirac a ⊗ₘ κ := by
  rw [listener_truthful_apply' (π ⊗ₘ κ) _ a (measurable_fst (measurableSet_singleton a))]
  exact Measure.cond_preimage_fst_singleton_compProd π κ ha (measure_ne_top _ _)

end RSA
