module

public import Linglib.Pragmatics.RSA.AlternatingMaximization

/-!
# Zaslavsky, Hu and Levy (2021): A Rate–Distortion View of Human Pragmatic Reasoning?

Zaslavsky, Hu and Levy show that the Rational Speech Act recursion is an alternating maximization.
A reference game has finitely many meanings and utterances, a prior over the meanings, a lexicon
and a cost on the utterances. A speaker is a kernel from meanings to utterances and a listener a
kernel back. The tradeoff of a speaker and a listener is the speaker's conditional entropy plus
`α` times the expected utility, the listener's log-probability of the speaker's meaning less the
cost of her utterance. Against a fixed listener the RSA speaker maximizes the tradeoff, and
against a fixed speaker the Bayesian listener does, so the tradeoff never decreases along the
recursion.

## Main statements

* `freeEnergy_le_freeEnergy_speaker`, `freeEnergy_le_freeEnergy_listener`: against a fixed
  listener the RSA speaker maximizes the tradeoff, and against a fixed speaker the Bayesian
  listener does.
* `freeEnergy_le_freeEnergy_listener_succ`, `freeEnergy_le_freeEnergy_speaker_succ`,
  `exists_tendsto_freeEnergy`: along the recursion each listener update and each speaker update
  raises the tradeoff, which therefore converges.
* `listener_apply_singleton_eq_zero`, `speaker_listener_apply_singleton_eq_zero`: no agent of the
  recursion pairs an utterance with a meaning the lexicon rules out for it.

## Implementation notes

* The paper's speaker knows the meaning, so its tradeoff is `RSA.freeEnergy` at the identity
  observation kernel, which `RSA.freeEnergy_id` writes as the paper does, and its speaker believes
  the point mass. The two maximality statements are cases of the ones in the
  alternating-maximization file, whose notes say how the real-valued utility there relates to the
  paper's.
* `listener t` is the paper's listener of depth `t`, and the speaker who answers it is the
  paper's speaker of depth `t + 1`. The recursion assumes a prior that charges every meaning and
  a finite lexicon in which every meaning has an applicable utterance, so that every speaker is
  a probability kernel. A listener's row is zero at an utterance that applies to no meaning. The
  lexicon is any such weight and the cost any real function, where the paper's lexicon has
  values in the unit interval and its cost is nonnegative.
* The lexicon statements need `0 < α`, where the paper has `0 ≤ α`. At `α = 0` the speaker
  here is uniform over all the utterances, since `0 ^ 0 = 1`.

## TODO

* The fixed points of the recursion are stationary points of the tradeoff, and the limit of the
  tradeoff along the recursion is its value at one.
* The rate–distortion variant, whose tradeoff has mutual information in place of the conditional
  entropy, with its update equations.
* The asymptotic behaviour of the recursion and the criticality of `α = 1`.

## References

* [zaslavsky-hu-levy-2020]
* [frank-goodman-2012]
-/

@[expose] public section

namespace ZaslavskyHuLevy2021

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

variable {M U : Type*} [MeasurableSpace M] [MeasurableSpace U] [Fintype M] [Fintype U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] (P : Measure M) (C : U → ℝ) (α : ℝ)

/-! ### The two steps -/

/-- Against a fixed listener the RSA speaker maximizes the tradeoff (7). -/
theorem freeEnergy_le_freeEnergy_speaker [IsFiniteMeasure P] {α : ℝ} (hα : 0 ≤ α) (L : Kernel U M)
    [IsFiniteKernel L] (S : Kernel M U) [IsMarkovKernel S]
    (hS : ∀ m, P {m} ≠ 0 → S m ≪ RSA.speaker α C L Measure.dirac m) :
    RSA.freeEnergy P Kernel.id C α S L ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C L Measure.dirac) L :=
  RSA.freeEnergy_le_freeEnergy_speaker (RSA.id_comp_real_mul_dirac_real P) hα L S
    (by simpa only [Measure.id_comp] using hS)

section Listener

variable [Nonempty M] [IsProbabilityMeasure P] (S : Kernel M U) [IsMarkovKernel S]
  (L : Kernel U M) [∀ u, IsZeroOrProbabilityMeasure (L u)]
  (hL : ∀ u, (S ∘ₘ P) {u} ≠ 0 → RSA.listener P S u ≪ L u)
include hL

-- (12)
theorem expectedUtility_le_listener :
    RSA.expectedUtility P Kernel.id C S L ≤
      RSA.expectedUtility P Kernel.id C S (RSA.listener P S) := by
  have h := RSA.expectedUtility_le_listener P Kernel.id C S L
    (by simpa only [Kernel.comp_id] using hL)
  simp only [Kernel.comp_id] at h
  exact h

/-- Against a fixed speaker her Bayesian listener maximizes the tradeoff (8). -/
theorem freeEnergy_le_freeEnergy_listener (hα : 0 ≤ α) :
    RSA.freeEnergy P Kernel.id C α S L ≤ RSA.freeEnergy P Kernel.id C α S (RSA.listener P S) := by
  have h := RSA.freeEnergy_le_freeEnergy_listener P Kernel.id C α S L
    (by simpa only [Kernel.comp_id] using hL) hα
  simp only [Kernel.comp_id] at h
  exact h

end Listener

/-! ### The recursion -/

section Recursion

variable (l : U → M → ℝ≥0∞)

/-- The listeners of the recursion (3) start from the literal listener
`L₀(m | u) ∝ l(m, u) P(m)`, and each later one is the listener of the speaker (2) who answers
the one before. -/
noncomputable def listener : ℕ → Kernel U M
  | 0 => Kernel.ofDensity P l
  | t + 1 => RSA.listener P (RSA.speaker α C (listener t) Measure.dirac)

instance : ∀ t, IsFiniteKernel (listener P C α l t)
  | 0 => inferInstanceAs (IsFiniteKernel (Kernel.ofDensity P l))
  | _ + 1 => inferInstanceAs (IsFiniteKernel (RSA.listener P _))

instance : ∀ t u, IsZeroOrProbabilityMeasure (listener P C α l t u)
  | 0, u => inferInstanceAs (IsZeroOrProbabilityMeasure (Kernel.ofDensity P l u))
  | _ + 1, u => inferInstanceAs (IsZeroOrProbabilityMeasure (RSA.listener P _ u))

variable {P C α l} {u : U} {m : M}

/-- The listeners of the recursion respect the lexicon. An utterance never leads the listener to
a meaning it does not apply to. -/
theorem listener_apply_singleton_eq_zero (hα : 0 < α) (h : l u m = 0) :
    ∀ t, listener P C α l t u {m} = 0
  | 0 => by rw [listener, Kernel.ofDensity_apply_singleton, h, zero_mul, ENNReal.zero_div]
  | t + 1 => by
    rw [listener]
    exact RSA.listener_apply_singleton_eq_zero
      (RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hα h t))

/-- The speakers of the recursion respect the lexicon. No meaning is expressed by an utterance
that does not apply to it. -/
theorem speaker_listener_apply_singleton_eq_zero (hα : 0 < α) (h : l u m = 0) (t : ℕ) :
    RSA.speaker α C (listener P C α l t) Measure.dirac m {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hα h t)

section Support

variable [IsFiniteMeasure P] (hP : ∀ m, P {m} ≠ 0) (hl : ∀ u m, l u m ≠ ∞) (hα : 0 ≤ α)
include hP hl hα

theorem listener_apply_singleton_ne_zero (h : l u m ≠ 0) : ∀ t, listener P C α l t u {m} ≠ 0
  | 0 => by
    rw [listener, Kernel.ofDensity_apply_singleton]
    exact ENNReal.div_ne_zero.2 ⟨mul_ne_zero h (hP m), ENNReal.sum_ne_top.2 fun m' _ ↦
      ENNReal.mul_ne_top (hl u m') (measure_ne_top _ _)⟩
  | t + 1 => by
    rw [listener]
    exact RSA.listener_apply_singleton_ne_zero (hP m)
      (RSA.speaker_dirac_apply_singleton_ne_zero hα (listener_apply_singleton_ne_zero h t))

theorem isMarkovKernel_speaker_listener (hm : ∀ m, ∃ u, l u m ≠ 0) (t : ℕ) :
    IsMarkovKernel (RSA.speaker α C (listener P C α l t) Measure.dirac) :=
  RSA.isMarkovKernel_speaker_dirac hα C _ fun m ↦
    (hm m).imp fun _ h ↦ listener_apply_singleton_ne_zero hP hl hα h t

end Support

variable [IsProbabilityMeasure P] (hP : ∀ m, P {m} ≠ 0) (hl : ∀ u m, l u m ≠ ∞)
  (hα : 0 ≤ α) (hm : ∀ m, ∃ u, l u m ≠ 0)
include hP hl hα hm

/-- Each speaker update raises the tradeoff, the second inequality of (9). -/
theorem freeEnergy_le_freeEnergy_speaker_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l (t + 1)) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  have h := RSA.freeEnergy_listener_le_freeEnergy_speaker (C := C)
    (RSA.id_comp_real_mul_dirac_real P) hα (RSA.speaker α C (listener P C α l t) Measure.dirac)
  simp only [Kernel.comp_id] at h
  exact h

variable [Nonempty M]

/-- Each listener update raises the tradeoff, the first inequality of (9). -/
theorem freeEnergy_le_freeEnergy_listener_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l t) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  have h := RSA.freeEnergy_speaker_le_freeEnergy_listener (C := C)
    (RSA.id_comp_real_mul_dirac_real P) hα (listener P C α l t)
  simp only [Kernel.comp_id] at h
  exact h

/-- The tradeoff converges along the recursion, being monotone and bounded above. -/
theorem exists_tendsto_freeEnergy : ∃ g, Tendsto (fun t ↦ RSA.freeEnergy P Kernel.id C α
    (RSA.speaker α C (listener P C α l t) Measure.dirac) (listener P C α l t)) atTop (𝓝 g) := by
  refine ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ fun t ↦
    (freeEnergy_le_freeEnergy_listener_succ hP hl hα hm t).trans
      (freeEnergy_le_freeEnergy_speaker_succ hP hl hα hm t))
    ⟨log (Fintype.card U) + α * ∑ u, |C u|, ?_⟩⟩
  rintro _ ⟨t, rfl⟩
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  exact RSA.freeEnergy_le P Kernel.id C hα _ _

end Recursion

end ZaslavskyHuLevy2021
