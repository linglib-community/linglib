module

public import Linglib.Pragmatics.RSA.AlternatingMaximization

/-!
# Zaslavsky, Hu and Levy (2021): A Rate–Distortion View of Human Pragmatic Reasoning?

Zaslavsky, Hu and Levy show that the Rational Speech Act recursion is an alternating maximization.
A reference game has finitely many meanings and utterances, a prior over the meanings, a lexicon
and a cost on the utterances. A speaker is a kernel from meanings to utterances and a listener a
kernel back. The tradeoff of a speaker and a listener is the speaker's conditional entropy plus
`α` times the expected utility, the listener's log-probability of the speaker's meaning less the
cost of her utterance, which is `−∞` when the listener rules out a meaning the speaker conveys.
Among all speakers the RSA speaker
[maximizes](##ZaslavskyHuLevy2021.freeEnergy_le_freeEnergy_speaker) the tradeoff against a fixed
listener, and among all listeners the Bayesian listener
[does](##ZaslavskyHuLevy2021.freeEnergy_le_freeEnergy_listener) against a fixed speaker, so the
tradeoff never decreases along the recursion and
[converges](##ZaslavskyHuLevy2021.exists_tendsto_freeEnergy).

## Implementation notes

* The paper's speaker knows the meaning, so its tradeoff is `RSA.freeEnergy` at the identity
  observation kernel, which `RSA.freeEnergy_id` writes as the paper does, and its speaker believes
  the point mass. The two maximality statements are cases of the ones in the
  alternating-maximization file, which also give the gap: a speaker falls short of the RSA
  speaker, and a listener of the Bayesian listener, by an expected divergence from it.
* `listener t` is the paper's listener of depth `t`, and the speaker who answers it is the
  paper's speaker of depth `t + 1`. The recursion assumes a prior that charges every meaning and
  a finite lexicon in which every meaning has an applicable utterance, so that every speaker is
  a probability kernel. A listener's row is zero at an utterance that applies to no meaning. The
  lexicon is any such weight and the cost any real function, where the paper's lexicon has
  values in the unit interval and its cost is nonnegative.
* Equation numbers are those of the arXiv preprint 2005.06641v1. The two-page proceedings
  abstract numbers its equations differently and leaves out the proofs.

## TODO

* The fixed points of the recursion are stationary points of the tradeoff, and the limit of the
  tradeoff along the recursion is its value at one.
* The rate–distortion variant, whose tradeoff has mutual information in place of the conditional
  entropy, with its update equations.
* The asymptotic behaviour of the recursion and the criticality of `α = 1`.

## References

* [zaslavsky-hu-levy-2021]
* [frank-goodman-2012]
-/

@[expose] public section

namespace ZaslavskyHuLevy2021

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

variable {M U : Type*} [MeasurableSpace M] [MeasurableSpace U] [Fintype M] [Fintype U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] (P : Measure M) (C : U → ℝ) (α : ℝ)

/-! ### The two steps -/

/-- Against a fixed listener the RSA speaker maximizes the tradeoff (7) over all speakers. -/
theorem freeEnergy_le_freeEnergy_speaker [Nonempty M] [IsFiniteMeasure P] {α : ℝ} (hα : 0 ≤ α)
    (S : Kernel M U) [IsMarkovKernel S] (L : Kernel U M)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    RSA.freeEnergy P Kernel.id C α S L ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C L Measure.dirac) L :=
  RSA.freeEnergy_le_freeEnergy_speaker (RSA.dirac_ae_eq_posterior_id P) hα S L

section Listener

variable [Nonempty M] [IsFiniteMeasure P] (S : Kernel M U) [IsFiniteKernel S] (L : Kernel U M)
  [∀ u, IsZeroOrProbabilityMeasure (L u)]

-- (12)
theorem expectedUtility_le_listener :
    RSA.expectedUtility P S L C ≤ RSA.expectedUtility P S (RSA.listener P S) C :=
  RSA.expectedUtility_le_listener P S L C

/-- Against a fixed speaker her Bayesian listener maximizes the tradeoff (8) over all
listeners. -/
theorem freeEnergy_le_freeEnergy_listener {α : ℝ} (hα : 0 ≤ α) :
    RSA.freeEnergy P Kernel.id C α S L ≤ RSA.freeEnergy P Kernel.id C α S (RSA.listener P S) := by
  simpa only [Kernel.comp_id] using RSA.freeEnergy_le_freeEnergy_listener P Kernel.id C hα S L

end Listener

/-! ### The recursion -/

section Recursion

variable (l : U → M → ℝ≥0∞)

/-- The listeners of the recursion (3) start from the literal listener
`L₀(m | u) ∝ l(m, u) P(m)`, and each later one is the listener of the speaker (2) who answers
the one before. -/
noncomputable abbrev listener (t : ℕ) : Kernel U M :=
  (RSA.recurse P Kernel.id Measure.dirac α C)^[t] (Kernel.ofDensity P l)

theorem listener_succ (t : ℕ) : listener P C α l (t + 1) =
    RSA.recurse P Kernel.id Measure.dirac α C (listener P C α l t) :=
  Function.iterate_succ_apply' _ _ _

variable {P C α l} {u : U} {m : M}

theorem listener_apply_singleton_eq_zero (hα : 0 < α) (h : l u m = 0) (t : ℕ) :
    listener P C α l t u {m} = 0 :=
  RSA.iterate_recurse_id_dirac_apply_singleton_eq_zero hα (by
    rw [Kernel.ofDensity_apply_singleton, h, zero_mul, ENNReal.zero_div]) t

theorem speaker_listener_apply_singleton_eq_zero (hα : 0 < α) (h : l u m = 0) (t : ℕ) :
    RSA.speaker α C (listener P C α l t) Measure.dirac m {u} = 0 :=
  RSA.speaker_dirac_apply_singleton_eq_zero hα (listener_apply_singleton_eq_zero hα h t)

section Support

variable [IsFiniteMeasure P] (hP : ∀ m, P {m} ≠ 0) (hl : ∀ u m, l u m ≠ ∞) (hα : 0 ≤ α)
include hP hl hα

theorem listener_apply_singleton_ne_zero (h : l u m ≠ 0) (t : ℕ) :
    listener P C α l t u {m} ≠ 0 := by
  refine RSA.iterate_recurse_id_dirac_apply_singleton_ne_zero hα (hP m) ?_ t
  rw [Kernel.ofDensity_apply_singleton]
  exact ENNReal.div_ne_zero.2 ⟨mul_ne_zero h (hP m), ENNReal.sum_ne_top.2 fun m' _ ↦
    ENNReal.mul_ne_top (hl u m') (measure_ne_top _ _)⟩

theorem isMarkovKernel_speaker_listener (hm : ∀ m, ∃ u, l u m ≠ 0) (t : ℕ) :
    IsMarkovKernel (RSA.speaker α C (listener P C α l t) Measure.dirac) :=
  RSA.isMarkovKernel_speaker_dirac hα C _ fun m ↦
    (hm m).imp fun _ h ↦ listener_apply_singleton_ne_zero hP hl hα h t

end Support

variable [IsProbabilityMeasure P] [Nonempty M] (hP : ∀ m, P {m} ≠ 0) (hl : ∀ u m, l u m ≠ ∞)
  (hα : 0 ≤ α) (hm : ∀ m, ∃ u, l u m ≠ 0)
include hP hl hα hm

/-- Each listener update raises the tradeoff, the first inequality of (9). -/
theorem freeEnergy_le_freeEnergy_listener_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l t) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  rw [listener_succ]
  exact RSA.freeEnergy_le_freeEnergy_listener P Kernel.id C hα _ _

/-- Each speaker update raises the tradeoff, the second inequality of (9). -/
theorem freeEnergy_le_freeEnergy_speaker_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l (t + 1)) Measure.dirac)
        (listener P C α l (t + 1)) :=
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  RSA.freeEnergy_le_freeEnergy_speaker (RSA.dirac_ae_eq_posterior_id P) hα _ _

/-- The tradeoff converges along the recursion to a real number, being monotone, bounded above
and nowhere `−∞`. -/
theorem exists_tendsto_freeEnergy : ∃ g : ℝ, Tendsto (fun t ↦ RSA.freeEnergy P Kernel.id C α
    (RSA.speaker α C (listener P C α l t) Measure.dirac) (listener P C α l t)) atTop (𝓝 g) :=
  have : IsMarkovKernel (RSA.speaker α C (Kernel.ofDensity P l) Measure.dirac) :=
    isMarkovKernel_speaker_listener (C := C) hP hl hα hm 0
  RSA.exists_tendsto_freeEnergy_iterate_recurse (RSA.dirac_ae_eq_posterior_id P) hα
    (fun o ↦ by rw [Measure.id_comp]; exact hP o) (Kernel.ofDensity P l)

end Recursion

end ZaslavskyHuLevy2021
