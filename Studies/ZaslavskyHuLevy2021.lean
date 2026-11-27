module

public import Linglib.Pragmatics.Probabilistic.AlternatingMaximization
public import Linglib.Pragmatics.SignalingGame.SignalingSystem

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

With as many utterances as meanings, a uniform prior and no cost, the tradeoff is at most
$\max\{(1-\alpha)\log K, 0\}$ for $K$ meanings. Up to $\alpha = 1$ the speaker who draws her
utterance uniformly, whatever the meaning, is optimal
(`ZaslavskyHuLevy2021.isMaxOn_freeEnergy_const`), and from $\alpha = 1$ on so is every speaker who
names each meaning by an utterance of its own, the communicator of a signaling system of
[lewis-1969] (`ZaslavskyHuLevy2021.isMaxOn_freeEnergy_signalingSystem`).

## Implementation notes

* The paper's speaker knows the meaning, so its tradeoff is `RSA.freeEnergy` at the identity
  observation kernel, which `RSA.freeEnergy_id` writes as the paper does, and its speaker believes
  the point mass. The two maximality statements are cases of the ones in the
  alternating-maximization file, which also gives the speaker's gap: a speaker falls short of
  the RSA speaker by her expected divergence from it.
* The lexicon is respected at a positive rationality. At rationality zero the speaker is uniform
  over all utterances, whatever the lexicon.
* `listener t` is the paper's listener of depth `t`, and the speaker who answers it is the
  paper's speaker of depth `t + 1`. The recursion assumes a prior that charges every meaning and
  a finite lexicon in which every meaning has an applicable utterance, so that every speaker is
  a probability kernel. A listener is the zero measure at an utterance that applies to no
  meaning. The lexicon is any such weight and the cost any real function, where the paper's
  lexicon has values in the unit interval and its cost is nonnegative.
* Equation numbers are those of the arXiv preprint 2005.06641v1. The two-page proceedings
  abstract numbers its equations differently and leaves out the proofs.

## TODO

* The fixed points of the recursion are stationary points of the tradeoff. Whether the speakers
  and listeners of the recursion converge, and to what, is not settled here.
* The rate–distortion variant, whose tradeoff has mutual information in place of the conditional
  entropy, with its update equations.
* The full sets of optimal speakers: for `α < 1` only the uniform speaker, for `α > 1` only the
  signaling systems, and at `α = 1` the speakers whose utterance is uniformly distributed.
* The first critical value of `α` when the cost is not constant, and the rate–distortion
  counterpart of the bound.

## References

* [zaslavsky-hu-levy-2021]
* [frank-goodman-2012]
* [lewis-1969]
-/

@[expose] public section

namespace ZaslavskyHuLevy2021

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

variable {M U : Type*} [MeasurableSpace M] [MeasurableSpace U] [Fintype M] [Fintype U]
  [MeasurableSingletonClass M] [MeasurableSingletonClass U] (P : Measure M) (C : U → ℝ) (α : ℝ)

/-! ### The two steps -/

/-- Against a fixed listener the RSA speaker maximizes the tradeoff over all speakers (7). -/
theorem freeEnergy_le_freeEnergy_speaker [Nonempty M] [IsFiniteMeasure P] {α : ℝ} (hα : 0 ≤ α)
    (S : Kernel M U) [IsMarkovKernel S] (L : Kernel U M)
    [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    RSA.freeEnergy P Kernel.id C α S L ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C L Measure.dirac) L :=
  RSA.freeEnergy_le_freeEnergy_speaker (ProbabilityTheory.dirac_ae_eq_posterior_id P) hα S L

section Listener

variable [Nonempty M] [IsFiniteMeasure P] (S : Kernel M U) [IsFiniteKernel S] (L : Kernel U M)
  [∀ u, IsZeroOrProbabilityMeasure (L u)]

-- (12)
theorem expectedUtility_le_listener :
    RSA.expectedUtility P S L C ≤ RSA.expectedUtility P S (RSA.listener P S) C :=
  RSA.expectedUtility_le_listener P S L C

/-- Against a fixed speaker her Bayesian listener maximizes the tradeoff over all listeners
(8). -/
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

-- (9)
-- Each listener update raises the tradeoff, the first inequality of (9).
theorem freeEnergy_le_freeEnergy_listener_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l t) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) := by
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  rw [listener_succ]
  exact RSA.freeEnergy_le_freeEnergy_listener P Kernel.id C hα _ _

-- (9)
-- Each speaker update raises the tradeoff, the second inequality of (9).
theorem freeEnergy_le_freeEnergy_speaker_succ (t : ℕ) :
    RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l t) Measure.dirac)
        (listener P C α l (t + 1)) ≤
      RSA.freeEnergy P Kernel.id C α (RSA.speaker α C (listener P C α l (t + 1)) Measure.dirac)
        (listener P C α l (t + 1)) :=
  have := isMarkovKernel_speaker_listener (C := C) hP hl hα hm t
  RSA.freeEnergy_le_freeEnergy_speaker (ProbabilityTheory.dirac_ae_eq_posterior_id P) hα _ _

/-- The tradeoff converges along the recursion to a real number, being monotone, bounded above
and nowhere `−∞`. -/
theorem exists_tendsto_freeEnergy : ∃ g : ℝ, Tendsto (fun t ↦ RSA.freeEnergy P Kernel.id C α
    (RSA.speaker α C (listener P C α l t) Measure.dirac) (listener P C α l t)) atTop (𝓝 g) :=
  have : IsMarkovKernel (RSA.speaker α C (Kernel.ofDensity P l) Measure.dirac) :=
    isMarkovKernel_speaker_listener (C := C) hP hl hα hm 0
  RSA.exists_tendsto_freeEnergy_iterate_recurse (ProbabilityTheory.dirac_ae_eq_posterior_id P) hα
    (fun o ↦ by rw [Measure.id_comp]; exact hP o) (Kernel.ofDensity P l)

end Recursion

/-! ### Asymptotic behaviour and the criticality of `α = 1` -/

section Criticality

open InformationTheory

variable [Nonempty M]

-- Proposition 3, against the Bayesian listener.
theorem freeEnergy_listener_le_max (hcard : Fintype.card U = Fintype.card M) (α : ℝ)
    (S : Kernel M U) [IsMarkovKernel S] :
    RSA.freeEnergy (uniformOn Set.univ) Kernel.id (0 : U → ℝ) α S
        (RSA.listener (uniformOn Set.univ) S) ≤
      ((max ((1 - α) * log (Fintype.card M)) 0 : ℝ) : EReal) := by
  have hI0 : 0 ≤ Im[(uniformOn Set.univ : Measure M) ⊗ₘ S] := measureMutualInfo_nonneg _
  have hIK : Im[(uniformOn Set.univ : Measure M) ⊗ₘ S] ≤ log (Fintype.card M) := by
    rw [← hcard]
    exact measureMutualInfo_compProd_le_log_card S _
  have hU : Hm[S ∘ₘ (uniformOn Set.univ : Measure M)] ≤ log (Fintype.card M) := by
    rw [← hcard]
    exact measureEntropy_le_log_card _
  rw [RSA.freeEnergy_id_listener, EReal.coe_le_coe_iff,
    (measureEntropy_eq_log_card_iff (uniformOn (Set.univ : Set M))).2 rfl]
  simp only [Pi.zero_apply, integral_zero, mul_zero, sub_zero]
  rcases le_total α 1 with h | h
  · exact le_max_of_le_left (by nlinarith [mul_nonneg (sub_nonneg.2 h) hI0])
  · exact le_max_of_le_right (by nlinarith [mul_le_mul_of_nonneg_left hIK (sub_nonneg.2 h)])

-- Proposition 3: no speaker and listener exceed `max ((1 - α) * log K) 0`.
theorem freeEnergy_le_max (hcard : Fintype.card U = Fintype.card M) {α : ℝ} (hα : 0 ≤ α)
    (S : Kernel M U) [IsMarkovKernel S] (L : Kernel U M) [∀ u, IsZeroOrProbabilityMeasure (L u)] :
    RSA.freeEnergy (uniformOn Set.univ) Kernel.id (0 : U → ℝ) α S L ≤
      ((max ((1 - α) * log (Fintype.card M)) 0 : ℝ) : EReal) := by
  have hL := RSA.freeEnergy_le_freeEnergy_listener (uniformOn Set.univ) Kernel.id (0 : U → ℝ) hα S L
  rw [Kernel.comp_id] at hL
  exact hL.trans (freeEnergy_listener_le_max hcard α S)

-- Proposition 3: the uniform speaker attains `(1 - α) * log K`.
theorem freeEnergy_const_uniformOn [Nonempty U] (hcard : Fintype.card U = Fintype.card M)
    (α : ℝ) :
    RSA.freeEnergy (uniformOn Set.univ) Kernel.id (0 : U → ℝ) α
        (Kernel.const M (uniformOn Set.univ))
        (RSA.listener (uniformOn Set.univ) (Kernel.const M (uniformOn Set.univ))) =
      (((1 - α) * log (Fintype.card M) : ℝ) : EReal) := by
  rw [RSA.freeEnergy_id_listener_const,
    (measureEntropy_eq_log_card_iff (uniformOn (Set.univ : Set M))).2 rfl,
    (measureEntropy_eq_log_card_iff (uniformOn (Set.univ : Set U))).2 rfl, hcard]
  congr 1
  simp only [Pi.zero_apply, integral_zero, mul_zero, sub_zero]
  ring

-- Proposition 3: the communicator of a signaling system attains `0`, at every prior.
theorem freeEnergy_signalingSystem {R : Type*} {F : M ≃ R} [IsProbabilityMeasure P]
    (A : SignalingSystem F U) (α : ℝ) :
    RSA.freeEnergy P Kernel.id (0 : U → ℝ) α (Kernel.deterministic A.communicator .of_discrete)
        (RSA.listener P (Kernel.deterministic A.communicator .of_discrete)) = 0 := by
  rw [RSA.freeEnergy_id_listener_deterministic _ _ _ A.communicator_injective]
  simp

/-- Proposition 3: up to `α = 1`, the speaker who draws her utterance uniformly, whatever the
meaning, is optimal against her Bayesian listener. -/
theorem isMaxOn_freeEnergy_const [Nonempty U] (hcard : Fintype.card U = Fintype.card M) {α : ℝ}
    (hα : α ≤ 1) :
    IsMaxOn (fun S : Kernel M U ↦ RSA.freeEnergy (uniformOn Set.univ) Kernel.id (0 : U → ℝ) α S
      (RSA.listener (uniformOn Set.univ) S)) {S | IsMarkovKernel S}
      (Kernel.const M (uniformOn Set.univ)) := fun S (hS : IsMarkovKernel S) ↦ by
  dsimp only
  rw [freeEnergy_const_uniformOn hcard]
  exact (freeEnergy_listener_le_max hcard α S).trans (EReal.coe_le_coe_iff.2
    (max_le le_rfl (mul_nonneg (sub_nonneg.2 hα) (log_natCast_nonneg _))))

/-- Proposition 3: from `α = 1` on, the communicator of any signaling system of [lewis-1969] is
optimal against her Bayesian listener. -/
theorem isMaxOn_freeEnergy_signalingSystem {R : Type*} {F : M ≃ R}
    (hcard : Fintype.card U = Fintype.card M) {α : ℝ} (hα : 1 ≤ α) (A : SignalingSystem F U) :
    IsMaxOn (fun S : Kernel M U ↦ RSA.freeEnergy (uniformOn Set.univ) Kernel.id (0 : U → ℝ) α S
      (RSA.listener (uniformOn Set.univ) S)) {S | IsMarkovKernel S}
      (Kernel.deterministic A.communicator .of_discrete) := fun S (hS : IsMarkovKernel S) ↦ by
  dsimp only
  rw [freeEnergy_signalingSystem]
  exact (freeEnergy_listener_le_max hcard α S).trans (EReal.coe_le_coe_iff.2
    (max_le (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hα) (log_natCast_nonneg _)) le_rfl))

end Criticality

end ZaslavskyHuLevy2021
