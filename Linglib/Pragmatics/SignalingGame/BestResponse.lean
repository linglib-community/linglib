module

public import Linglib.Pragmatics.Agent.BestResponse
public import Linglib.Pragmatics.SignalingGame.Defs

/-!
# Best responses in a signaling game

The receiver's best responses to a sender are the best responses of the agent who believes the
posterior of the prior given the signal, and the sender's best responses to a receiver those of
the agent who knows the state and values a signal at the expected utility of the action it
brings. In the guessing game the receiver's best responses are the most probable states of the
posterior (`SignalingGame.mem_receiverBestResponses_guess_iff`).

## TODO

* A pair of pure strategies is a `SignalingGame.IsEquilibrium` of the values exactly when each is
  a best response to the other at every state and signal that occurs.
* The optimal actions of [jaeger-2014] as the receiver's best responses.
* Perfect Bayesian equilibrium, with a belief at the signals that do not occur.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SignalingGame

variable {S M A : Type*} [MeasurableSpace S] [MeasurableSpace M] [MeasurableSpace A]
  (G : SignalingGame S M A)

/-- The signals that are best for the sender at a state, against the receiver `ρ`. -/
noncomputable def senderBestResponses (ρ : Kernel M A) (s : S) : Set M :=
  (G.sender ρ).bestResponses s

/-- The actions that are best for the receiver at a signal, against the sender `σ`. -/
noncomputable def receiverBestResponses [StandardBorelSpace S] [Nonempty S]
    [IsFiniteMeasure G.prior] (σ : Kernel S M) [IsFiniteKernel σ] (m : M) : Set A :=
  (G.receiver σ).bestResponses m

section Guess

variable [StandardBorelSpace S] [Nonempty S] [MeasurableSingletonClass S] (pr : Measure S)
  [IsFiniteMeasure pr] (σ : Kernel S M) [IsFiniteKernel σ] {m : M} {s : S}

/-- In the guessing game the receiver values a guess at its posterior probability. -/
theorem guess_receiver_value (m : M) (s : S) :
    ((guess pr : SignalingGame S M S).receiver σ).value m s = ((σ†pr) m).real {s} := by
  have h : (fun t ↦ ({t} : Set S).indicator (1 : S → ℝ) s) = ({s} : Set S).indicator 1 := by
    ext t
    by_cases h : t = s
    · simp [h]
    · simp only [Set.indicator, Set.mem_singleton_iff, h, ite_false, ite_eq_right_iff]
      exact fun h' ↦ absurd h'.symm h
  change ∫ t, ({t} : Set S).indicator (1 : S → ℝ) s ∂(σ†pr) m = _
  rw [h, integral_indicator_one (.singleton s)]

/-- In the guessing game the receiver's best responses to a sender are the most probable states
of the posterior. -/
theorem mem_receiverBestResponses_guess_iff :
    s ∈ (guess pr : SignalingGame S M S).receiverBestResponses σ m ↔
      ∀ t, ((σ†pr) m).real {t} ≤ ((σ†pr) m).real {s} := by
  simp only [receiverBestResponses, Agent.bestResponses, Set.mem_ofPred_eq, guess_receiver_value]

end Guess

end SignalingGame
