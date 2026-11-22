module

public import Linglib.Pragmatics.Agent.BestResponse
public import Linglib.Pragmatics.SignalingGame.Defs

/-!
# Best responses in a signaling game

The receiver's best responses to a sender are the best responses of the agent who believes the
posterior of the prior given the signal, and the sender's best responses to a receiver those of
the agent who knows the state and values a signal at the expected utility of the action it
brings.

## TODO

* A pair of pure strategies is a `SignalingGame.IsEquilibrium` of the values exactly when each is
  a best response to the other at every state and signal that occurs.
* The receiver's best responses as the most probable states of the posterior in the guessing
  game, which [franke-2011] proves for its receiver, and the optimal actions of [jaeger-2014].
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

end SignalingGame
