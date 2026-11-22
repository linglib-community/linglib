module

public import Linglib.Pragmatics.Agent.Basic
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Posterior

/-!
# Signaling games

A signaling game has states `S`, signals `M` and actions `A`. A state is drawn from a prior, the
sender sees it and gives a signal, and the receiver, who sees only the signal, acts. The sender's
utility depends on the state, her signal and the action, and the receiver's on the state and the
action. A sender is a kernel from states to signals and a receiver a kernel from signals to
actions, and the value of the game to either player is the expectation of her utility,
`SignalingGame.senderValue` and `SignalingGame.receiverValue`.

Each player is an agent. Against a sender, the receiver believes the posterior of the prior given
the signal (`SignalingGame.receiver`), and against a receiver the sender, who knows the state,
values a signal at the expected utility of the action it brings (`SignalingGame.sender`).

The game is of common interest when the two utilities agree. In the guessing game the actions are
the states and both players gain `1` when the action is the state.

## Layout of the directory

* `Defs`: the game, the values, the players as agents.
* `Basic`: expected success in the guessing game.
* `Pure`: pure strategies and the profile of a sender with a receiver.
* `SignalingSystem`: the pure profiles in which the receiver's response is the preferred one.
* `Symmetry`: relabelling of signals.
* `BestResponse`, `Equilibrium`: best responses and the equilibria they define.
* `Information`: a sender as an experiment.
* `Dynamics/`: the replicator dynamic and iterated response.

## TODO

* State `SignalingGame.success` and its lemmas as the value of the guessing game.
* Games with a literal meaning for the signals, which [franke-2011] and [jaeger-2014] both define.

## References

* [lewis-1969]
* [franke-2011]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- A signaling game: a prior over the states, the sender's utility of a signal and an action at a
state, and the receiver's utility of an action at a state. -/
structure SignalingGame (S M A : Type*) [MeasurableSpace S] where
  /-- The prior over the states. -/
  prior : Measure S
  /-- What a signal and the action it brings are worth to the sender at a state. -/
  senderUtility : S → M → A → ℝ
  /-- What an action is worth to the receiver at a state. -/
  receiverUtility : S → A → ℝ

namespace SignalingGame

variable {S M A : Type*} [MeasurableSpace S] [MeasurableSpace M] [MeasurableSpace A]
  (G : SignalingGame S M A)

/-- The value of the game to the sender: her expected utility when she plays `σ` and the receiver
plays `ρ`. -/
noncomputable def senderValue (σ : Kernel S M) (ρ : Kernel M A) : ℝ :=
  ∫ s, ∫ m, ∫ a, G.senderUtility s m a ∂ρ m ∂σ s ∂G.prior

/-- The value of the game to the receiver: his expected utility when the sender plays `σ` and he
plays `ρ`. -/
noncomputable def receiverValue (σ : Kernel S M) (ρ : Kernel M A) : ℝ :=
  ∫ s, ∫ a, G.receiverUtility s a ∂(ρ ∘ₖ σ) s ∂G.prior

/-- A game is of common interest when the sender's utility is the receiver's. -/
def IsCommonInterest : Prop := ∀ s m a, G.senderUtility s m a = G.receiverUtility s a

/-- In a game of common interest the two players value every pair of strategies alike. -/
theorem IsCommonInterest.senderValue_eq [Fintype M] [MeasurableSingletonClass M] [Fintype A]
    [MeasurableSingletonClass A] (h : G.IsCommonInterest) (σ : Kernel S M) [IsFiniteKernel σ]
    (ρ : Kernel M A) [IsFiniteKernel ρ] : G.senderValue σ ρ = G.receiverValue σ ρ := by
  unfold senderValue receiverValue
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  simp only [show ∀ m a, G.senderUtility s m a = G.receiverUtility s a from h s]
  rw [Kernel.integral_comp .of_finite]

/-- Against the receiver `ρ`, the sender is an agent who knows the state and values a signal at
the expected utility of the action it brings. -/
noncomputable def sender (ρ : Kernel M A) : Agent S S M :=
  ⟨Kernel.id, fun s m ↦ ∫ a, G.senderUtility s m a ∂ρ m⟩

/-- Against the sender `σ`, the receiver is an agent who believes the posterior of the prior given
the signal. -/
noncomputable def receiver [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure G.prior]
    (σ : Kernel S M) [IsFiniteKernel σ] : Agent M S A :=
  ⟨σ†G.prior, G.receiverUtility⟩

/-- The guessing game at a prior: the actions are the states, and both players gain `1` when the
action is the state. -/
noncomputable def guess (pr : Measure S) : SignalingGame S M S :=
  ⟨pr, fun s _ ↦ ({s} : Set S).indicator 1, fun s ↦ ({s} : Set S).indicator 1⟩

omit [MeasurableSpace M] in
instance (pr : Measure S) [IsFiniteMeasure pr] :
    IsFiniteMeasure (guess pr : SignalingGame S M S).prior :=
  ‹_›

omit [MeasurableSpace M] in
theorem isCommonInterest_guess (pr : Measure S) :
    (guess pr : SignalingGame S M S).IsCommonInterest :=
  fun _ _ _ ↦ rfl

end SignalingGame
