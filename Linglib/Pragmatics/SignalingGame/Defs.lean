module

public import Linglib.Pragmatics.Agent.Basic
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Posterior

/-!
# Signaling games

A signaling game has states `S`, signals `M` and actions `A`. A state is drawn from a prior, the
sender sees it and gives a signal, and the receiver, who sees only the signal, acts. Each player's
utility depends on the state, the signal and the action. A sender is a kernel from states to
signals and a receiver a kernel from signals to actions, and the value of the game to either player
is the expectation of her utility, `SignalingGame.senderValue` and `SignalingGame.receiverValue`.

Each player is an agent. Against a sender, the receiver believes the posterior of the prior given
the signal (`SignalingGame.receiver`), and against a receiver the sender, who knows the state,
values a signal at the expected utility of the action it brings (`SignalingGame.sender`).

The game is of common interest when the two utilities agree, and cheap talk when neither depends
on the signal. In the guessing game the actions are the states and both players gain `1` when the
action is the state.

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

* [osborne-rubinstein-1994]
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
  /-- What a signal and the action it brings are worth to the receiver at a state. -/
  receiverUtility : S → M → A → ℝ

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
  ∫ s, ∫ m, ∫ a, G.receiverUtility s m a ∂ρ m ∂σ s ∂G.prior

/-- A game is of common interest when the sender's utility is the receiver's. -/
def IsCommonInterest : Prop := G.senderUtility = G.receiverUtility

/-- In a game of common interest the two players value every pair of strategies alike. -/
theorem IsCommonInterest.senderValue_eq (h : G.IsCommonInterest) (σ : Kernel S M)
    (ρ : Kernel M A) : G.senderValue σ ρ = G.receiverValue σ ρ := by
  rw [senderValue, receiverValue, h]

/-- A game is cheap talk when neither player's utility depends on which signal is given. -/
structure IsCheapTalk : Prop where
  /-- The sender's utility does not depend on the signal. -/
  senderUtility_eq : ∀ s m m' a, G.senderUtility s m a = G.senderUtility s m' a
  /-- The receiver's utility does not depend on the signal. -/
  receiverUtility_eq : ∀ s m m' a, G.receiverUtility s m a = G.receiverUtility s m' a

/-- Against the receiver `ρ`, the sender is an agent who knows the state and values a signal at
the expected utility of the action it brings. -/
noncomputable def sender (ρ : Kernel M A) : Agent S S M :=
  ⟨Kernel.id, fun s m ↦ ((∫ a, G.senderUtility s m a ∂ρ m : ℝ) : EReal)⟩

instance (ρ : Kernel M A) : (G.sender ρ).IsUnconstrained := by
  unfold sender; infer_instance

section Receiver

variable [StandardBorelSpace S] [Nonempty S] [IsFiniteMeasure G.prior] (σ : Kernel S M)
  [IsFiniteKernel σ]

/-- Against the sender `σ`, the receiver is an agent who knows the signal and believes of the
state the posterior of the prior given it. -/
noncomputable def receiver : Agent M (S × M) A :=
  ⟨(σ†G.prior) ×ₖ Kernel.id, fun p a ↦ ((G.receiverUtility p.1 p.2 a : ℝ) : EReal)⟩

instance : (G.receiver σ).IsUnconstrained := by
  unfold receiver; infer_instance

omit [MeasurableSpace A] in
/-- The receiver values an action at a signal at its expected utility under the posterior. -/
theorem receiver_value [Countable S] [MeasurableSingletonClass S] [Countable M]
    [MeasurableSingletonClass M] (m : M) (a : A) :
    (G.receiver σ).value m a = ∫ s, G.receiverUtility s m a ∂(σ†G.prior) m := by
  rw [receiver, Agent.value_coe, Kernel.prod_apply, Kernel.id_apply, Measure.prod_dirac,
    integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable]

end Receiver

/-- The guessing game at a prior: the actions are the states, and both players gain `1` when the
action is the state. -/
noncomputable def guess (pr : Measure S) : SignalingGame S M S :=
  ⟨pr, fun s _ ↦ ({s} : Set S).indicator 1, fun s _ ↦ ({s} : Set S).indicator 1⟩

omit [MeasurableSpace M] in
instance (pr : Measure S) [IsFiniteMeasure pr] :
    IsFiniteMeasure (guess pr : SignalingGame S M S).prior :=
  ‹_›

omit [MeasurableSpace M] in
theorem isCommonInterest_guess (pr : Measure S) :
    (guess pr : SignalingGame S M S).IsCommonInterest :=
  rfl

omit [MeasurableSpace M] in
theorem isCheapTalk_guess (pr : Measure S) : (guess pr : SignalingGame S M S).IsCheapTalk :=
  ⟨fun _ _ _ _ ↦ rfl, fun _ _ _ _ ↦ rfl⟩

end SignalingGame
