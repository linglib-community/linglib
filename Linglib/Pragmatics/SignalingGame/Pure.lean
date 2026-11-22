module

public import Linglib.Pragmatics.SignalingGame.Defs
public import Mathlib.Probability.Kernel.Basic

/-!
# Pure strategies

A pure strategy of the sender is a function from states to signals and one of the receiver a
function from signals to actions. Their values are the expected utilities of the action the
receiver takes on the sender's signal, `SignalingGame.pureSenderValue` and
`SignalingGame.pureReceiverValue`, which are the values of the kernels that follow the two
functions (`SignalingGame.senderValue_deterministic`).

The sender and the receiver are the agents `false` and `true` of a family of strategy types,
`SignalingGame.Strategies`, on which the equilibria of the game are stated.

## TODO

* Port the families of [lewis-1969] and [franke-2011] in their studies to `Strategies`.
* The receiver's value of a pure profile in the guessing game is `success_deterministic`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SignalingGame

universe u

variable {S M A : Type u}

/-- The pure strategies of the sender, `false`, and of the receiver, `true`. -/
abbrev Strategies (S M A : Type u) : Bool → Type u
  | false => S → M
  | true => M → A

/-- The profile in which the sender plays `f` and the receiver `g`. -/
def profile (f : S → M) (g : M → A) : ∀ b, Strategies S M A b
  | false => f
  | true => g

@[simp] theorem profile_false (f : S → M) (g : M → A) : profile f g false = f := rfl

@[simp] theorem profile_true (f : S → M) (g : M → A) : profile f g true = g := rfl

variable [MeasurableSpace S] (G : SignalingGame S M A)

/-- The sender's value of a pure profile. -/
noncomputable def pureSenderValue (f : S → M) (g : M → A) : ℝ :=
  ∫ s, G.senderUtility s (f s) (g (f s)) ∂G.prior

/-- The receiver's value of a pure profile. -/
noncomputable def pureReceiverValue (f : S → M) (g : M → A) : ℝ :=
  ∫ s, G.receiverUtility s (g (f s)) ∂G.prior

variable [MeasurableSpace M] [MeasurableSpace A] [Countable S] [MeasurableSingletonClass S]
  [Countable M] [MeasurableSingletonClass M] [MeasurableSingletonClass A]

/-- The sender's value of a pure profile is her value of the kernels that follow it. -/
theorem senderValue_deterministic (f : S → M) (g : M → A) :
    G.senderValue (.deterministic f .of_discrete) (.deterministic g .of_discrete) =
      G.pureSenderValue f g := by
  simp only [senderValue, pureSenderValue, Kernel.deterministic_apply, integral_dirac]

/-- The receiver's value of a pure profile is his value of the kernels that follow it. -/
theorem receiverValue_deterministic (f : S → M) (g : M → A) :
    G.receiverValue (.deterministic f .of_discrete) (.deterministic g .of_discrete) =
      G.pureReceiverValue f g := by
  simp only [receiverValue, pureReceiverValue, Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply, Kernel.deterministic_apply, integral_dirac]

end SignalingGame
