module

public import Linglib.Pragmatics.SignalingGame.Basic

/-!
# Relabelling the signals

A permutation of the signals relabels a sender by pushing her signals forward and a receiver by
pulling his back. When the sender's utility does not depend on which signal is used, relabelling
both players leaves the values of the game unchanged
(`SignalingGame.senderValue_relabel`, `SignalingGame.receiverValue_relabel`).

## TODO

* Move `SignalingGame.success_relabel` and the bounds on strategies that every relabelling leaves
  unchanged here from `Basic`, and state them for the values of a game.
* The optimal strategies of a game whose utilities ignore the signal form orbits of the
  relabellings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SignalingGame

variable {S M A : Type*} [MeasurableSpace S] [MeasurableSpace M] [MeasurableSpace A]
  [Countable M] [MeasurableSingletonClass M] (G : SignalingGame S M A)

/-- Relabelling the signals leaves the sender's value unchanged when her utility ignores the
signal. -/
theorem senderValue_relabel (h : ∀ s m m' a, G.senderUtility s m a = G.senderUtility s m' a)
    (π : M ≃ M) (σ : Kernel S M) [IsFiniteKernel σ] (ρ : Kernel M A) [IsFiniteKernel ρ] :
    G.senderValue (σ.map π) (ρ.comap π.symm .of_discrete) = G.senderValue σ ρ := by
  -- TODO: `Kernel.map_apply` and `integral_map` at each state, as in `success_relabel`.
  sorry

/-- Relabelling the signals leaves the receiver's value unchanged. -/
theorem receiverValue_relabel (π : M ≃ M) (σ : Kernel S M) [IsFiniteKernel σ] (ρ : Kernel M A)
    [IsFiniteKernel ρ] :
    G.receiverValue (σ.map π) (ρ.comap π.symm .of_discrete) = G.receiverValue σ ρ := by
  -- TODO: the composite of the relabelled kernels is the composite of the kernels.
  sorry

end SignalingGame
