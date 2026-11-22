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
  unfold senderValue
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  rw [Kernel.map_apply _ .of_discrete, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  refine integral_congr_ae (.of_forall fun m ↦ ?_)
  simp only [Kernel.comap_apply, Equiv.symm_apply_apply]
  exact integral_congr_ae (.of_forall fun a ↦ h s (π m) m a)

/-- Relabelling the signals leaves the receiver's value unchanged. -/
theorem receiverValue_relabel (π : M ≃ M) (σ : Kernel S M) [IsFiniteKernel σ] (ρ : Kernel M A)
    [IsFiniteKernel ρ] :
    G.receiverValue (σ.map π) (ρ.comap π.symm .of_discrete) = G.receiverValue σ ρ := by
  have hπ : (ρ.comap π.symm .of_discrete).comap π .of_discrete = ρ := by
    ext m : 1
    rw [Kernel.comap_apply, Kernel.comap_apply, π.symm_apply_apply]
  rw [receiverValue, receiverValue, Kernel.comp_map _ _ .of_discrete, hπ]

end SignalingGame
