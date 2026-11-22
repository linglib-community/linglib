module

public import Linglib.Pragmatics.SignalingGame.Basic

/-!
# Relabelling the signals

A permutation of the signals relabels a sender by pushing her signals forward and a receiver by
pulling his back. In cheap talk, where no utility depends on which signal is used, relabelling
both players leaves the values of the game unchanged
(`SignalingGame.IsCheapTalk.senderValue_relabel`,
`SignalingGame.IsCheapTalk.receiverValue_relabel`).

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

/-- Relabelling the signals leaves the sender's value of cheap talk unchanged. -/
theorem IsCheapTalk.senderValue_relabel (h : G.IsCheapTalk) (π : M ≃ M) (σ : Kernel S M)
    (ρ : Kernel M A) :
    G.senderValue (σ.map π) (ρ.comap π.symm .of_discrete) = G.senderValue σ ρ := by
  unfold senderValue
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  rw [Kernel.map_apply _ .of_discrete, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  refine integral_congr_ae (.of_forall fun m ↦ ?_)
  simp only [Kernel.comap_apply, Equiv.symm_apply_apply]
  exact integral_congr_ae (.of_forall fun a ↦ h.senderUtility_eq s (π m) m a)

/-- Relabelling the signals leaves the receiver's value of cheap talk unchanged. -/
theorem IsCheapTalk.receiverValue_relabel (h : G.IsCheapTalk) (π : M ≃ M) (σ : Kernel S M)
    (ρ : Kernel M A) :
    G.receiverValue (σ.map π) (ρ.comap π.symm .of_discrete) = G.receiverValue σ ρ := by
  unfold receiverValue
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  rw [Kernel.map_apply _ .of_discrete, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  refine integral_congr_ae (.of_forall fun m ↦ ?_)
  simp only [Kernel.comap_apply, Equiv.symm_apply_apply]
  exact integral_congr_ae (.of_forall fun a ↦ h.receiverUtility_eq s (π m) m a)

end SignalingGame
