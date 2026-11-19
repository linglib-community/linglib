module

public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Signaling games

In a signaling game a sender observes a state drawn from a prior `pr` and sends a signal, and a
receiver who sees only the signal guesses the state. A sender is a kernel `σ` from states to
signals and a receiver a kernel `η` from signals to states, so that the state and the guess have
the joint law `pr ⊗ₘ (η ∘ₖ σ)`. When both players are rewarded for a correct guess, as in Lewis's
games, their expected payoff is the expected success of the pair, the probability under that law
that the guess is the state. Equivalently it is the chance, averaged over the prior, that the round
trip `η ∘ₖ σ` returns the state (`SignalingGame.success_eq_lintegral`).

The signals are integrated out of the round trip, so relabelling the signals by any permutation,
and the states by one that preserves the prior, leaves expected success unchanged
(`SignalingGame.success_relabel`).

## References

* [lewis-1969]
* [huttegger-skyrms-tarres-wagner-2014]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace SignalingGame

variable {S M : Type*} [MeasurableSpace S] [MeasurableSpace M]

/-- The expected success of a sender `σ` with a receiver `η` at the prior `pr`: the probability
that the receiver's guess is the state. -/
noncomputable def success (pr : Measure S) (σ : Kernel S M) (η : Kernel M S) : ℝ :=
  (pr ⊗ₘ (η ∘ₖ σ)).real (Set.diagonal S)

variable [Countable S] [MeasurableSingletonClass S] (pr : Measure S) [SFinite pr]

private theorem compProd_real_diagonal (κ : Kernel S S) [IsSFiniteKernel κ] :
    (pr ⊗ₘ κ).real (Set.diagonal S) = (∫⁻ s, κ s {s} ∂pr).toReal := by
  rw [measureReal_def, Measure.compProd_apply .of_discrete]
  congr 2 with s
  congr 1
  ext t
  simp [eq_comm]

/-- Expected success is the chance, averaged over the prior, that the round trip from a state
through a signal returns it. -/
theorem success_eq_lintegral (σ : Kernel S M) [IsSFiniteKernel σ] (η : Kernel M S)
    [IsSFiniteKernel η] : success pr σ η = (∫⁻ s, (η ∘ₖ σ) s {s} ∂pr).toReal :=
  compProd_real_diagonal pr _

theorem success_eq_sum [Fintype S] [IsFiniteMeasure pr] [Fintype M] [MeasurableSingletonClass M]
    (σ : Kernel S M) [IsFiniteKernel σ] (η : Kernel M S) [IsFiniteKernel η] :
    success pr σ η = ∑ s, pr.real {s} * ∑ m, (σ s).real {m} * (η m).real {s} := by
  rw [success_eq_lintegral, lintegral_fintype, ENNReal.toReal_sum fun s _ ↦
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)]
  refine sum_congr rfl fun s _ ↦ ?_
  rw [Kernel.comp_apply' _ _ _ (.singleton s), lintegral_fintype, ENNReal.toReal_mul,
    ENNReal.toReal_sum fun m _ ↦ ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _),
    mul_comm, measureReal_def]
  simp only [ENNReal.toReal_mul, measureReal_def, mul_comm]

/-- Relabelling the states by a permutation `e` that preserves the prior, and the signals by any
permutation `π`, leaves the expected success of every sender with every receiver unchanged. -/
theorem success_relabel [Countable M] [MeasurableSingletonClass M] {pr : Measure S} [SFinite pr]
    {e : S ≃ S} (he : MeasurePreserving e pr pr) (π : M ≃ M) (σ : Kernel S M) [IsFiniteKernel σ]
    (η : Kernel M S) [IsFiniteKernel η] :
    success pr ((σ.comap e.symm .of_discrete).map π) ((η.comap π.symm .of_discrete).map e) =
      success pr σ η := by
  have hπ : (η.comap π.symm .of_discrete).comap π .of_discrete = η := by
    ext m : 1
    rw [Kernel.comap_apply, Kernel.comap_apply, π.symm_apply_apply]
  rw [success, ← Kernel.map_comp, Kernel.comp_map _ _ .of_discrete, hπ, success,
    compProd_real_diagonal, compProd_real_diagonal, ← he.lintegral_comp .of_discrete]
  refine congrArg _ (lintegral_congr fun s ↦ ?_)
  rw [Kernel.map_apply' _ .of_discrete _ (.singleton _), show e ⁻¹' {e s} = {s} by ext; simp,
    Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply, e.symm_apply_apply]

end SignalingGame
