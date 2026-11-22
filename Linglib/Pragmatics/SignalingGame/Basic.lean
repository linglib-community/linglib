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
(`SignalingGame.success_relabel`). A sender whose own strategy is unchanged by every relabelling
of the signals sends each signal equally often at every state, so the pair succeeds no more often
than the likeliest state occurs (`SignalingGame.success_le_of_forall_map_eq`), and likewise for a
receiver (`SignalingGame.success_le_of_forall_comap_eq`). A sender and a receiver who act on
functions `f` and `g` always succeed exactly when `g (f s) = s` at almost every state
(`SignalingGame.success_deterministic_eq_one_iff`).

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

theorem success_le_one (pr : Measure S) [IsProbabilityMeasure pr] (σ : Kernel S M)
    [IsMarkovKernel σ] (η : Kernel M S) [IsMarkovKernel η] : success pr σ η ≤ 1 :=
  measureReal_le_one

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

theorem success_deterministic [Countable M] [MeasurableSingletonClass M] (f : S → M) (g : M → S) :
    success pr (.deterministic f .of_discrete) (.deterministic g .of_discrete) =
      pr.real {s | g (f s) = s} := by
  rw [success_eq_lintegral, measureReal_def, ← lintegral_indicator_one .of_discrete]
  refine congrArg _ (lintegral_congr fun s ↦ ?_)
  rw [Kernel.comp_apply' _ _ _ (.singleton s), Kernel.deterministic_apply, lintegral_dirac,
    Kernel.deterministic_apply, Measure.dirac_apply' _ (.singleton s)]
  by_cases h : g (f s) = s <;> simp [Set.indicator, h]

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

variable [IsProbabilityMeasure pr]

private theorem compProd_const_real_diagonal_le (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ}
    (hb : ∀ s, pr.real {s} ≤ b) : (pr ⊗ₘ Kernel.const S ν).real (Set.diagonal S) ≤ b := by
  have hb0 : 0 ≤ b := measureReal_nonneg.trans (hb pr.nonempty_of_neZero.some)
  have h (t : S) : pr ((fun s ↦ (s, t)) ⁻¹' Set.diagonal S) ≤ ENNReal.ofReal b := by
    rw [show (fun s ↦ (s, t)) ⁻¹' Set.diagonal S = {t} by ext; simp, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hb t)
  rw [Measure.compProd_const, measureReal_def, Measure.prod_apply_symm .of_discrete]
  exact ENNReal.toReal_le_of_le_ofReal hb0 ((lintegral_mono h).trans (by simp))

/-- A sender whose signal does not depend on the state succeeds no more often than the likeliest
state occurs, whatever the receiver. -/
theorem success_const_le (μ : Measure M) [IsProbabilityMeasure μ] (η : Kernel M S)
    [IsMarkovKernel η] {b : ℝ} (hb : ∀ s, pr.real {s} ≤ b) :
    success pr (Kernel.const S μ) η ≤ b := by
  have : η ∘ₖ Kernel.const S μ = Kernel.const S (η ∘ₘ μ) := by
    ext s : 1
    rw [Kernel.comp_apply, Kernel.const_apply, Kernel.const_apply]
  rw [success, this]
  exact compProd_const_real_diagonal_le pr _ hb

/-- A receiver whose guess does not depend on the signal succeeds no more often than the likeliest
state occurs, whatever the sender. -/
theorem success_le_of_const (σ : Kernel S M) [IsMarkovKernel σ] (ν : Measure S)
    [IsProbabilityMeasure ν] {b : ℝ} (hb : ∀ s, pr.real {s} ≤ b) :
    success pr σ (Kernel.const M ν) ≤ b := by
  rw [success, Kernel.const_comp']
  exact compProd_const_real_diagonal_le pr _ hb

variable [Countable M] [MeasurableSingletonClass M]

/-- A sender and a receiver who each act on a function always succeed exactly when the receiver's
function undoes the sender's at almost every state. -/
theorem success_deterministic_eq_one_iff (f : S → M) (g : M → S) :
    success pr (.deterministic f .of_discrete) (.deterministic g .of_discrete) = 1 ↔
      ∀ᵐ s ∂pr, g (f s) = s := by
  rw [success_deterministic, measureReal_def, ENNReal.toReal_eq_one_iff,
    ae_iff_prob_eq_one .of_discrete]

/-- A sender whose strategy is unchanged by every relabelling of the signals succeeds no more often
than the likeliest state occurs, whatever the receiver. -/
theorem success_le_of_forall_map_eq [Fintype M] (σ : Kernel S M) [IsMarkovKernel σ]
    (η : Kernel M S) [IsMarkovKernel η] (hσ : ∀ π : Equiv.Perm M, σ.map π = σ) {b : ℝ}
    (hb : ∀ s, pr.real {s} ≤ b) : success pr σ η ≤ b := by
  classical
  have h (s : S) (m : M) : σ s {m} = (Fintype.card M : ℝ≥0∞)⁻¹ := by
    have key (m' : M) : σ s {m'} = σ s {m} := by
      conv_lhs => rw [← hσ (Equiv.swap m m'), Kernel.map_apply' _ .of_discrete _ (.singleton m')]
      congr 1
      ext x
      simp [Equiv.swap_apply_eq_iff]
    refine ENNReal.eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_congr rfl
      fun m' _ ↦ key m', sum_measure_singleton, Finset.coe_univ, measure_univ]
  have s₀ := pr.nonempty_of_neZero.some
  have : σ = Kernel.const S (σ s₀) := by
    ext s : 1
    exact Measure.ext_of_singleton fun m ↦ by rw [Kernel.const_apply, h, h]
  rw [this]
  exact success_const_le pr _ η hb

/-- A receiver whose strategy is unchanged by every relabelling of the signals succeeds no more
often than the likeliest state occurs, whatever the sender. -/
theorem success_le_of_forall_comap_eq (σ : Kernel S M) [IsMarkovKernel σ] (η : Kernel M S)
    [IsMarkovKernel η] (hη : ∀ π : Equiv.Perm M, η.comap π .of_discrete = η) {b : ℝ}
    (hb : ∀ s, pr.real {s} ≤ b) : success pr σ η ≤ b := by
  classical
  have m₀ := (σ pr.nonempty_of_neZero.some).nonempty_of_neZero.some
  have : η = Kernel.const M (η m₀) := by
    ext m : 1
    conv_lhs => rw [← hη (Equiv.swap m m₀), Kernel.comap_apply, Equiv.swap_apply_left]
    rfl
  rw [this]
  exact success_le_of_const pr σ _ hb

end SignalingGame
