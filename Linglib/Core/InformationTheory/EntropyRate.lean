/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy
public import Linglib.Core.Probability.Stationary
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Entropy rate

The conditional entropy `pastCondEntropy X μ n` of the value of a process at time `n` given the
`n` values before it falls as the past grows when the process is stationary, and its infimum is
the entropy rate. The drop from a past of `t - 1` values to a past of `t` is the information
`distanceInfo X μ t` that the value at time `0` carries about the value at time `t` given the
values between them. The entropy rate plus the information at distances beyond `T` is the
conditional entropy given a past of `T` values.

## Main definitions

* `InformationTheory.pastCondEntropy X μ n`: the entropy of `X n` given `X 0, …, X (n - 1)`.
* `InformationTheory.distanceInfo X μ t`: the mutual information of `X t` and `X 0` given the
  values between them.
* `InformationTheory.entropyRate X μ`: the infimum of `pastCondEntropy X μ`.

## Main statements

* `InformationTheory.entropy_block`: the chain rule for a block.
* `InformationTheory.distanceInfo_succ`: under stationarity, `distanceInfo X μ (t + 1)` is the
  drop from `pastCondEntropy X μ t` to `pastCondEntropy X μ (t + 1)`.
* `InformationTheory.entropyRate_add_tsum`: under stationarity, the entropy rate plus the
  information at distances beyond `T` is `pastCondEntropy X μ T`.

## References

* [cover-thomas-2006]
* [hahn-degen-futrell-2021]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace InformationTheory

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype S] {X : ℕ → Ω → S} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `pastCondEntropy X μ n` is the conditional entropy of the value at time `n` given the `n`
values before it. -/
noncomputable def pastCondEntropy (X : ℕ → Ω → S) (μ : Measure Ω) (n : ℕ) : ℝ :=
  H[X n | block X 0 n ; μ]

/-- `distanceInfo X μ t` is the mutual information `I[X t : X 0 | X 1, …, X (t - 1)]` between
values at distance `t` given the values between them, which is the entropy of `X t` that `X 0`
removes. -/
noncomputable def distanceInfo (X : ℕ → Ω → S) (μ : Measure Ω) (t : ℕ) : ℝ :=
  H[X t | block X 1 (t - 1) ; μ] - H[X t | block X 0 t ; μ]

/-- The entropy rate is the infimum of the conditional entropies of a value given its past,
which is their limit when the process is stationary. -/
noncomputable def entropyRate (X : ℕ → Ω → S) (μ : Measure Ω) : ℝ :=
  ⨅ n, pastCondEntropy X μ n

variable (hX : ∀ t, Measurable (X t))
include hX

theorem pastCondEntropy_zero : pastCondEntropy X μ 0 = H[X 0 ; μ] := by
  rw [pastCondEntropy, condEntropy_eq_sum _ (measurable_block hX 0 0), Fintype.sum_unique,
    show block X 0 0 ⁻¹' {default} = Set.univ from
      Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _]
  simp

theorem distanceInfo_succ_nonneg (t : ℕ) : 0 ≤ distanceInfo X μ (t + 1) :=
  sub_nonneg.mpr <| condEntropy_le_condEntropy_comp μ (hX _) (measurable_block hX 0 _) Fin.tail

/-- The entropy of a block is the sum of the conditional entropies of its values given their
predecessors. -/
theorem entropy_block (T : ℕ) : H[block X 0 T ; μ] = ∑ t ∈ range T, pastCondEntropy X μ t := by
  induction T with
  | zero => simp [entropy_of_subsingleton]
  | succ T ih =>
    rw [sum_range_succ, ← ih, pastCondEntropy, ← chain_rule μ (hX T) (measurable_block hX 0 T),
      block_zero_succ, entropy_comp_of_injective μ ((hX T).prodMk (measurable_block hX 0 T))
        (measurable_of_finite _) (Fin.snocEquiv _).injective]

variable (hs : IsStationary X μ)
include hs

/-- Under stationarity, `distanceInfo X μ (t + 1)` is the drop in conditional entropy as the past
grows from `t` values to `t + 1`. -/
theorem distanceInfo_succ (t : ℕ) :
    distanceInfo X μ (t + 1) = pastCondEntropy X μ t - pastCondEntropy X μ (t + 1) :=
  congrArg (· - _) <| ((hs 1 (t + 1)).comp
    (u := fun (v : Fin (t + 1) → S) ↦ (v (Fin.last t), fun i : Fin t ↦ v i.castSucc))
    (measurable_of_finite _)).condEntropy_eq (hX _) (measurable_block hX 1 t) (hX _)
    (measurable_block hX 0 t)

theorem pastCondEntropy_antitone : Antitone (pastCondEntropy X μ) :=
  antitone_nat_of_succ_le fun t ↦ by
    linarith [distanceInfo_succ hX hs t, distanceInfo_succ_nonneg (μ := μ) hX t]

theorem sum_Icc_mul_distanceInfo (T : ℕ) :
    ∑ t ∈ Icc 1 T, t * distanceInfo X μ t
      = ∑ t ∈ range T, pastCondEntropy X μ t - T * pastCondEntropy X μ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_Icc_succ_top (by omega), ih, distanceInfo_succ hX hs, sum_range_succ]
    push_cast
    ring

theorem tendsto_pastCondEntropy :
    Tendsto (pastCondEntropy X μ) atTop (𝓝 (entropyRate X μ)) :=
  tendsto_atTop_ciInf (pastCondEntropy_antitone hX hs)
    ⟨0, Set.forall_mem_range.mpr fun _ ↦ condEntropy_nonneg _ _ _⟩

/-- The entropy rate plus the information at distances beyond `T` is the conditional entropy of
a value given the `T` values before it. -/
theorem entropyRate_add_tsum (T : ℕ) :
    entropyRate X μ + ∑' t, distanceInfo X μ (T + t + 1) = pastCondEntropy X μ T := by
  have htel (n : ℕ) :
      ∑ t ∈ range n, (pastCondEntropy X μ (T + t) - pastCondEntropy X μ (T + t + 1))
        = pastCondEntropy X μ T - pastCondEntropy X μ (T + n) :=
    sum_range_sub' (fun t ↦ pastCondEntropy X μ (T + t)) n
  have hsum : HasSum (fun t ↦ distanceInfo X μ (T + t + 1))
      (pastCondEntropy X μ T - entropyRate X μ) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun t ↦ distanceInfo_succ_nonneg hX _) _).mpr ?_
    simp_rw [distanceInfo_succ hX hs, htel]
    exact tendsto_const_nhds.sub ((tendsto_pastCondEntropy hX hs).comp
      (tendsto_atTop_mono (fun n ↦ Nat.le_add_left n T) tendsto_id))
  rw [hsum.tsum_eq]
  ring

end InformationTheory
