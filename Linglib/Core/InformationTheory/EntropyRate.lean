/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Entropy.Basic
public import Linglib.Core.Probability.Process.Stationary
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Entropy rate

The entropy rate of a process is the growth of the entropy of a block per value. It is defined
here as the infimum of the conditional entropies `pastCondEntropy X μ n` of the value at time `n`
given the `n` values before it. For a stationary process these
[fall to the rate](##tendsto_pastCondEntropy), and
[the entropy per value of a block tends to it](##tendsto_inv_mul_entropy_block). Their
[drop from a past of `t` values to a past of `t + 1`](##distanceInfo_succ) is the conditional mutual
information `distanceInfo X μ (t + 1)` between values at that distance given the values between
them, so [the rate plus the information beyond distance `T`](##entropyRate_add_tsum) is the
conditional entropy given `T` values. When the blocks of one process have the laws of the reversed
blocks of another, the two have
[the same information at each positive distance](##distanceInfo_succ_eq_of_map_rev) and
[the same rate](##entropyRate_eq_of_map_rev).

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

/-- `distanceInfo X μ t` is the mutual information between values at distance `t` given the values
between them, the quantity `I_t` of [hahn-degen-futrell-2021]. -/
noncomputable def distanceInfo (X : ℕ → Ω → S) (μ : Measure Ω) (t : ℕ) : ℝ :=
  I[X t : X 0 | block X 1 (t - 1) ; μ]

/-- The entropy rate is the infimum of the conditional entropies of a value given its past. For a
stationary process this is their limit and the limit of the entropy per value of a block; other
processes need have neither limit. -/
noncomputable def entropyRate (X : ℕ → Ω → S) (μ : Measure Ω) : ℝ :=
  ⨅ n, pastCondEntropy X μ n

variable (hX : ∀ t, Measurable (X t))
include hX

theorem pastCondEntropy_zero : pastCondEntropy X μ 0 = H[X 0 ; μ] := by
  rw [pastCondEntropy, condEntropy_eq_sum _ (measurable_block hX 0 0), Fintype.sum_unique,
    show block X 0 0 ⁻¹' {default} = Set.univ from
      Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _]
  simp

theorem distanceInfo_nonneg (t : ℕ) : 0 ≤ distanceInfo X μ t :=
  condMutualInfo_nonneg μ (hX _) (hX _)

/-- The value at distance `t` carries no information about the value at time `0` beyond the values
between them exactly when the two are independent given those values. -/
theorem distanceInfo_eq_zero_iff (t : ℕ) :
    distanceInfo X μ t = 0 ↔ ∀ z, X t ⟂ᵢ[μ[|block X 1 (t - 1) ⁻¹' {z}]] X 0 :=
  condMutualInfo_eq_zero_iff μ (hX _) (hX _) (measurable_block hX 1 _)

/-- The information at distance `t + 1` is the entropy of the value at that distance that the value
at time `0` removes, given the values between them. -/
theorem distanceInfo_succ_eq_sub (t : ℕ) :
    distanceInfo X μ (t + 1) = H[X (t + 1) | block X 1 t ; μ] - pastCondEntropy X μ (t + 1) := by
  have he : MeasurableEmbedding (Fin.consEquiv fun _ : Fin (t + 1) ↦ S) :=
    (MeasurableEquiv.mk (Fin.consEquiv fun _ ↦ S) (measurable_of_finite _)
      (measurable_of_finite _)).measurableEmbedding
  rw [pastCondEntropy, block_zero_succ', condEntropy_comp_right_of_measurableEmbedding _ _
    ((hX 0).prodMk (measurable_block hX 1 t)) he]
  exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (hX _) (hX _) (measurable_block hX 1 t)

/-- The entropy of a block is the sum of the conditional entropies of its values given their
predecessors. -/
theorem entropy_block (T : ℕ) : H[block X 0 T ; μ] = ∑ t ∈ range T, pastCondEntropy X μ t := by
  induction T with
  | zero => simp [entropy_of_subsingleton]
  | succ T ih =>
    rw [sum_range_succ, ← ih, pastCondEntropy,
      ← entropy_pair_eq_add_condEntropy μ (hX T) (measurable_block hX 0 T),
      block_zero_succ, entropy_comp_of_injective μ ((hX T).prodMk (measurable_block hX 0 T))
        (measurable_of_finite _) (Fin.snocEquiv _).injective]

section Stationary

variable (hs : IsStationary X μ)
include hs

/-- Under stationarity, `distanceInfo X μ (t + 1)` is the drop in conditional entropy as the past
grows from `t` values to `t + 1`. -/
theorem distanceInfo_succ (t : ℕ) :
    distanceInfo X μ (t + 1) = pastCondEntropy X μ t - pastCondEntropy X μ (t + 1) := by
  rw [distanceInfo_succ_eq_sub hX]
  exact congrArg (· - _) <| ((hs 1).comp (u := fun x : ℕ → S ↦ (x t, fun i : Fin t ↦ x i))
    (by fun_prop)).condEntropy_eq (hX _) (measurable_block hX 1 t) (hX _) (measurable_block hX 0 t)

theorem pastCondEntropy_antitone : Antitone (pastCondEntropy X μ) :=
  antitone_nat_of_succ_le fun t ↦ by
    linarith [distanceInfo_succ hX hs t, distanceInfo_nonneg (μ := μ) hX (t + 1)]

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

/-- The entropy per value of a block tends to the entropy rate, so for a stationary process
`entropyRate` agrees with the definition of the rate as the growth of block entropy per value. -/
theorem tendsto_inv_mul_entropy_block :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * H[block X 0 n ; μ]) atTop (𝓝 (entropyRate X μ)) := by
  simpa only [entropy_block hX] using (tendsto_pastCondEntropy hX hs).cesaro

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
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun _ ↦ distanceInfo_nonneg hX _) _).mpr ?_
    simp_rw [distanceInfo_succ hX hs, htel]
    exact tendsto_const_nhds.sub ((tendsto_pastCondEntropy hX hs).comp
      (tendsto_atTop_mono (fun n ↦ Nat.le_add_left n T) tendsto_id))
  rw [hsum.tsum_eq]
  ring

end Stationary

/-! ### Time reversal

When the blocks of `Y` have the laws of the reversed blocks of `X`, the two processes have the same
block entropies, hence the same conditional entropies given the past and the same entropy rate.
The condition also forces both to be stationary, which gives them the same information at every
positive distance. -/

section Reversal

variable {Ω' : Type*} [MeasurableSpace Ω'] {Y : ℕ → Ω' → S} {ν : Measure Ω'}
  [IsProbabilityMeasure ν] (hY : ∀ t, Measurable (Y t))
  (h : ∀ n, ν.map (block Y 0 n) = μ.map fun ω ↦ block X 0 n ω ∘ Fin.rev)
include hY h

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] hY in
theorem entropy_block_eq_of_map_rev (n : ℕ) : H[block Y 0 n ; ν] = H[block X 0 n ; μ] := by
  rw [entropy_def, h n, ← entropy_def]
  exact entropy_comp_of_injective μ (measurable_block hX 0 n) (f := fun v : Fin n → S ↦ v ∘ Fin.rev)
    (measurable_of_finite _) fun v w hvw ↦ funext fun i ↦ by simpa using congrFun hvw i.rev

theorem pastCondEntropy_eq_of_map_rev (n : ℕ) : pastCondEntropy Y ν n = pastCondEntropy X μ n := by
  have hXn := entropy_block (μ := μ) hX (n + 1)
  have hYn := entropy_block (μ := ν) hY (n + 1)
  rw [sum_range_succ, ← entropy_block hX n] at hXn
  rw [sum_range_succ, ← entropy_block hY n] at hYn
  linarith [entropy_block_eq_of_map_rev hX h n, entropy_block_eq_of_map_rev hX h (n + 1)]

theorem entropyRate_eq_of_map_rev : entropyRate Y ν = entropyRate X μ :=
  iInf_congr (pastCondEntropy_eq_of_map_rev hX hY h)

omit [IsProbabilityMeasure μ] in
/-- A process whose blocks have the laws of the reversed blocks of another is stationary: the
block of `n` values from any time has the law of the reversed first block of `n` values. -/
theorem isStationary_of_map_rev : IsStationary Y ν := isStationary_iff_forall_block.2 fun a n ↦ by
  let g : (Fin (a + n) → S) → (Fin n → S) := fun v j ↦ v (Fin.natAdd a j)
  have hg : Measurable g := measurable_of_finite g
  have hrev (m : ℕ) : Measurable fun ω ↦ block X 0 m ω ∘ Fin.rev :=
    (measurable_of_finite fun v : Fin m → S ↦ v ∘ Fin.rev).comp (measurable_block hX 0 m)
  have h₁ : block Y a n = g ∘ block Y 0 (a + n) := by
    funext ω j
    simp [g, block, add_comm]
  have h₂ : g ∘ (fun ω ↦ block X 0 (a + n) ω ∘ Fin.rev) = fun ω ↦ block X 0 n ω ∘ Fin.rev := by
    funext ω j
    simp only [g, block, Function.comp_apply, Fin.val_rev, Fin.val_natAdd, add_zero]
    exact congrArg (fun k ↦ X k ω) (by omega)
  refine ⟨(measurable_block hY a n).aemeasurable, (measurable_block hY 0 n).aemeasurable, ?_⟩
  rw [h₁, ← Measure.map_map hg (measurable_block hY 0 _), h (a + n), Measure.map_map hg (hrev _),
    h₂, h n]

omit [IsProbabilityMeasure ν] in
/-- A process whose reversed blocks have the laws of the blocks of another is stationary as well:
reversing twice is the identity, so the condition holds with the two processes swapped. -/
theorem isStationary_of_map_rev' : IsStationary X μ := by
  refine isStationary_of_map_rev (μ := ν) hY hX fun n ↦ ?_
  have hrev : Measurable fun v : Fin n → S ↦ v ∘ Fin.rev := measurable_of_finite _
  have hX' := measurable_block hX 0 n
  have hY' := measurable_block hY 0 n
  rw [show (fun ω ↦ block Y 0 n ω ∘ Fin.rev) = (· ∘ Fin.rev) ∘ block Y 0 n from rfl,
    ← Measure.map_map hrev hY', h n,
    show (fun ω ↦ block X 0 n ω ∘ Fin.rev) = (· ∘ Fin.rev) ∘ block X 0 n from rfl,
    Measure.map_map hrev (hrev.comp hX')]
  exact congrArg (Measure.map · μ) (funext fun ω ↦ funext fun i ↦ by simp)

theorem distanceInfo_succ_eq_of_map_rev (t : ℕ) :
    distanceInfo Y ν (t + 1) = distanceInfo X μ (t + 1) := by
  rw [distanceInfo_succ hY (isStationary_of_map_rev hX hY h),
    distanceInfo_succ hX (isStationary_of_map_rev' hX hY h),
    pastCondEntropy_eq_of_map_rev hX hY h, pastCondEntropy_eq_of_map_rev hX hY h]

end Reversal

end InformationTheory
