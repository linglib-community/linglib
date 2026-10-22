/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecificLimits.ProdOneSub
public import Linglib.Core.Probability.AutoregressiveSequenceModel.Basic

/-!
# Tight autoregressive sequence models

Survival is the probability that no end symbol appears in the first `n` steps. The probabilities
of the strings shorter than `n` and the survival at `n` sum to one, so a model is tight exactly
when survival tends to zero, and since survival is the product of one minus the conditional end
probability at each step, exactly when that probability reaches one or has a divergent sum. In a
tight model the strings extending a prefix have total probability its prefix probability, the
conditionals are the next-symbol laws of the string law, and the expected length is the total
survival after the first step.

## Main definitions

* `survival`, `stopProb`, `eosHazard`.

## Main results

* `isTight_iff_tendsto_survival`, `survival_eq_prod`.
* `isTight_iff`: tight exactly when the conditional end probability reaches one or has a
  divergent sum ([du-etal-2023], Theorem 4.7).
* `isTight_of_le_next_none`: a divergent lower bound on the end probability gives tightness
  ([du-etal-2023], Proposition 4.3).
* `IsTight.after`, `IsTight.stringMeasure_setOf_prefix`, `IsTight.next_ofMeasure_stringMeasure`.
* `lintegral_length_le`, `IsTight.lintegral_length`, `lintegral_length_le_div`: bounds on the
  expected length; `IsTight.tsum_prefixProb` ([opedal-chodroff-cotterell-wilcox-2024]).

## Implementation notes

* The product criterion behind `isTight_iff` is `ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff`,
  [du-etal-2023]'s Corollary 4.6 extended to factors that may vanish.
* [du-etal-2023] count steps from one, so their conditional end probability at step `t` is
  `eosHazard (t - 1)`. Where survival is zero the ratio is `0` by the convention of `ℝ≥0∞`
  division; the characterization is unaffected, since survival first reaching zero forces a
  conditional end probability of one.

## References

* [du-etal-2023]
* [opedal-chodroff-cotterell-wilcox-2024]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal

namespace AutoregressiveSequenceModel

variable {α : Type*} [MeasurableSpace α] (M : AutoregressiveSequenceModel α)

/-! ### Survival -/

/-- The probability that no end symbol appears in the first `n` steps: the total prefix
probability of the strings of length `n`. -/
noncomputable def survival (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.prefixProb x

/-- The probability of generating a string of length `n`. -/
noncomputable def stopProb (n : ℕ) : ℝ≥0∞ := ∑' x : {x : List α // x.length = n}, M.stringProb x

/-- The probability of ending after `n` symbols given survival to that point, the end
probability at step `n + 1` of [du-etal-2023]. -/
noncomputable def eosHazard (n : ℕ) : ℝ≥0∞ := M.stopProb n / M.survival n

@[simp] theorem survival_zero : M.survival 0 = 1 := by
  rw [survival, tsum_eq_single (⟨[], rfl⟩ : {x : List α // x.length = 0}) fun x hx ↦
    absurd (Subtype.ext (List.eq_nil_of_length_eq_zero x.2)) hx]
  rfl

theorem tsum_stringProb : ∑' x, M.stringProb x = ∑' n, M.stopProb n := by
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma']
  rfl

/-- Strings of length `n + 1` are the strings of length `n` followed by a symbol. -/
private def concatEquiv (n : ℕ) :
    {x : List α // x.length = n} × α ≃ {y : List α // y.length = n + 1} where
  toFun p := ⟨p.1.1 ++ [p.2], by simp [p.1.2]⟩
  invFun y := (⟨y.1.dropLast, by simp [y.2]⟩, y.1.getLast (List.ne_nil_of_length_eq_add_one y.2))
  left_inv p := by ext <;> simp
  right_inv y := Subtype.ext (List.dropLast_append_getLast _)

/-- The strings of length `n` end with probability at least `c` times survival to `n` when every
prefix of length `n` ends with probability at least `c`. -/
theorem mul_survival_le_stopProb {n : ℕ} {c : ℝ≥0∞}
    (hc : ∀ x : List α, x.length = n → c ≤ M.next x {none}) :
    c * M.survival n ≤ M.stopProb n := by
  rw [survival, ← ENNReal.tsum_mul_left, stopProb]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [stringProb, mul_comm c]
  gcongr
  exact hc x x.2

/-- Surviving `n` steps after `x` is surviving `n + |x|` steps through `x`. -/
theorem prefixProb_mul_survival_after_le (x : List α) (n : ℕ) :
    M.prefixProb x * (M.after x).survival n ≤ M.survival (n + x.length) := by
  calc M.prefixProb x * (M.after x).survival n
      = ∑' z : {z : List α // z.length = n}, M.prefixProb (x ++ z.1) := by
        rw [survival, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun z ↦ (M.prefixProb_append x z).symm
    _ ≤ M.survival (n + x.length) :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (f := fun z ↦
          (⟨x ++ z.1, by simp [z.2, add_comm]⟩ : {y : List α // y.length = n + x.length}))
        (fun z z' h ↦ Subtype.ext (List.append_cancel_left (congrArg Subtype.val h)))
        fun y ↦ M.prefixProb y.1

variable [MeasurableSingletonClass α] [Countable α]


/-- After any prefix the model either ends or continues with some symbol. -/
theorem next_none_add_tsum_next_some (x : List α) :
    M.next x {none} + ∑' a, M.next x {some a} = 1 := by
  have hU : ({none} : Set (Option α))ᶜ = ⋃ a, {some a} := by ext o; cases o <;> simp
  rw [← measure_iUnion (fun a b hab ↦ Set.disjoint_singleton.2 ((Option.some_injective α).ne hab))
    fun a ↦ measurableSet_singleton _, ← hU, measure_add_measure_compl (measurableSet_singleton _),
    measure_univ]

theorem survival_succ_add_stopProb (n : ℕ) : M.survival (n + 1) + M.stopProb n = M.survival n := by
  rw [survival, ← (concatEquiv n).tsum_eq, ENNReal.tsum_prod', stopProb, survival,
    ← ENNReal.tsum_add]
  refine tsum_congr fun x ↦ ?_
  simp only [concatEquiv, Equiv.coe_fn_mk, prefixProb_concat, ENNReal.tsum_mul_left, stringProb,
    ← mul_add, add_comm (∑' a, _), next_none_add_tsum_next_some, mul_one]

theorem sum_range_stopProb_add_survival (n : ℕ) :
    ∑ k ∈ range n, M.stopProb k + M.survival n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, add_assoc, add_comm (M.stopProb n),
      survival_succ_add_stopProb, ih]

theorem survival_le_one (n : ℕ) : M.survival n ≤ 1 :=
  (M.sum_range_stopProb_add_survival n).le.trans' le_add_self

theorem survival_ne_top (n : ℕ) : M.survival n ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.survival_le_one n)

theorem stopProb_le_survival (n : ℕ) : M.stopProb n ≤ M.survival n :=
  (M.survival_succ_add_stopProb n).le.trans' le_add_self

theorem survival_antitone : Antitone M.survival :=
  antitone_nat_of_succ_le fun n ↦ (M.survival_succ_add_stopProb n).le.trans' le_self_add

theorem isTight_iff_tendsto_survival : M.IsTight ↔ Tendsto M.survival atTop (𝓝 0) := by
  have hsum (n : ℕ) : ∑ k ∈ range n, M.stopProb k = 1 - M.survival n :=
    ENNReal.eq_sub_of_add_eq (M.survival_ne_top n) (M.sum_range_stopProb_add_survival n)
  have hinf : ⨅ n, M.survival n ≤ 1 := (iInf_le _ 0).trans (M.survival_le_one 0)
  rw [IsTight, tsum_stringProb, ENNReal.tsum_eq_iSup_nat, iSup_congr hsum, ← ENNReal.sub_iInf]
  constructor
  · intro h
    have h0 : ⨅ n, M.survival n = 0 := by
      rw [← ENNReal.sub_sub_cancel ENNReal.one_ne_top hinf, h, tsub_self]
    exact h0 ▸ tendsto_atTop_iInf M.survival_antitone
  · intro h
    rw [tendsto_nhds_unique (tendsto_atTop_iInf M.survival_antitone) h, tsub_zero]

/-! ### The conditional end probability -/

theorem eosHazard_le_one (n : ℕ) : M.eosHazard n ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact M.stopProb_le_survival n)

theorem survival_succ (n : ℕ) : M.survival (n + 1) = M.survival n * (1 - M.eosHazard n) := by
  by_cases h : M.survival n = 0
  · rw [h, zero_mul]
    exact nonpos_iff_eq_zero.1 ((M.survival_antitone n.le_succ).trans h.le)
  · rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, eosHazard,
      ENNReal.mul_div_cancel h (M.survival_ne_top n)]
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)

theorem survival_eq_prod (n : ℕ) : M.survival n = ∏ k ∈ range n, (1 - M.eosHazard k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [survival_succ, ih, prod_range_succ]

/-- A model is tight exactly when the conditional end probability reaches one or has a divergent
sum ([du-etal-2023], Theorem 4.7). -/
theorem isTight_iff : M.IsTight ↔ (∃ n, M.eosHazard n = 1) ∨ ∑' n, M.eosHazard n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext M.survival_eq_prod]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff M.eosHazard_le_one

/-- A model whose end probability after every prefix of length `t - 1` is at least `f t`, for a
divergent series of bounds, is tight ([du-etal-2023], Proposition 4.3). -/
theorem isTight_of_le_next_none {f : ℕ → ℝ≥0∞}
    (hf : ∀ x : List α, f (x.length + 1) ≤ M.next x {none}) (h : ∑' t, f (t + 1) = ∞) :
    M.IsTight := by
  by_cases hs : ∃ n, M.survival n = 0
  · obtain ⟨n, hn⟩ := hs
    rw [isTight_iff_tendsto_survival]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
    exact (nonpos_iff_eq_zero.1 ((M.survival_antitone hm).trans hn.le)).symm
  · simp only [not_exists] at hs
    refine M.isTight_iff.2 (.inr (eq_top_mono (ENNReal.tsum_le_tsum fun n ↦ ?_) h))
    rw [eosHazard, ENNReal.le_div_iff_mul_le (.inl (hs n)) (.inl (M.survival_ne_top n))]
    exact M.mul_survival_le_stopProb fun x hx ↦ hx ▸ hf x

/-- When the end probability after a prefix depends only on its length, survival is the product
of one minus it. -/
theorem survival_eq_prod_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (n : ℕ) :
    M.survival n = ∏ k ∈ range n, (1 - e k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop : M.stopProb n = e n * M.survival n := by
      rw [stopProb, survival, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun x ↦ by rw [stringProb, he, x.2, mul_comm]
    rw [prod_range_succ, ← ih, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n), hstop,
      ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]

/-- When the end probability after a prefix depends only on its length, the model is tight exactly
when that probability reaches one or has a divergent sum. -/
theorem isTight_iff_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (he1 : ∀ n, e n ≤ 1) :
    M.IsTight ↔ (∃ n, e n = 1) ∨ ∑' n, e n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext (M.survival_eq_prod_of_next_none_eq he)]
  exact ENNReal.tendsto_prod_range_one_sub_nhds_zero_iff he1

/-- An end probability of at least `c` after every prefix makes survival decay geometrically. -/
theorem survival_le_pow {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) (n : ℕ) :
    M.survival n ≤ (1 - c) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop := M.mul_survival_le_stopProb (n := n) fun x _ ↦ hc x
    rw [pow_succ, ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n)
      (M.stopProb_le_survival n)) (M.survival_succ_add_stopProb n)]
    calc M.survival n - M.stopProb n ≤ M.survival n - c * M.survival n := tsub_le_tsub_left hstop _
      _ = M.survival n * (1 - c) := by
        rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]
      _ ≤ (1 - c) ^ n * (1 - c) := by gcongr

/-- The string probabilities of any model sum to at most one. -/
theorem tsum_stringProb_le_one : ∑' x, M.stringProb x ≤ 1 := by
  rw [tsum_stringProb, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n ↦ le_self_add.trans (M.sum_range_stopProb_add_survival n).le

/-- The model after a prefix of positive probability inherits tightness. -/
theorem IsTight.after {M : AutoregressiveSequenceModel α} (hM : M.IsTight) {x : List α}
    (hx : M.prefixProb x ≠ 0) : (M.after x).IsTight := by
  rw [isTight_iff_tendsto_survival] at hM ⊢
  have hlim : Tendsto (fun n ↦ M.survival (n + x.length) / M.prefixProb x) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const ((tendsto_add_atTop_iff_nat x.length).2 hM) (.inr hx)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
    fun n ↦ ?_
  rw [ENNReal.le_div_iff_mul_le (.inl hx) (.inl (M.prefixProb_ne_top x)), mul_comm]
  exact M.prefixProb_mul_survival_after_le x n

/-- In a tight model the strings extending `x` have total probability its prefix probability. -/
theorem IsTight.stringMeasure_setOf_prefix {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    (x : List α) : M.stringMeasure {y | x <+: y} = M.prefixProb x := by
  rw [M.stringMeasure_setOf_prefix]
  by_cases hx : M.prefixProb x = 0
  · rw [hx, zero_mul]
  · rw [hM.after hx, mul_one]

/-- A tight model's conditional after a prefix of positive probability is the next-symbol law of
its string law. -/
theorem IsTight.next_ofMeasure_stringMeasure {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    {x : List α} (hx : M.prefixProb x ≠ 0) : (ofMeasure M.stringMeasure).next x = M.next x := by
  have := M.isTight_iff_isProbabilityMeasure.1 hM
  refine Measure.ext_of_singleton fun o ↦ ?_
  cases o with
  | some a =>
    have hsub : {y | x ++ [a] <+: y} ⊆ {y | x <+: y} := fun y ↦ (List.prefix_append x [a]).trans
    rw [next_ofMeasure_apply_some, cond_apply_of_subset .of_discrete hsub,
      hM.stringMeasure_setOf_prefix, hM.stringMeasure_setOf_prefix, prefixProb_concat,
      mul_comm (M.prefixProb x), ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]
  | none =>
    have hsub : {x} ⊆ {y | x <+: y} := Set.singleton_subset_iff.2 (List.prefix_refl x)
    rw [next_ofMeasure_apply_none _ (by rwa [hM.stringMeasure_setOf_prefix]),
      cond_apply_of_subset .of_discrete hsub, stringMeasure_singleton,
      hM.stringMeasure_setOf_prefix, stringProb, mul_comm (M.prefixProb x),
      ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]

/-! ### Expected length

The law of the generated string is a sum of point masses, so an integral against it is a sum
weighted by the string probabilities. Survival to `n` is at least the probability of a string of
length at least `n`, with equality in a tight model, so the tail-sum formula bounds the expected
length by the total survival after the first step. -/

/-- Survival to `n` is at least the probability of a string of length at least `n`. -/
theorem stringMeasure_setOf_length_le (n : ℕ) :
    M.stringMeasure {y | n ≤ y.length} ≤ M.survival n := by
  rw [← Measure.tsum_measure_setOf_prefix_length, survival]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [M.stringMeasure_setOf_prefix]
  exact mul_le_of_le_one_right' (M.after x.1).tsum_stringProb_le_one

/-- In a tight model survival to `n` is the probability of a string of length at least `n`. -/
theorem IsTight.stringMeasure_setOf_length_le {M : AutoregressiveSequenceModel α}
    (hM : M.IsTight) (n : ℕ) : M.stringMeasure {y | n ≤ y.length} = M.survival n := by
  rw [← Measure.tsum_measure_setOf_prefix_length, survival]
  exact tsum_congr fun x ↦ hM.stringMeasure_setOf_prefix x.1

/-- The expected length of the generated string is at most the total survival after the first
step. -/
theorem lintegral_length_le :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure ≤ ∑' n, M.survival (n + 1) := by
  rw [lintegral_natCast_eq_tsum_measure_lt .of_discrete]
  exact ENNReal.tsum_le_tsum fun n ↦ M.stringMeasure_setOf_length_le (n + 1)

/-- In a tight model the expected length is the total survival after the first step. -/
theorem IsTight.lintegral_length {M : AutoregressiveSequenceModel α} (hM : M.IsTight) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure = ∑' n, M.survival (n + 1) := by
  rw [lintegral_natCast_eq_tsum_measure_lt .of_discrete]
  exact tsum_congr fun n ↦ hM.stringMeasure_setOf_length_le (n + 1)

/-- In a tight model the prefix probabilities sum to the expected length plus one, the
normalizing constant of the prefix distribution ([opedal-chodroff-cotterell-wilcox-2024],
Proposition 1). -/
theorem IsTight.tsum_prefixProb {M : AutoregressiveSequenceModel α} (hM : M.IsTight) :
    ∑' x, M.prefixProb x = ∫⁻ x, (x.length : ℝ≥0∞) + 1 ∂M.stringMeasure := by
  rw [← Measure.tsum_measure_setOf_prefix]
  exact tsum_congr fun x ↦ (hM.stringMeasure_setOf_prefix x).symm

/-- An end probability of at least `c` after every prefix bounds the expected length by
`(1 - c) / c`. -/
theorem lintegral_length_le_div {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) :
    ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure ≤ (1 - c) / c := by
  have hc1 : c ≤ 1 := (hc []).trans prob_le_one
  calc ∫⁻ x, (x.length : ℝ≥0∞) ∂M.stringMeasure
      ≤ ∑' n, M.survival (n + 1) := M.lintegral_length_le
    _ ≤ ∑' n, (1 - c) ^ (n + 1) := ENNReal.tsum_le_tsum fun n ↦ M.survival_le_pow hc (n + 1)
    _ = (1 - c) / c := by
        simp_rw [pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1, div_eq_mul_inv]

end AutoregressiveSequenceModel
