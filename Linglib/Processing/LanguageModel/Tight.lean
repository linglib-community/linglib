/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Log.Summable
public import Linglib.Core.MeasureTheory.Measure.Basic
public import Linglib.Processing.LanguageModel.Autoregressive

/-!
# Tight autoregressive sequence models

Survival is the probability that no end symbol appears in the first `n` steps. The string
probabilities and the limit of survival [sum to one](##tsum_stringProb_add_iInf_survival), so a
model is tight [exactly when survival tends to zero](##isTight_iff_tendsto_survival), and since
survival is [the product](##survival_eq_prod) of one minus the conditional end probability at each
step, [exactly when](##isTight_iff) that probability reaches one or has a divergent sum. In a tight
model the strings extending a prefix have
[total probability its prefix probability](##IsTight.stringMeasure_cylinder), the conditionals
are [the next-symbol laws](##IsTight.next_ofMeasure_stringMeasure) of the string law, the model
after a prefix [generates the continuation](##IsTight.continuation_stringMeasure), and the
expected length is [the total survival](##IsTight.lintegral_length) after the first step.

## Implementation notes

* The product criterion behind `isTight_iff` is `ENNReal.hasProd_one_sub_zero_iff`,
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
  rw [← measure_range_eq_tsum (Option.some_injective α),
    measure_singleton_none_add_measure_range_some, measure_univ]

theorem survival_succ_add_stopProb (n : ℕ) : M.survival (n + 1) + M.stopProb n = M.survival n := by
  rw [survival, ← (concatEquiv n).tsum_eq, ENNReal.tsum_prod', stopProb, survival,
    ← ENNReal.tsum_add]
  refine tsum_congr fun x ↦ ?_
  simp only [concatEquiv, Equiv.coe_fn_mk, prefixProb_concat, ENNReal.tsum_mul_left, stringProb,
    ← mul_add, add_comm (∑' a, _), next_none_add_tsum_next_some, mul_one]

theorem survival_antitone : Antitone M.survival :=
  antitone_nat_of_succ_le fun n ↦ (M.survival_succ_add_stopProb n).le.trans' le_self_add

theorem survival_le_one (n : ℕ) : M.survival n ≤ 1 :=
  (M.survival_antitone n.zero_le).trans_eq M.survival_zero

theorem survival_ne_top (n : ℕ) : M.survival n ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.survival_le_one n)

/-- The probability of a string of length `n` is the drop in survival at step `n`. -/
theorem stopProb_eq_sub (n : ℕ) : M.stopProb n = M.survival n - M.survival (n + 1) :=
  ENNReal.eq_sub_of_add_eq (M.survival_ne_top _)
    ((add_comm _ _).trans (M.survival_succ_add_stopProb n))

theorem stopProb_le_survival (n : ℕ) : M.stopProb n ≤ M.survival n :=
  (M.survival_succ_add_stopProb n).le.trans' le_add_self

theorem survival_succ_eq_sub (n : ℕ) : M.survival (n + 1) = M.survival n - M.stopProb n :=
  ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top (M.survival_ne_top n) (M.stopProb_le_survival n))
    (M.survival_succ_add_stopProb n)

theorem sum_range_stopProb_add_survival (n : ℕ) :
    ∑ k ∈ range n, M.stopProb k + M.survival n = 1 := by
  simp_rw [stopProb_eq_sub]
  exact (ENNReal.sum_range_sub_succ_add M.survival_antitone n).trans M.survival_zero

/-- The string probabilities and the limit of survival sum to one: the mass a model does not give
to strings is the probability of never ending. -/
theorem tsum_stringProb_add_iInf_survival : ∑' x, M.stringProb x + ⨅ n, M.survival n = 1 := by
  rw [tsum_stringProb]
  simp_rw [stopProb_eq_sub]
  exact (ENNReal.tsum_sub_succ_add_iInf M.survival_antitone (by simp)).trans M.survival_zero

theorem isTight_iff_iInf_survival_eq_zero : M.IsTight ↔ ⨅ n, M.survival n = 0 := by
  have h := M.tsum_stringProb_add_iInf_survival
  refine ⟨fun hM ↦ ?_, fun h0 ↦ by rwa [h0, add_zero] at h⟩
  rw [show ∑' x, M.stringProb x = 1 from hM] at h
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (h.trans (add_zero 1).symm)

theorem isTight_iff_tendsto_survival : M.IsTight ↔ Tendsto M.survival atTop (𝓝 0) := by
  have h := tendsto_atTop_iInf M.survival_antitone
  rw [isTight_iff_iInf_survival_eq_zero]
  exact ⟨fun h0 ↦ h0 ▸ h, tendsto_nhds_unique h⟩

/-- A model whose strings all end within `n` symbols is tight. -/
theorem isTight_of_survival_eq_zero {n : ℕ} (h : M.survival n = 0) : M.IsTight :=
  M.isTight_iff_tendsto_survival.2 (tendsto_atTop_of_eventually_const (i₀ := n) fun _ hm ↦
    nonpos_iff_eq_zero.1 (h ▸ M.survival_antitone hm))

/-! ### The conditional end probability -/

theorem eosHazard_le_one (n : ℕ) : M.eosHazard n ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact M.stopProb_le_survival n)

theorem survival_succ (n : ℕ) : M.survival (n + 1) = M.survival n * (1 - M.eosHazard n) := by
  rw [eosHazard, stopProb_eq_sub, ENNReal.mul_one_sub_sub_succ_div M.survival_antitone (by simp)]

theorem survival_eq_prod (n : ℕ) : M.survival n = ∏ k ∈ range n, (1 - M.eosHazard k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [survival_succ, ih, prod_range_succ]

/-- The probability of never ending is the product of one minus the conditional end
probabilities. -/
theorem iInf_survival_eq_tprod : ⨅ n, M.survival n = ∏' n, (1 - M.eosHazard n) :=
  tendsto_nhds_unique (tendsto_atTop_iInf M.survival_antitone) <| by
    simpa only [← survival_eq_prod] using (ENNReal.multipliable_of_le_one
      fun n ↦ tsub_le_self (a := 1) (b := M.eosHazard n)).hasProd.tendsto_prod_nat

/-- A model is tight exactly when the conditional end probability reaches one or has a divergent
sum ([du-etal-2023], Theorem 4.7). -/
theorem isTight_iff : M.IsTight ↔ (∃ n, M.eosHazard n = 1) ∨ ∑' n, M.eosHazard n = ∞ := by
  rw [isTight_iff_iInf_survival_eq_zero, iInf_survival_eq_tprod,
    ← (ENNReal.multipliable_of_le_one fun _ ↦ tsub_le_self).hasProd_iff,
    ENNReal.hasProd_one_sub_zero_iff]
  simp_rw [(M.eosHazard_le_one _).ge_iff_eq]

/-- An end probability of at least `c n` after every prefix of length `n` bounds survival by the
product of the `1 - c n`. -/
theorem survival_le_prod {c : ℕ → ℝ≥0∞} (hc : ∀ x : List α, c x.length ≤ M.next x {none})
    (n : ℕ) : M.survival n ≤ ∏ k ∈ range n, (1 - c k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstop := M.mul_survival_le_stopProb (n := n) fun x hx ↦ hx ▸ hc x
    rw [prod_range_succ, survival_succ_eq_sub]
    calc M.survival n - M.stopProb n ≤ M.survival n - c n * M.survival n :=
          tsub_le_tsub_left hstop _
      _ = M.survival n * (1 - c n) := by
        rw [ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]
      _ ≤ _ := by gcongr

/-- A model whose end probability after every prefix of length `n` is at least `c n`, with the
`c n` of infinite sum, is tight ([du-etal-2023], Proposition 4.3). -/
theorem isTight_of_le_next_none {c : ℕ → ℝ≥0∞}
    (hc : ∀ x : List α, c x.length ≤ M.next x {none}) (h : ∑' n, c n = ∞) : M.IsTight :=
  M.isTight_iff_tendsto_survival.2 <| tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (ENNReal.hasProd_one_sub_zero_iff.2 (.inr h)).tendsto_prod_nat
    (fun _ ↦ zero_le) (M.survival_le_prod hc)

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
    rw [prod_range_succ, ← ih, survival_succ_eq_sub, hstop,
      ENNReal.mul_sub fun _ _ ↦ M.survival_ne_top n, mul_one, mul_comm]

/-- When the end probability after a prefix depends only on its length, the model is tight exactly
when that probability reaches one or has a divergent sum. -/
theorem isTight_iff_of_next_none_eq {e : ℕ → ℝ≥0∞}
    (he : ∀ x : List α, M.next x {none} = e x.length) (he1 : ∀ n, e n ≤ 1) :
    M.IsTight ↔ (∃ n, e n = 1) ∨ ∑' n, e n = ∞ := by
  rw [isTight_iff_tendsto_survival, funext (M.survival_eq_prod_of_next_none_eq he),
    ← ENNReal.hasProd_iff_tendsto_nat fun _ ↦ tsub_le_self, ENNReal.hasProd_one_sub_zero_iff]
  simp_rw [(he1 _).ge_iff_eq]

/-- An end probability of at least `c` after every prefix makes survival decay geometrically. -/
theorem survival_le_pow {c : ℝ≥0∞} (hc : ∀ x : List α, c ≤ M.next x {none}) (n : ℕ) :
    M.survival n ≤ (1 - c) ^ n := by
  simpa using M.survival_le_prod (c := fun _ ↦ c) hc n

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
theorem IsTight.stringMeasure_cylinder {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    (x : List α) : M.stringMeasure x.cylinder = M.prefixProb x := by
  rw [M.stringMeasure_cylinder]
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
    rw [next_ofMeasure_apply_some,
      cond_apply_of_subset .of_discrete (x.cylinder_append_subset [a]),
      hM.stringMeasure_cylinder, hM.stringMeasure_cylinder, prefixProb_concat,
      mul_comm (M.prefixProb x), ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]
  | none =>
    rw [next_ofMeasure_apply_none _ (by rwa [hM.stringMeasure_cylinder]),
      cond_apply_of_subset .of_discrete x.singleton_subset_cylinder, stringMeasure_singleton,
      hM.stringMeasure_cylinder, stringProb, mul_comm (M.prefixProb x),
      ENNReal.mul_div_cancel_right hx (M.prefixProb_ne_top x)]

/-- In a tight model the continuation of the string law after a prefix of positive probability is
the string law of the model after the prefix. -/
theorem IsTight.continuation_stringMeasure {M : AutoregressiveSequenceModel α} (hM : M.IsTight)
    {x : List α} (hx : M.prefixProb x ≠ 0) :
    M.stringMeasure.continuation x = (M.after x).stringMeasure := by
  have := M.isTight_iff_isProbabilityMeasure.1 hM
  have := M.stringMeasure.isProbabilityMeasure_continuation
    (by rwa [hM.stringMeasure_cylinder] : M.stringMeasure x.cylinder ≠ 0)
  refine (stringMeasure_eq_of_next_eq fun u hu ↦ ?_).symm
  rw [ofMeasure_continuation, next_after, next_after, hM.next_ofMeasure_stringMeasure]
  refine fun h0 ↦ hu ?_
  rw [Measure.continuation_cylinder,
    cond_apply_of_subset .of_discrete (x.cylinder_append_subset u),
    hM.stringMeasure_cylinder, h0, ENNReal.zero_div]

/-! ### Expected length

The law of the generated string is a sum of point masses, so an integral against it is a sum
weighted by the string probabilities. Survival to `n` is at least the probability of a string of
length at least `n`, with equality in a tight model, so the tail-sum formula bounds the expected
length by the total survival after the first step. -/

/-- Survival to `n` is at least the probability of a string of length at least `n`. -/
theorem stringMeasure_setOf_length_le (n : ℕ) :
    M.stringMeasure {y | n ≤ y.length} ≤ M.survival n := by
  rw [← Measure.tsum_measure_cylinder_length, survival]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  rw [M.stringMeasure_cylinder]
  exact mul_le_of_le_one_right' (M.after x.1).tsum_stringProb_le_one

/-- In a tight model survival to `n` is the probability of a string of length at least `n`. -/
theorem IsTight.stringMeasure_setOf_length_le {M : AutoregressiveSequenceModel α}
    (hM : M.IsTight) (n : ℕ) : M.stringMeasure {y | n ≤ y.length} = M.survival n := by
  rw [← Measure.tsum_measure_cylinder_length, survival]
  exact tsum_congr fun x ↦ hM.stringMeasure_cylinder x.1

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
  rw [← Measure.tsum_measure_cylinder]
  exact tsum_congr fun x ↦ (hM.stringMeasure_cylinder x).symm

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
