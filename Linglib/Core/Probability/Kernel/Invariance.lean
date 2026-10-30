/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Probability.Kernel.Composition.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Irreducible

/-!
# Invariant measures of kernels

This file adds to mathlib's `Kernel.Invariant` the facts about invariant measures that a Markov
chain on a finite state space needs. An invariant measure is carried along a map that intertwines
two kernels, and it is invariant for every power of its kernel. One step of a Markov kernel leaves
the mass of a set unchanged exactly when the flow out of the set balances the flow into it.

On a finite state space with measurable singletons, every Markov kernel has an invariant
probability measure. When the kernel is irreducible with respect to the counting measure, every
state reaching every state, it has exactly one, and that measure charges every state; conversely a
Markov kernel whose invariant probability measures all charge every state is irreducible.

## Main statements

* `ProbabilityTheory.Kernel.Invariant.map`: if `η (f a) = (κ a).map f` for all `a`, an invariant
  measure of `κ` maps along `f` to an invariant measure of `η`.
* `ProbabilityTheory.Kernel.comp_apply_eq_iff_setLIntegral_compl`: `(κ ∘ₘ μ) s = μ s` exactly
  when `∫⁻ a in s, κ a sᶜ ∂μ = ∫⁻ a in sᶜ, κ a s ∂μ`.
* `ProbabilityTheory.Kernel.isIrreducible_count_iff`: irreducibility with respect to the counting
  measure is reachability of every point from every point.
* `ProbabilityTheory.Kernel.exists_isProbabilityMeasure_invariant`: on a finite type, a Markov
  kernel has an invariant probability measure.
* `ProbabilityTheory.Kernel.Invariant.eq_of_isIrreducible`,
  `ProbabilityTheory.Kernel.Invariant.measure_singleton_ne_zero`: an irreducible kernel on a finite
  type has at most one invariant probability measure, and a nonzero invariant measure charges
  every point.
* `ProbabilityTheory.Kernel.isIrreducible_count_of_measure_singleton_ne_zero`: a Markov kernel on
  a finite type whose invariant probability measures all charge every point is irreducible.

## Implementation notes

The existence proof is linear algebra rather than compactness: the transition matrix `P` fixes the
constant vector, so `P - 1` is singular and has a nonzero left null vector, whose absolute value
is a nonnegative fixed vector. Uniqueness is the minimum-ratio argument: subtracting from one
invariant law the largest multiple of another that stays nonnegative leaves an invariant measure
that vanishes at a point, hence everywhere. Neither needs the Perron–Frobenius theorem.
`[UPSTREAM]` candidate for `Mathlib/Probability/Kernel/Invariance.lean`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α α}
  {μ ν : Measure α}

/-- An invariant measure of `κ` maps along `f` to an invariant measure of `η` when `η` moves the
image of a point as `κ` moves the point. -/
theorem Invariant.map {η : Kernel β β} {f : α → β} (hf : Measurable f)
    (h : ∀ a, η (f a) = (κ a).map f) (hμ : κ.Invariant μ) : η.Invariant (μ.map f) := by
  rw [Invariant, Measure.bind_map hf.aemeasurable η.measurable.aemeasurable]
  simp_rw [h]
  rw [← Measure.map_bind κ.measurable.aemeasurable hf.aemeasurable, hμ.def]

theorem Invariant.pow (hμ : κ.Invariant μ) : ∀ n, (κ ^ n).Invariant μ
  | 0 => by rw [pow_zero, one_def]; exact Measure.id_comp
  | n + 1 => by rw [pow_succ, mul_def]; exact (hμ.pow n).comp hμ

/-- One step of a Markov kernel leaves the mass of a set unchanged exactly when the flow out of the
set balances the flow into it. -/
theorem comp_apply_eq_iff_setLIntegral_compl [IsMarkovKernel κ] [IsFiniteMeasure μ] {s : Set α}
    (hs : MeasurableSet s) :
    (κ ∘ₘ μ) s = μ s ↔ ∫⁻ a in s, κ a sᶜ ∂μ = ∫⁻ a in sᶜ, κ a s ∂μ := by
  have h₁ : (κ ∘ₘ μ) s = ∫⁻ a in s, κ a s ∂μ + ∫⁻ a in sᶜ, κ a s ∂μ := by
    rw [Measure.bind_apply hs κ.aemeasurable, lintegral_add_compl _ hs]
  have h₂ : μ s = ∫⁻ a in s, κ a s ∂μ + ∫⁻ a in s, κ a sᶜ ∂μ := by
    rw [← lintegral_add_left (κ.measurable_coe hs)]
    simp_rw [prob_add_prob_compl hs]
    exact (setLIntegral_one s).symm
  have hfin : ∫⁻ a in s, κ a s ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ne_top μ s) (h₂ ▸ le_self_add)
  rw [h₁, h₂, ENNReal.add_right_inj hfin, eq_comm]

/-- The flow of an invariant measure out of a set balances the flow into it. -/
theorem Invariant.setLIntegral_compl [IsMarkovKernel κ] [IsFiniteMeasure μ] (hμ : κ.Invariant μ)
    {s : Set α} (hs : MeasurableSet s) : ∫⁻ a in s, κ a sᶜ ∂μ = ∫⁻ a in sᶜ, κ a s ∂μ :=
  (comp_apply_eq_iff_setLIntegral_compl hs).1 (by rw [hμ.def])

/-- A path to `b` in `n` steps followed by a step from `b` to `c` reaches `c` in `n + 1` steps. -/
theorem pow_succ_apply_singleton_ne_zero [MeasurableSingletonClass α] {n : ℕ} {a b c : α}
    (hab : (κ ^ n) a {b} ≠ 0) (hbc : κ b {c} ≠ 0) : (κ ^ (n + 1)) a {c} ≠ 0 := by
  rw [pow_succ', mul_def, comp_apply]
  exact Measure.comp_apply_singleton_ne_zero κ _ hab hbc

/-- On a space with measurable singletons, `κ` is irreducible with respect to the counting measure
when every point is reached from every point. -/
theorem isIrreducible_count_iff [MeasurableSingletonClass α] :
    IsIrreducible Measure.count κ ↔ ∀ a b, ∃ n, (κ ^ n) a {b} ≠ 0 := by
  refine ⟨fun h a b ↦ ?_, fun h ↦ ⟨fun A hA hφA a ↦ ?_⟩⟩
  · obtain ⟨n, hn⟩ := h.irreducible (measurableSet_singleton b) (by simp) a
    exact ⟨n, hn.ne'⟩
  · obtain ⟨b, hb⟩ : A.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦ by simp [h] at hφA
    obtain ⟨n, hn⟩ := h a b
    exact ⟨n, (pos_iff_ne_zero.2 hn).trans_le (measure_mono (Set.singleton_subset_iff.2 hb))⟩

/-- A nonzero invariant measure of an irreducible kernel charges every point. -/
theorem Invariant.measure_singleton_ne_zero [MeasurableSingletonClass α] [Countable α]
    [IsIrreducible Measure.count κ] (hμ : κ.Invariant μ) (hμ0 : μ ≠ 0) (a : α) : μ {a} ≠ 0 := by
  have : NeZero μ := ⟨hμ0⟩
  obtain ⟨b, hb⟩ := Measure.exists_measure_singleton_ne_zero μ
  obtain ⟨n, hn⟩ := isIrreducible_count_iff.1 ‹_› b a
  rw [← (hμ.pow n).def]
  exact Measure.comp_apply_singleton_ne_zero _ _ hb hn

section Finite

variable [Fintype α] [MeasurableSingletonClass α]

/-- On a finite type, invariance is the system of equations `∑ a, μ {a} κ a {b} = μ {b}`. -/
theorem invariant_iff_forall_real_singleton [IsMarkovKernel κ] [IsFiniteMeasure μ] :
    κ.Invariant μ ↔ ∀ b, ∑ a, μ.real {a} * (κ a).real {b} = μ.real {b} := by
  refine ⟨fun h b ↦ ?_, fun h ↦ Measure.ext_of_singleton fun b ↦ ?_⟩
  · rw [← Measure.comp_real_singleton, h.def]
  · rw [← measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _),
      Measure.comp_real_singleton, h b]

private theorem sum_real_singleton (ρ : Measure α) [IsProbabilityMeasure ρ] :
    ∑ b, ρ.real {b} = 1 := by
  rw [sum_measureReal_singleton, coe_univ, probReal_univ]

/-- A Markov kernel on a finite type has an invariant probability measure. -/
theorem exists_isProbabilityMeasure_invariant [Nonempty α] (κ : Kernel α α) [IsMarkovKernel κ] :
    ∃ μ : Measure α, IsProbabilityMeasure μ ∧ κ.Invariant μ := by
  classical
  set P : Matrix α α ℝ := fun a b ↦ (κ a).real {b}
  have hP : ∀ a b, 0 ≤ P a b := fun _ _ ↦ measureReal_nonneg
  have hrow : ∀ a, ∑ b, P a b = 1 := fun a ↦ sum_real_singleton (κ a)
  have hdet : (P - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1
    ⟨fun _ ↦ 1, one_ne_zero, by ext a; simp [Matrix.mulVec, dotProduct, hrow, Matrix.one_apply]⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hv
  set w : α → ℝ := fun a ↦ |v a|
  have hle : ∀ b ∈ univ, w b ≤ ∑ a, w a * P a b := fun b _ ↦ by
    calc w b = |∑ a, v a * P a b| := by
          show |v b| = _; rw [show v b = ∑ a, v a * P a b from (congrFun hv b).symm]
      _ ≤ ∑ a, |v a * P a b| := abs_sum_le_sum_abs _ _
      _ = ∑ a, w a * P a b := by simp_rw [abs_mul, abs_of_nonneg (hP _ _)]; rfl
  have hsum : ∑ b, w b = ∑ b, ∑ a, w a * P a b := by
    rw [Finset.sum_comm]; simp_rw [← mul_sum, hrow, mul_one]
  have hw : ∀ b, ∑ a, w a * P a b = w b := fun b ↦
    ((sum_eq_sum_iff_of_le hle).1 hsum b (mem_univ b)).symm
  have hS : 0 < ∑ a, w a := by
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hv0
    exact sum_pos' (fun a _ ↦ abs_nonneg _) ⟨a, mem_univ a, abs_pos.2 ha⟩
  set u : α → ℝ := fun a ↦ w a / ∑ a, w a
  have hu : ∀ a, 0 ≤ u a := fun a ↦ div_nonneg (abs_nonneg _) hS.le
  have := Measure.isProbabilityMeasure_ofRealWeights hu (by rw [← sum_div, div_self hS.ne'])
  refine ⟨Measure.ofRealWeights u, this, invariant_iff_forall_real_singleton.2 fun b ↦ ?_⟩
  simp_rw [Measure.ofRealWeights_real_singleton hu]
  show ∑ a, w a / (∑ a, w a) * P a b = w b / ∑ a, w a
  rw [← hw b, sum_div]
  exact sum_congr rfl fun a _ ↦ div_mul_eq_mul_div _ _ _

/-- An irreducible Markov kernel on a finite type has at most one invariant probability measure. -/
theorem Invariant.eq_of_isIrreducible [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμ : κ.Invariant μ) (hν : κ.Invariant ν) :
    μ = ν := by
  have := nonempty_of_isProbabilityMeasure μ
  have hp a : 0 < μ.real {a} := ENNReal.toReal_pos
    (hμ.measure_singleton_ne_zero (IsProbabilityMeasure.ne_zero μ) a) (measure_ne_top _ _)
  obtain ⟨a₀, -, ha₀⟩ := exists_min_image univ (fun a ↦ ν.real {a} / μ.real {a}) univ_nonempty
  set c := ν.real {a₀} / μ.real {a₀}
  set w : α → ℝ := fun a ↦ ν.real {a} - c * μ.real {a}
  have hw a : 0 ≤ w a := sub_nonneg.2 ((le_div_iff₀ (hp a)).1 (ha₀ a (mem_univ a)))
  have hwa₀ : w a₀ = 0 := by simp only [w, c, div_mul_cancel₀ _ (hp a₀).ne', sub_self]
  have hwinv : κ.Invariant (Measure.ofRealWeights w) :=
    invariant_iff_forall_real_singleton.2 fun b ↦ by
      simp_rw [Measure.ofRealWeights_real_singleton hw]
      simp only [w, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
      rw [invariant_iff_forall_real_singleton.1 hν b, invariant_iff_forall_real_singleton.1 hμ b]
  have hw0 : ∀ a, w a = 0 := by
    by_contra! ⟨a, ha⟩
    refine hwinv.measure_singleton_ne_zero (fun h0 ↦ ?_) a₀ (by simp [Measure.ofRealWeights, hwa₀])
    have := congrArg (· {a}) h0
    simp only [Measure.ofRealWeights, Measure.ofWeights_apply_singleton, Measure.coe_zero,
      Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact ha (le_antisymm this (hw a))
  have hc : c = 1 := by
    have := sum_congr rfl fun a (_ : a ∈ univ) ↦ hw0 a
    simp only [w, sum_sub_distrib, ← mul_sum, sum_real_singleton, sum_const_zero] at this
    linarith
  refine (Measure.ext_of_singleton fun a ↦ ?_).symm
  rw [← measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)]
  linarith [hw0 a, show c * μ.real {a} = μ.real {a} by rw [hc, one_mul]]

/-- A Markov kernel on a finite type is irreducible when each of its invariant probability
measures charges every point. -/
theorem isIrreducible_count_of_measure_singleton_ne_zero [IsMarkovKernel κ]
    (h : ∀ μ : Measure α, IsProbabilityMeasure μ → κ.Invariant μ → ∀ a, μ {a} ≠ 0) :
    IsIrreducible Measure.count κ := by
  classical
  refine isIrreducible_count_iff.2 fun a b ↦ ?_
  by_contra! hab
  set R : Set α := {x | ∃ n, (κ ^ n) a {x} ≠ 0}
  have haR : a ∈ R := ⟨0, by simp [one_def, id_apply]⟩
  have hclosed : ∀ x ∈ R, ∀ y ∉ R, κ x {y} = 0 := fun x ⟨n, hn⟩ y hy ↦ by
    by_contra hxy
    exact hy ⟨n + 1, pow_succ_apply_singleton_ne_zero hn hxy⟩
  have hRm : MeasurableSet R := R.toFinite.measurableSet
  have : Nonempty α := ⟨a⟩
  obtain ⟨μ, hμp, hμ⟩ :=
    exists_isProbabilityMeasure_invariant (piecewise hRm κ (const α (Measure.dirac a)))
  have hout : ∀ y ∉ R, μ {y} = 0 := fun y hy ↦ by
    rw [← hμ.def, Measure.comp_apply_singleton]
    refine sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x ∈ R
    · simp [piecewise_apply, hx, hclosed x hx y hy]
    · have hay : a ∉ ({y} : Set α) := fun h ↦ hy (h ▸ haR)
      simp [piecewise_apply, hx, hay]
  have hRc : μ Rᶜ = 0 := (measure_null_iff_singleton Rᶜ.to_countable).2 hout
  have hκ : κ.Invariant μ := by
    have hae : ∀ᵐ x ∂μ, κ x = piecewise hRm κ (const α (Measure.dirac a)) x := ae_iff.2 <|
      measure_mono_null (t := Rᶜ) (fun x hx hxR ↦ hx (by simp [piecewise_apply, hxR])) hRc
    exact (Measure.comp_congr hae).trans hμ.def
  exact h μ hμp hκ b (hout b fun ⟨n, hn⟩ ↦ hn (hab n))

end Finite

end ProbabilityTheory.Kernel
