/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.UniformOn

/-!
# Kernels from weight functions

This file defines `ProbabilityTheory.Kernel.ofWeights`, the kernel that normalizes a nonnegative
weight function on a finite target: its measure at `a` is the weighted sum of Dirac measures
`∑ b, w a b • dirac b` conditioned on the whole space, so a point has mass
`w a b / ∑ b', w a b'`. Weights of zero or infinite total give the zero measure, so the kernel is
always finite, and its measure at `a` is a probability measure exactly when some weight there is
nonzero and all are finite. Comparing the masses of two points compares their weights, and
rescaling the weights by a positive finite constant leaves the measure unchanged.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private theorem uniformOn_mul_uniformOn_apply_singleton [MeasurableSingletonClass β] [DecidableEq β]
    (A B : Finset β) (b : β) :
    uniformOn ↑A {b} * uniformOn ↑B {b} =
      if b ∈ A ∩ B then ((A.card : ℝ≥0∞) * B.card)⁻¹ else 0 := by
  rw [← Finset.coe_singleton, uniformOn_apply_finset, uniformOn_apply_finset]
  by_cases hA : b ∈ A <;> by_cases hB : b ∈ B <;>
    simp [Finset.inter_singleton_of_notMem, hA, hB, ENNReal.mul_inv, div_eq_mul_inv]

variable [Countable α] [MeasurableSingletonClass α] [Fintype β]

/-- The kernel that normalizes a nonnegative weight function on a finite target. Its measure at
`a` is the probability measure proportional to `w a`, and the zero measure when the weights there
have zero or infinite total. -/
noncomputable def ofWeights (w : α → β → ℝ≥0∞) : Kernel α β :=
  ofFunOfCountable fun a ↦ (∑ b, w a b • Measure.dirac b)[|Set.univ]

theorem ofWeights_apply (w : α → β → ℝ≥0∞) (a : α) :
    ofWeights w a = (∑ b, w a b • Measure.dirac b)[|Set.univ] :=
  rfl

theorem ofWeights_apply_univ (w : α → β → ℝ≥0∞) (a : α) :
    ofWeights w a Set.univ = (∑ b, w a b)⁻¹ * ∑ b, w a b := by
  simp [ofWeights_apply, cond]

instance (w : α → β → ℝ≥0∞) (a : α) : IsZeroOrProbabilityMeasure (ofWeights w a) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure (∑ b, w a b • Measure.dirac b)[|Set.univ])

instance (w : α → β → ℝ≥0∞) : IsFiniteKernel (ofWeights w) :=
  ⟨⟨1, ENNReal.one_lt_top, fun _ ↦ prob_le_one⟩⟩

/-- The measure at `a` is a probability measure exactly when some weight there is nonzero and all
are finite. -/
theorem isProbabilityMeasure_ofWeights_iff {w : α → β → ℝ≥0∞} {a : α} :
    IsProbabilityMeasure (ofWeights w a) ↔ (∃ b, w a b ≠ 0) ∧ ∀ b, w a b ≠ ∞ := by
  rw [isProbabilityMeasure_iff, ofWeights_apply_univ]
  have h0 : (∃ b, w a b ≠ 0) ↔ ∑ b, w a b ≠ 0 := by simp
  have htop : (∀ b, w a b ≠ ∞) ↔ ∑ b, w a b ≠ ∞ := by simp
  rw [h0, htop]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ ENNReal.inv_mul_cancel h.1 h.2⟩ <;> rintro h' <;>
    simp [h'] at h

theorem isProbabilityMeasure_ofWeights {w : α → β → ℝ≥0∞} {a : α} (h0 : ∃ b, w a b ≠ 0)
    (htop : ∀ b, w a b ≠ ∞) : IsProbabilityMeasure (ofWeights w a) :=
  isProbabilityMeasure_ofWeights_iff.2 ⟨h0, htop⟩

theorem isMarkovKernel_ofWeights {w : α → β → ℝ≥0∞}
    (h0 : ∀ a, ∃ b, w a b ≠ 0) (htop : ∀ a b, w a b ≠ ∞) :
    IsMarkovKernel (ofWeights w) :=
  ⟨fun a ↦ isProbabilityMeasure_ofWeights (h0 a) (htop a)⟩

variable [MeasurableSingletonClass β]

@[simp] theorem ofWeights_apply_singleton (w : α → β → ℝ≥0∞) (a : α) (b : β) :
    ofWeights w a {b} = w a b / ∑ b', w a b' := by
  rw [ofWeights_apply, cond_apply .univ, Set.univ_inter, Measure.finsetSum_smul_dirac_singleton,
    ← Finset.coe_univ, Measure.finsetSum_smul_dirac_apply_finset, ENNReal.div_eq_inv_mul]

theorem ofWeights_apply_singleton_eq_zero {w : α → β → ℝ≥0∞} {a : α} {b : β} (h : w a b = 0) :
    ofWeights w a {b} = 0 := by
  rw [ofWeights_apply_singleton, h, ENNReal.zero_div]

theorem ofWeights_apply_singleton_ne_zero {w : α → β → ℝ≥0∞} {a : α} {b : β} (h : w a b ≠ 0)
    (htop : ∀ c, w a c ≠ ∞) : ofWeights w a {b} ≠ 0 := by
  rw [ofWeights_apply_singleton, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨h, ENNReal.sum_ne_top.mpr fun c _ ↦ htop c⟩

/-- The least weight gets at most the uniform share. -/
theorem ofWeights_apply_singleton_le_inv_card {w : α → β → ℝ≥0∞} {a : α} {b : β}
    (h : ∀ c, w a b ≤ w a c) : ofWeights w a {b} ≤ (Fintype.card β : ℝ≥0∞)⁻¹ := by
  have : Nonempty β := ⟨b⟩
  have hsum : (Fintype.card β : ℝ≥0∞) * w a b ≤ ∑ c, w a c := by
    simpa using Finset.card_nsmul_le_sum Finset.univ (w a) (w a b) fun c _ ↦ h c
  rw [ofWeights_apply_singleton]
  refine ENNReal.div_le_of_le_mul ?_
  calc w a b = (Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card β * w a b) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ c, w a c := by gcongr

/-- The greatest weight gets at least the uniform share. -/
theorem inv_card_le_ofWeights_apply_singleton {w : α → β → ℝ≥0∞} {a : α} {b : β}
    (h : ∀ c, w a c ≤ w a b) (h0 : ∑ c, w a c ≠ 0) (htop : ∑ c, w a c ≠ ∞) :
    (Fintype.card β : ℝ≥0∞)⁻¹ ≤ ofWeights w a {b} := by
  have : Nonempty β := ⟨b⟩
  have hsum : ∑ c, w a c ≤ (Fintype.card β : ℝ≥0∞) * w a b := by
    simpa using Finset.sum_le_card_nsmul Finset.univ (w a) (w a b) fun c _ ↦ h c
  rw [ofWeights_apply_singleton, ENNReal.le_div_iff_mul_le (.inl h0) (.inl htop)]
  calc (Fintype.card β : ℝ≥0∞)⁻¹ * ∑ c, w a c
      ≤ (Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card β * w a b) := by gcongr
    _ = w a b := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]

theorem isProbabilityMeasure_ofWeights_of_absolutelyContinuous {w : α → β → ℝ≥0∞} {a : α}
    {μ : Measure β} [NeZero μ] (htop : ∀ b, w a b ≠ ∞) (hμ : μ ≪ ofWeights w a) :
    IsProbabilityMeasure (ofWeights w a) := by
  obtain ⟨b, hb⟩ := Measure.exists_measure_singleton_ne_zero μ
  exact isProbabilityMeasure_ofWeights
    ⟨b, fun h ↦ hb (hμ (ofWeights_apply_singleton_eq_zero h))⟩ htop

/-- Rescaling the weights by a positive finite constant leaves the measure unchanged. -/
theorem ofWeights_apply_eq_of_mul {w w' : α → β → ℝ≥0∞} {a a' : α} {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) (h : ∀ b, w' a' b = w a b * c) : ofWeights w' a' = ofWeights w a :=
  Measure.ext_of_singleton fun b ↦ by
    simp only [ofWeights_apply_singleton, h, ← Finset.sum_mul, ENNReal.mul_div_mul_right _ _ hc0 hc]

theorem ofWeights_eq_of_mul {w w' : α → β → ℝ≥0∞} {c : α → ℝ≥0∞} (hc0 : ∀ a, c a ≠ 0)
    (hc : ∀ a, c a ≠ ∞) (h : ∀ a b, w' a b = w a b * c a) : ofWeights w' = ofWeights w :=
  Kernel.ext fun a ↦ ofWeights_apply_eq_of_mul (hc0 a) (hc a) (h a)

theorem ofWeights_real_singleton_of_pair {w : α → β → ℝ≥0∞} (a : α) {b b' : β} (hbb' : b ≠ b')
    (htop : ∀ c, w a c ≠ ∞) (hsupp : ∀ c, w a c ≠ 0 → c = b ∨ c = b') :
    (ofWeights w a).real {b} = (w a b).toReal / ((w a b).toReal + (w a b').toReal) := by
  rw [measureReal_def, ofWeights_apply_singleton,
    Fintype.sum_eq_add b b' hbb' (fun c hc ↦ of_not_not (mt (hsupp c) (not_or.mpr hc))),
    ENNReal.toReal_div, ENNReal.toReal_add (htop b) (htop b')]

/-- Weights that vanish away from one point, where the weight is positive and finite, give the
Dirac measure there. -/
theorem ofWeights_apply_eq_dirac {w : α → β → ℝ≥0∞} {a : α} {b₀ : β} (h0 : w a b₀ ≠ 0)
    (htop : w a b₀ ≠ ∞) (h : ∀ b, b ≠ b₀ → w a b = 0) : ofWeights w a = Measure.dirac b₀ := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [ofWeights_apply_singleton, Fintype.sum_eq_single b₀ h]
  rcases eq_or_ne b b₀ with rfl | hb
  · rw [ENNReal.div_self h0 htop, Measure.dirac_apply_of_mem (Set.mem_singleton b)]
  · rw [h b hb, ENNReal.zero_div, Measure.dirac_apply' _ (.singleton b),
      Set.indicator_of_notMem (Set.notMem_singleton_iff.2 hb.symm)]

/-- A finite set has the total weight of its points over the total weight. -/
theorem ofWeights_apply_finset (w : α → β → ℝ≥0∞) (a : α) (E : Finset β) :
    ofWeights w a ↑E = (∑ b ∈ E, w a b) / ∑ b, w a b := by
  rw [← sum_measure_singleton, div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by rw [ofWeights_apply_singleton, div_eq_mul_inv]

theorem ofWeights_apply_setOf_eq_zero (w : α → β → ℝ≥0∞) (a : α) :
    ofWeights w a {b | w a b = 0} = 0 := by
  rw [show {b | w a b = 0} = ↑(Finset.univ.filter fun b ↦ w a b = 0) by ext; simp,
    ofWeights_apply_finset, Finset.sum_filter, Finset.sum_eq_zero fun b _ ↦ ?_, ENNReal.zero_div]
  split_ifs with h <;> simp [h]

theorem ofWeights_real_finset (w : α → β → ℝ≥0∞) (a : α) (hw : ∀ b, w a b ≠ ∞) (E : Finset β) :
    (ofWeights w a).real ↑E = (∑ b ∈ E, (w a b).toReal) / ∑ b, (w a b).toReal := by
  rw [measureReal_def, ofWeights_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_sum fun b _ ↦ hw b, ENNReal.toReal_sum fun b _ ↦ hw b]

theorem ofWeights_real_singleton (w : α → β → ℝ≥0∞) (a : α) (hw : ∀ b, w a b ≠ ∞) (b : β) :
    (ofWeights w a).real {b} = (w a b).toReal / ∑ b', (w a b').toReal := by
  rw [← Finset.coe_singleton, ofWeights_real_finset w a hw, Finset.sum_singleton]

/-- With finite weights, the real mass of a decidable event is the total weight of its points over
the total weight. -/
theorem ofWeights_real_setOf (w : α → β → ℝ≥0∞) (a : α) (hw : ∀ b, w a b ≠ ∞) (p : β → Prop)
    [DecidablePred p] :
    (ofWeights w a).real {b | p b} = (∑ b with p b, (w a b).toReal) / ∑ b, (w a b).toReal := by
  rw [show {b | p b} = (↑(Finset.univ.filter p) : Set β) by ext b; simp,
    ofWeights_real_finset w a hw]

/-- Comparing the masses of two points compares their weights, since the normalization
cancels. -/
theorem ofWeights_apply_singleton_lt_iff {w : α → β → ℝ≥0∞} (a : α) (htop : ∀ b, w a b ≠ ∞)
    {b₁ b₂ : β} : ofWeights w a {b₁} < ofWeights w a {b₂} ↔ w a b₁ < w a b₂ := by
  rw [ofWeights_apply_singleton, ofWeights_apply_singleton]
  rcases eq_or_ne (∑ b, w a b) 0 with h0 | h0
  · simp [Finset.sum_eq_zero_iff.1 h0 _ (Finset.mem_univ _)]
  · exact ENNReal.div_lt_div_iff_left h0 (ENNReal.sum_ne_top.2 fun b _ ↦ htop b)

theorem ofWeights_real_singleton_lt_iff {w : α → β → ℝ≥0∞} (a : α) (htop : ∀ b, w a b ≠ ∞)
    {b₁ b₂ : β} : (ofWeights w a).real {b₁} < (ofWeights w a).real {b₂} ↔ w a b₁ < w a b₂ := by
  rw [measureReal_def, measureReal_def,
    ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    ofWeights_apply_singleton_lt_iff a htop]

/-- The product of two uniform experts is uniform on their agreement set, and collapses to the
zero measure when they agree nowhere. -/
theorem ofWeights_uniformOn_mul_uniformOn [DecidableEq β] (A B : α → Finset β) (a : α) :
    ofWeights (fun a b ↦ uniformOn ↑(A a) {b} * uniformOn ↑(B a) {b}) a =
      uniformOn (↑(A a ∩ B a) : Set β) := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [ofWeights_apply_singleton]
  simp only [uniformOn_mul_uniformOn_apply_singleton, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.coe_singleton, uniformOn_apply_finset]
  by_cases hb : b ∈ A a ∩ B a
  · have hK : ((A a).card : ℝ≥0∞) * (B a).card ≠ 0 := by
      have := Finset.mem_inter.mp hb
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨b, this.1⟩).ne')
        (Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨b, this.2⟩).ne')
    have hK' : ((A a).card : ℝ≥0∞) * (B a).card ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
    rw [ite_eq_left hb, Finset.inter_singleton_of_mem hb, Finset.card_singleton, Nat.cast_one,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hK))
        (Or.inl (ENNReal.natCast_ne_top _)), inv_inv, mul_assoc,
      ENNReal.mul_inv_cancel hK hK', mul_one, one_div]
  · rw [ite_eq_right hb, Finset.inter_singleton_of_notMem hb, Finset.card_empty, Nat.cast_zero,
      ENNReal.zero_div, ENNReal.zero_div]

end ProbabilityTheory.Kernel
