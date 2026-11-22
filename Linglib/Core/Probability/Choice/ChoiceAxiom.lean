/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Systems of choice probabilities and the choice axiom

A system of choice probabilities, `ProbabilityTheory.ChoiceFn`, assigns to every finite set `T` of
alternatives the distribution `P_T` of the alternative chosen from `T`. It has a ratio scale when
one measure with positive finite point masses gives every `P_T` by conditioning on `T`, so that
choice between two alternatives is `v x / (v x + v y)` for a positive scale `v`,
`ProbabilityTheory.pairwiseProb`.

A system with a ratio scale satisfies the constant-ratio rule, that every set containing two
alternatives gives them the odds of the pair, and the choice axiom. A system that gives every
alternative of every set positive probability has a ratio scale exactly when it satisfies the
constant-ratio rule (`ProbabilityTheory.ChoiceFn.hasRatioScale_iff_hasPairwiseIIA`).

## Implementation notes

A system of choice probabilities is a family of probability measures indexed by finite sets, so
the product rule of the choice axiom is conditioning (`ProbabilityTheory.cond`). The choice from a
singleton is that alternative, so `binary x x = 1`.

## References

* [luce-1959]
-/

@[expose] public section

namespace ProbabilityTheory

section ChoiceAxiom

open Finset Real

/-! ### Pairwise choice under a ratio scale

Under a ratio scale `v` the probability of choosing `x` over `y` is `v x / (v x + v y)`. The lemmas
assume positivity only at the alternatives involved, so they apply to scales defined on a local set.
-/

section PairwiseProb

variable {A : Type*} {v : A → ℝ} {x y z : A}

/-- Under the ratio scale `v`, `x` is chosen over `y` with probability `v x / (v x + v y)`. -/
noncomputable def pairwiseProb (v : A → ℝ) (x y : A) : ℝ :=
  v x / (v x + v y)

theorem pairwiseProb_complement (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y + pairwiseProb v y x = 1 := by
  rw [pairwiseProb, pairwiseProb, add_comm (v y), ← add_div,
    div_self (ne_of_gt (add_pos hx hy))]

theorem pairwiseProb_ge_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    1 / 2 ≤ pairwiseProb v x y ↔ v y ≤ v x := by
  rw [pairwiseProb, le_div_iff₀ (add_pos hx hy)]
  constructor <;> intro h <;> nlinarith

theorem pairwiseProb_eq_half_iff (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y = 1 / 2 ↔ v x = v y := by
  rw [pairwiseProb, div_eq_iff (ne_of_gt (add_pos hx hy))]
  constructor <;> intro h <;> linarith

theorem pairwiseProb_mono_iff (hx : 0 < v x) (hy : 0 < v y) (hz : 0 < v z) :
    pairwiseProb v y z ≤ pairwiseProb v x z ↔ v y ≤ v x := by
  rw [pairwiseProb, pairwiseProb,
    div_le_div_iff₀ (add_pos hy hz) (add_pos hx hz)]
  constructor <;> intro h <;> nlinarith

-- Definition 2, p. 25
theorem pairwiseProb_sst (hx : 0 < v x) (hy : 0 < v y) (hz : 0 < v z)
    (hxy : 1 / 2 ≤ pairwiseProb v x y) (hyz : 1 / 2 ≤ pairwiseProb v y z) :
    max (pairwiseProb v x y) (pairwiseProb v y z) ≤ pairwiseProb v x z := by
  rw [pairwiseProb_ge_half_iff hx hy] at hxy
  rw [pairwiseProb_ge_half_iff hy hz] at hyz
  refine max_le ?_ ((pairwiseProb_mono_iff hx hy hz).2 hxy)
  rw [pairwiseProb, pairwiseProb, div_le_div_iff₀ (add_pos hx hy) (add_pos hx hz)]
  nlinarith

theorem pairwiseProb_eq_pairwiseProb_iff {x' y' : A} (hx : 0 < v x)
    (hy : 0 < v y) (hx' : 0 < v x') (hy' : 0 < v y') :
    pairwiseProb v x y = pairwiseProb v x' y' ↔ v x * v y' = v x' * v y := by
  rw [pairwiseProb, pairwiseProb,
    div_eq_div_iff (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

-- §2
theorem pairwiseProb_eq_sigmoid (hx : 0 < v x) (hy : 0 < v y) :
    pairwiseProb v x y = Real.sigmoid (Real.log (v x) - Real.log (v y)) := by
  have := add_pos hx hy
  rw [← Real.log_div hx.ne' hy.ne', Real.sigmoid_log (div_pos hx hy), pairwiseProb]
  field_simp

theorem pairwiseProb_exp (u : A → ℝ) (x y : A) :
    pairwiseProb (fun a ↦ Real.exp (u a)) x y = Real.sigmoid (u x - u y) := by
  rw [pairwiseProb_eq_sigmoid (v := fun a ↦ Real.exp (u a)) (Real.exp_pos _) (Real.exp_pos _),
    Real.log_exp, Real.log_exp]

end PairwiseProb

/-! ### The ratio rule and conditional probability

A positive scale `v` gives each alternative `a` of a finite set `T` the choice probability
`v a / ∑ b ∈ T, v b` (Theorem 3, p. 23). Luce remarks that under the choice axiom `P_S` "acts like a
conditional probability relative to `P_T`" (p. 24), and for the ratio rule this holds literally. -/

section RatioRule

variable {A : Type*}

open MeasureTheory in
theorem withDensity_ofReal_finset [MeasurableSpace A] [MeasurableSingletonClass A] {v : A → ℝ}
    (hv : ∀ a, 0 ≤ v a) (E : Finset A) :
    (Measure.count.withDensity fun b ↦ ENNReal.ofReal (v b)) ↑E =
      ENNReal.ofReal (∑ b ∈ E, v b) := by
  rw [withDensity_apply _ E.measurableSet, lintegral_finset,
    ENNReal.ofReal_sum_of_nonneg fun b _ ↦ hv b]
  simp

variable [DecidableEq A]

/-- The ratio rule gives `a` the probability `v a / ∑ b ∈ T, v b` of being chosen from `T`, and `0`
if `a ∉ T`. -/
noncomputable def ratioProb (v : A → ℝ) (T : Finset A) (a : A) : ℝ :=
  if a ∈ T then v a / ∑ b ∈ T, v b else 0

theorem ratioProb_eq_div (v : A → ℝ) (T : Finset A) (a : A) (ha : a ∈ T) :
    ratioProb v T a = v a / ∑ b ∈ T, v b := by
  simp only [ratioProb, ha, ↓reduceIte]

theorem ratioProb_sum_eq_one (v : A → ℝ) (T : Finset A) (hT : ∑ b ∈ T, v b ≠ 0) :
    ∑ a ∈ T, ratioProb v T a = 1 := by
  rw [Finset.sum_congr rfl fun a ha ↦ ratioProb_eq_div v T a ha, ← Finset.sum_div, div_self hT]

-- Lemma 3, p. 9
theorem ratioProb_ratio (v : A → ℝ) (T : Finset A) (a₁ a₂ : A) (h₁ : a₁ ∈ T) (h₂ : a₂ ∈ T) :
    ratioProb v T a₁ * v a₂ = ratioProb v T a₂ * v a₁ := by
  rw [ratioProb_eq_div v T a₁ h₁, ratioProb_eq_div v T a₂ h₂, div_mul_eq_mul_div,
    div_mul_eq_mul_div, mul_comm]

theorem ratioProb_univ [Fintype A] (v : A → ℝ) : ratioProb v Finset.univ = (∑ j, v j)⁻¹ • v := by
  ext a
  simp [ratioProb, div_eq_inv_mul]

-- Theorem 3, p. 23
theorem ratioProb_smul {c : ℝ} (hc : c ≠ 0) (v : A → ℝ) (T : Finset A) :
    ratioProb (c • v) T = ratioProb v T := by
  ext a
  unfold ratioProb
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_mul_left _ _ hc]
  · rfl

theorem ratioProb_pair (v : A → ℝ) {x y : A} (hne : x ≠ y) :
    ratioProb v {x, y} x = pairwiseProb v x y := by
  rw [ratioProb_eq_div v _ x (Finset.mem_insert_self x {y}), Finset.sum_pair hne]
  rfl

-- Theorem 1, p. 16
theorem ratioProb_eq_one_div_sum {v : A → ℝ} {T : Finset A} {x : A} (hv : ∀ a ∈ T, 0 < v a)
    (hx : x ∈ T) :
    ratioProb v T x = 1 / ∑ y ∈ T, pairwiseProb v y x / pairwiseProb v x y := by
  have hvx := hv x hx
  have hodds : ∀ y ∈ T, pairwiseProb v y x / pairwiseProb v x y = v y / v x := fun y hy ↦ by
    have := hv y hy
    rw [pairwiseProb, pairwiseProb, add_comm (v y)]
    field_simp
  rw [sum_congr rfl hodds, ← sum_div, ratioProb_eq_div v T x hx, one_div_div]

open MeasureTheory ProbabilityTheory in
-- p. 24
theorem ratioProb_eq_cond [MeasurableSpace A] [MeasurableSingletonClass A] {v : A → ℝ}
    (hv : ∀ a, 0 ≤ v a) (T : Finset A) (a : A) :
    ratioProb v T a =
      ((Measure.count.withDensity fun b ↦ ENNReal.ofReal (v b))[{a} | ↑T]).toReal := by
  have hsum (E : Finset A) : 0 ≤ ∑ b ∈ E, v b := Finset.sum_nonneg fun b _ ↦ hv b
  rw [cond_apply T.measurableSet, ← Finset.coe_singleton, ← Finset.coe_inter,
    withDensity_ofReal_finset hv, withDensity_ofReal_finset hv, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hsum _), ENNReal.toReal_ofReal (hsum _)]
  by_cases ha : a ∈ T
  · rw [ratioProb_eq_div v T a ha, Finset.inter_singleton_of_mem ha, Finset.sum_singleton,
      inv_mul_eq_div]
  · simp only [ratioProb, ha, ↓reduceIte, Finset.inter_singleton_of_notMem ha, Finset.sum_empty,
      mul_zero]

end RatioRule

/-! ### Systems of choice probabilities and the forms of the choice axiom

For each finite set `T` the choice probabilities `P_T` "form an ordinary probability measure on the
subsets of `T`" (p. 5). Part i of Axiom 1 makes choice from a subset the conditional probability
given it, and a ratio scale is a measure from which every `P_T` is obtained by conditioning. -/

section ChoiceAxiomForms

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

-- Theorem 3, p. 23
theorem restrict_eq_smul_of_cond_eq {A : Type*} [MeasurableSpace A] {μ ν : Measure A} {T : Set A}
    (hμ₀ : μ T ≠ 0) (hμ : μ T ≠ ∞) (h : μ[|T] = ν[|T]) :
    μ.restrict T = (μ T / ν T) • ν.restrict T := by
  have hrestrict (ρ : Measure A) (h₀ : ρ T ≠ 0) (h₁ : ρ T ≠ ∞) : ρ.restrict T = ρ T • ρ[|T] := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel h₀ h₁, one_smul]
  rw [hrestrict μ hμ₀ hμ, h, ProbabilityTheory.cond, smul_smul, div_eq_mul_inv]

/-- A system of choice probabilities assigns to every finite set `T` a measure `P_T` concentrated on
`T`, the distribution of the alternative chosen from `T`, which is a probability measure when `T` is
nonempty (pp. 4–5). -/
structure ChoiceFn (A : Type*) [MeasurableSpace A] [MeasurableSingletonClass A] where
  /-- The measure `P_T` of the alternative chosen from `T`. -/
  prob : Finset A → Measure A
  /-- `P_T` is a probability measure when `T` is nonempty (probability axioms (i) and (ii)). -/
  isProbabilityMeasure_prob : ∀ T : Finset A, T.Nonempty → IsProbabilityMeasure (prob T)
  /-- The alternative chosen from `T` lies in `T`. -/
  prob_compl : ∀ T : Finset A, prob T (↑T)ᶜ = 0

namespace ChoiceFn

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] (cf : ChoiceFn A)

instance isFiniteMeasure_prob (T : Finset A) : IsFiniteMeasure (cf.prob T) := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · have h : cf.prob ∅ = 0 := by simpa using cf.prob_compl ∅
    rw [h]
    infer_instance
  · have := cf.isProbabilityMeasure_prob T hT
    infer_instance

theorem prob_coe {T : Finset A} (hT : T.Nonempty) : cf.prob T ↑T = 1 := by
  have := cf.isProbabilityMeasure_prob T hT
  exact (prob_compl_eq_zero_iff T.measurableSet).1 (cf.prob_compl T)

theorem sum_prob_real {T : Finset A} (hT : T.Nonempty) : ∑ a ∈ T, (cf.prob T).real {a} = 1 := by
  rw [sum_measureReal_singleton, measureReal_def, cf.prob_coe hT, ENNReal.toReal_one]

private theorem measure_eq_of_singleton {μ ν : Measure A} {T : Finset A} (hμ : μ (↑T)ᶜ = 0)
    (hν : ν (↑T)ᶜ = 0) (h : ∀ a ∈ T, μ {a} = ν {a}) : μ = ν := by
  classical
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ),
    ← Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)]
  ext B hB
  have hBT : B ∩ ↑T = ↑(T.filter (· ∈ B)) := by ext; simp [and_comm]
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hBT, ← sum_measure_singleton,
    ← sum_measure_singleton]
  exact sum_congr rfl fun a ha ↦ h a (mem_filter.1 ha).1

private theorem measureReal_cond_singleton {μ : Measure A} {S : Finset A} {a : A} (ha : a ∈ S) :
    (μ[|↑S]).real {a} = μ.real {a} / μ.real ↑S := by
  rw [cond_real_apply _ S.measurableSet, Set.inter_singleton_of_mem (mem_coe.2 ha)]

/-- A system has a ratio scale if a measure `μ` with positive finite point masses gives every `P_T`
by conditioning on `T` (Theorem 3, p. 23). -/
def HasRatioScale : Prop :=
  ∃ μ : Measure A, (∀ a, μ {a} ≠ 0) ∧ (∀ a, μ {a} ≠ ∞) ∧
    ∀ T : Finset A, T.Nonempty → cf.prob T = μ[|↑T]

/-- A system satisfies the product rule if `P_T(R) = P_S(R) P_T(S)` whenever `R ⊆ S ⊆ T`, which is
part i of Axiom 1 without its hypothesis of imperfect discrimination (p. 6). -/
def HasProductRule : Prop :=
  ∀ R S T : Finset A, R ⊆ S → S ⊆ T → cf.prob T R = cf.prob S R * cf.prob T S

variable {cf} in
theorem HasRatioScale.hasProductRule (h : cf.HasRatioScale) : cf.HasProductRule := by
  obtain ⟨μ, -, hfin, hμ⟩ := h
  intro R S T hRS hST
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [subset_empty.1 hRS]
  have hT : μ ↑T ≠ ∞ := by
    rw [← sum_measure_singleton]
    exact ENNReal.sum_ne_top.2 fun a _ ↦ hfin a
  have hS' : μ[|↑S] = (cf.prob T)[|↑S] := by
    rw [hμ T (hS.mono hST), cond_cond_eq_cond_inter' T.measurableSet S.measurableSet hT,
      Set.inter_eq_right.2 (coe_subset.2 hST)]
  rw [hμ S hS, hS', cond_mul_eq_inter S.measurableSet, Set.inter_eq_right.2 (coe_subset.2 hRS)]

variable [DecidableEq A]

private theorem measure_pair {μ : Measure A} {x y : A} (hxy : x ≠ y) :
    μ ↑({x, y} : Finset A) = μ {x} + μ {y} := by
  rw [← sum_measure_singleton, sum_pair hxy]

/-- Binary choice `P(x, y)` is the probability `P_{x,y}(x)` of choosing `x` from `{x, y}` (p. 5). -/
noncomputable def binary (x y : A) : ℝ := (cf.prob {x, y}).real {x}

theorem binary_nonneg (x y : A) : 0 ≤ cf.binary x y := measureReal_nonneg

theorem binary_le_one (x y : A) : cf.binary x y ≤ 1 := by
  have := cf.isProbabilityMeasure_prob {x, y} (insert_nonempty _ _)
  exact measureReal_le_one

theorem binary_complement {x y : A} (hxy : x ≠ y) : cf.binary x y + cf.binary y x = 1 := by
  rw [binary, binary, pair_comm y x, ← sum_pair hxy (f := fun a ↦ (cf.prob {x, y}).real {a}),
    cf.sum_prob_real (insert_nonempty _ _)]

-- p. 5
theorem binary_self (x : A) : cf.binary x x = 1 := by
  rw [binary, insert_eq_of_mem (mem_singleton_self x), measureReal_def, ← coe_singleton,
    cf.prob_coe (singleton_nonempty x), ENNReal.toReal_one]

/-- A system satisfies the constant-ratio rule if every set containing `a` and `b` gives them the
odds of the pair, `P_T(a) P(b, a) = P_T(b) P(a, b)` (Lemma 3, p. 9). -/
def HasPairwiseIIA : Prop :=
  ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
    (cf.prob T).real {a} * cf.binary b a = (cf.prob T).real {b} * cf.binary a b

/-- A function `v`, positive on `S`, is a binary ratio scale on `S` if choice between distinct
elements of `S` follows `P(x, y) = v x / (v x + v y)`. -/
def BinaryRatioScaleOn (S : Set A) (v : A → ℝ) : Prop :=
  (∀ x ∈ S, 0 < v x) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → cf.binary x y = pairwiseProb v x y

/-- Discrimination is imperfect throughout `T` if `0 < P(x, y) < 1` for all distinct `x` and `y` in
`T` (p. 6). -/
def ImperfectOn (T : Finset A) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 0 < cf.binary x y ∧ cf.binary x y < 1

/-- A system satisfies Axiom 1 (p. 6) if `P_T(R) = P_S(R) P_T(S)` for `R ⊆ S ⊆ T` whenever
discrimination is imperfect throughout `T`, and `P_T(S) = P_{T - {x}}(S - {x})` for `S ⊆ T` whenever
`P(x, y) = 0` for some `x` and `y` in `T`. -/
structure HasChoiceAxiom : Prop where
  product_rule : ∀ T : Finset A, cf.ImperfectOn T → ∀ R S : Finset A, R ⊆ S → S ⊆ T →
    cf.prob T R = cf.prob S R * cf.prob T S
  deletion : ∀ T : Finset A, ∀ x ∈ T, ∀ y ∈ T, cf.binary x y = 0 →
    ∀ S ⊆ T, cf.prob T S = cf.prob (T.erase x) (S.erase x)

variable {cf}

theorem HasRatioScale.hasPairwiseIIA (h : cf.HasRatioScale) : cf.HasPairwiseIIA := by
  obtain ⟨μ, -, -, hμ⟩ := h
  intro T a b ha hb
  rw [binary, binary, pair_comm b a, hμ T ⟨a, ha⟩, hμ {a, b} (insert_nonempty _ _),
    measureReal_cond_singleton ha, measureReal_cond_singleton hb,
    measureReal_cond_singleton (by simp : a ∈ ({a, b} : Finset A)),
    measureReal_cond_singleton (by simp : b ∈ ({a, b} : Finset A))]
  ring

theorem HasRatioScale.binaryRatioScaleOn (h : cf.HasRatioScale) :
    ∃ v : A → ℝ, ∀ S : Set A, cf.BinaryRatioScaleOn S v := by
  obtain ⟨μ, h0, hfin, hμ⟩ := h
  refine ⟨fun a ↦ (μ {a}).toReal, fun S ↦ ⟨fun x _ ↦ ENNReal.toReal_pos (h0 x) (hfin x),
    fun x _ y _ hxy ↦ ?_⟩⟩
  rw [binary, hμ _ (insert_nonempty _ _), measureReal_cond_singleton (by simp), measureReal_def,
    measureReal_def, measure_pair hxy, ENNReal.toReal_add (hfin x) (hfin y), pairwiseProb]

-- Axiom 1
theorem HasRatioScale.hasChoiceAxiom (h : cf.HasRatioScale) : cf.HasChoiceAxiom := by
  obtain ⟨v, hv⟩ := h.binaryRatioScaleOn
  refine ⟨fun T _ R S hRS hST ↦ h.hasProductRule R S T hRS hST, fun T x _ y _ h0 ↦ ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · simp [binary_self] at h0
  rw [(hv Set.univ).2 x trivial y trivial hxy, pairwiseProb] at h0
  have hx := (hv Set.univ).1 x trivial
  have hy := (hv Set.univ).1 y trivial
  exact absurd h0 (div_pos hx (add_pos hx hy)).ne'

-- p. 24
theorem HasPairwiseIIA.hasRatioScale [Inhabited A] (hIIA : cf.HasPairwiseIIA)
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < (cf.prob T).real {a}) :
    cf.HasRatioScale := by
  set p : Finset A → A → ℝ := fun T a ↦ (cf.prob T).real {a} with hp
  have hIIA' : ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
      p T a * p {a, b} b = p T b * p {a, b} a := fun T a b ha hb ↦ by
    have := hIIA T a b ha hb
    simp only [binary, pair_comm b a] at this
    exact this
  set x₀ := (default : A)
  set v := fun a ↦ p {a, x₀} a / p {a, x₀} x₀ with hv_def
  have hv_pos : ∀ a, 0 < v a := fun a ↦
    div_pos (hpos _ a (mem_insert.mpr (Or.inl rfl))) (hpos _ x₀ (by simp))
  have ratio_mul : ∀ (T : Finset A) (a b : A), a ∈ T → b ∈ T →
      p T a * p {b, x₀} b * p {a, x₀} x₀ = p T b * p {a, x₀} a * p {b, x₀} x₀ := by
    intro T a b ha hb
    set T' := insert x₀ T
    have ha' : a ∈ T' := mem_insert_of_mem ha
    have hb' : b ∈ T' := mem_insert_of_mem hb
    have hx₀' : x₀ ∈ T' := mem_insert_self x₀ T
    have hT := hIIA' T a b ha hb
    have hT'ab := hIIA' T' a b ha' hb'
    have hT'ax₀ := hIIA' T' a x₀ ha' hx₀'
    have hT'bx₀ := hIIA' T' b x₀ hb' hx₀'
    have hB : p T' a * p {a, x₀} x₀ * p {b, x₀} b = p T' b * p {b, x₀} x₀ * p {a, x₀} a := by
      linear_combination p {b, x₀} b * hT'ax₀ - p {a, x₀} a * hT'bx₀
    have hA_mul : (p T a * p T' b - p T b * p T' a) * p {a, b} b = 0 := by
      linear_combination p T' b * hT - p T b * hT'ab
    have hA : p T a * p T' b = p T b * p T' a := by
      rcases mul_eq_zero.mp hA_mul with h | h
      · linarith
      · exact absurd h (hpos _ b (by simp)).ne'
    exact mul_left_cancel₀ (hpos T' b hb').ne' (by
      linear_combination p {b, x₀} b * p {a, x₀} x₀ * hA + p T b * hB)
  have hrule : ∀ (T : Finset A) (a : A), a ∈ T → p T a = v a / ∑ b ∈ T, v b := by
    intro T a ha
    have hsum : 0 < ∑ b ∈ T, v b := sum_pos (fun b _ ↦ hv_pos b) ⟨a, ha⟩
    rw [eq_div_iff hsum.ne']
    have swap : ∀ b ∈ T, p T a * v b = v a * p T b := fun b hb ↦ by
      have hrm := ratio_mul T a b ha hb
      have hne_a : p {a, x₀} x₀ ≠ 0 := (hpos _ x₀ (by simp)).ne'
      have hne_b : p {b, x₀} x₀ ≠ 0 := (hpos _ x₀ (by simp)).ne'
      simp only [hv_def]
      field_simp
      linarith
    rw [mul_sum, sum_congr rfl swap, ← mul_sum, cf.sum_prob_real ⟨a, ha⟩, mul_one]
  have hμa (b : A) :
      (Measure.count.withDensity fun b ↦ ENNReal.ofReal (v b)) {b} = ENNReal.ofReal (v b) := by
    simp
  refine ⟨Measure.count.withDensity fun b ↦ ENNReal.ofReal (v b), fun a ↦ ?_, fun a ↦ ?_,
    fun T hT ↦ ?_⟩
  · rw [hμa]
    exact (ENNReal.ofReal_pos.2 (hv_pos a)).ne'
  · rw [hμa]
    exact ENNReal.ofReal_ne_top
  · refine measure_eq_of_singleton (T := T) (cf.prob_compl T)
      (by simp [cond_apply T.measurableSet]) fun a ha ↦ ?_
    have hsum : 0 < ∑ b ∈ T, v b := sum_pos (fun b _ ↦ hv_pos b) hT
    rw [cond_apply T.measurableSet, Set.inter_singleton_of_mem (mem_coe.2 ha), hμa,
      withDensity_ofReal_finset (fun b ↦ (hv_pos b).le),
      ← ofReal_measureReal (measure_ne_top _ _)]
    change ENNReal.ofReal (p T a) = _
    rw [hrule T a ha, ENNReal.ofReal_div_of_pos hsum, ENNReal.div_eq_inv_mul]

theorem hasRatioScale_iff_hasPairwiseIIA [Inhabited A]
    (hpos : ∀ (T : Finset A) (a : A), a ∈ T → 0 < (cf.prob T).real {a}) :
    cf.HasRatioScale ↔ cf.HasPairwiseIIA :=
  ⟨HasRatioScale.hasPairwiseIIA, fun h ↦ h.hasRatioScale hpos⟩

-- Axiom 1, Lemma 1, p. 6
theorem HasChoiceAxiom.prob_singleton_eq_zero (h : cf.HasChoiceAxiom) {T : Finset A} {x y : A}
    (hx : x ∈ T) (hy : y ∈ T) (h0 : cf.binary x y = 0) : cf.prob T {x} = 0 := by
  simpa using h.deletion T x hx y hy h0 {x} (singleton_subset_iff.2 hx)

-- Axiom 1
theorem HasChoiceAxiom.prob_singleton_ne_zero (h : cf.HasChoiceAxiom) {T : Finset A}
    (himp : cf.ImperfectOn T) {x : A} (hx : x ∈ T) : cf.prob T {x} ≠ 0 := by
  intro h0
  have hall : ∀ y ∈ T, cf.prob T {y} = 0 := fun y hy ↦ by
    rcases eq_or_ne y x with rfl | hyx
    · exact h0
    have hprod := h.product_rule T himp {x} {x, y} (by simp)
      (insert_subset hx (singleton_subset_iff.2 hy))
    rw [coe_singleton, h0, eq_comm, mul_eq_zero] at hprod
    have hxy : cf.prob {x, y} {x} ≠ 0 := fun h' ↦
      (himp x hx y hy hyx.symm).1.ne' (by simp [binary, measureReal_def, h'])
    exact measure_mono_null (by simp) (hprod.resolve_left hxy)
  have := cf.prob_coe ⟨x, hx⟩
  rw [← sum_measure_singleton, sum_eq_zero hall] at this
  exact zero_ne_one this

-- Axiom 1, p. 24
theorem HasChoiceAxiom.prob_eq_cond (h : cf.HasChoiceAxiom) {T S : Finset A}
    (himp : cf.ImperfectOn T) (hST : S ⊆ T) (hS : S.Nonempty) : cf.prob S = (cf.prob T)[|↑S] := by
  obtain ⟨b, hb⟩ := hS
  have hne : cf.prob T ↑S ≠ 0 := fun h0 ↦
    h.prob_singleton_ne_zero himp (hST hb) (measure_mono_null (by simpa using hb) h0)
  refine measure_eq_of_singleton (T := S) (cf.prob_compl S) (by simp [cond_apply S.measurableSet])
    fun a ha ↦ ?_
  have hprod := h.product_rule T himp {a} S (singleton_subset_iff.2 ha) hST
  rw [coe_singleton] at hprod
  rw [cond_apply S.measurableSet, Set.inter_singleton_of_mem (mem_coe.2 ha), hprod,
    mul_comm (cf.prob S {a}), ← mul_assoc, ENNReal.inv_mul_cancel hne (measure_ne_top _ _),
    one_mul]

-- Axiom 1, Theorem 3, p. 23
theorem HasChoiceAxiom.ratioScaleOn (h : cf.HasChoiceAxiom) {T : Finset A}
    (himp : cf.ImperfectOn T) :
    (∀ x ∈ T, cf.prob T {x} ≠ 0) ∧ ∀ S ⊆ T, S.Nonempty → cf.prob S = (cf.prob T)[|↑S] :=
  ⟨fun _ hx ↦ h.prob_singleton_ne_zero himp hx, fun _ hST hS ↦ h.prob_eq_cond himp hST hS⟩

-- Axiom 1, Theorem 3, p. 23
theorem HasChoiceAxiom.binaryRatioScaleOn_prob (h : cf.HasChoiceAxiom) {T : Finset A}
    (himp : cf.ImperfectOn T) : cf.BinaryRatioScaleOn ↑T fun a ↦ (cf.prob T).real {a} := by
  refine ⟨fun x hx ↦ ENNReal.toReal_pos (h.prob_singleton_ne_zero himp hx) (measure_ne_top _ _),
    fun x hx y hy hxy ↦ ?_⟩
  rw [binary, h.prob_eq_cond himp (insert_subset hx (singleton_subset_iff.2 hy))
      (insert_nonempty _ _), measureReal_cond_singleton (by simp), pairwiseProb,
    measureReal_def (cf.prob T) ↑({x, y} : Finset A), measure_pair hxy,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rfl

theorem HasChoiceAxiom.binaryRatioScaleOn (h : cf.HasChoiceAxiom) {T : Finset A}
    (himp : cf.ImperfectOn T) : ∃ v : A → ℝ, cf.BinaryRatioScaleOn ↑T v :=
  ⟨_, h.binaryRatioScaleOn_prob himp⟩

-- Axiom 1, Theorem 2, p. 16
theorem HasChoiceAxiom.binary_mul_cycle (h : cf.HasChoiceAxiom) {x y z : A} (hxy : x ≠ y)
    (hyz : y ≠ z) (hxz : x ≠ z) (himp : cf.ImperfectOn {x, y, z}) :
    cf.binary x y * cf.binary y z * cf.binary z x =
      cf.binary x z * cf.binary z y * cf.binary y x := by
  obtain ⟨v, hpos, hrule⟩ := h.binaryRatioScaleOn himp
  have mx : x ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have my : y ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have mz : z ∈ (↑({x, y, z} : Finset A) : Set A) := by simp
  have px := hpos x mx
  have py := hpos y my
  have pz := hpos z mz
  rw [hrule x mx y my hxy, hrule y my z mz hyz, hrule z mz x mx (Ne.symm hxz),
    hrule x mx z mz hxz, hrule z mz y my (Ne.symm hyz), hrule y my x mx (Ne.symm hxy)]
  simp only [pairwiseProb]
  field_simp
  ring

end ChoiceFn

end ChoiceAxiomForms

end ChoiceAxiom

end ProbabilityTheory
