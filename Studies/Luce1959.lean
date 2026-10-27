module

public import Mathlib.Probability.ConditionalProbability
public import Linglib.Processing.Psychophysics.SignalDetection
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.MeasureTheory.Constructions.List
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Luce (1959): Individual choice behavior

This file formalizes Luce's theory of choice built on his choice axiom. Wherever discrimination is
imperfect, the axiom makes choice from a finite set of alternatives the conditional probability of a
ratio scale on them. The first chapter derives this scale and the semiorder of just noticeable
differences it induces. The second applies it to psychophysics, deriving the logistic and power laws
of discrimination, its incompatibility with Thurstone's discriminal processes, a response-bias
account of signal detection that is exactly a logistic observer, and the probabilities of rankings.
The third couples preference among gambles with the subjective likelihood of events and shows that
imperfect discrimination among pure alternatives confines the events to at most three classes. The
fourth builds learning models on response strengths and derives the asymptotic behavior of the beta
model.

## Implementation notes

* A system of choice probabilities is a family of mathlib probability measures indexed by finite
  sets, so part i of the choice axiom is conditioning (`ProbabilityTheory.cond`).
* Luce sets `P(a, a) = 1/2` by convention, where here `P(a, a) = 1` is the choice from a singleton,
  so the axioms and theorems of the third chapter carry guards against coincident arguments.
* The third chapter's ratio scales are local to a set of gambles, since the chapter mixes imperfect
  discrimination among gambles with perfect discrimination among pure alternatives.
* The beta model of §4.G is a Markov kernel on the logarithm of the ratio of the response strengths.
* Thurstone's discriminal processes are random variables `U ω a` on a probability space, and choice
  from `T` is the random utility model on the processes of `T` (`ChoiceFn.ofRandomUtility`). Luce's
  independence and densities enter Theorem 7 only through the null ties they imply.

## TODO

* Appendix 1's alternative forms of Axiom 1, stated for the rejection probabilities.
* The special case of §4.G.4 (equations 19–29 and Table 6) and its conjecture.
* Theorem 15 (ii) as printed has `(1 − A(−i))/(1 − B(−i))` in its product, where (10) and (11)
  give `(A(−i) − 1)/(1 − B(−i))`, which is what the file proves.
* The derivation of the gamma form on pp. 105–106 applies the independence-of-unit condition to
  `gᵢ` without rescaling the bound `v_M`, which read literally would force `γᵢ = 0`, so the form
  `βᵢ·v + γᵢ` is taken as given.

## References

* [R. D. Luce, *Individual Choice Behavior: A Theoretical Analysis* (1959)][luce-1959]
* [L. L. Thurstone, *A law of comparative judgment* (1927)][thurstone-1927]
* [R. R. Bush and F. Mosteller, *Stochastic Models for Learning* (1955)][bush-mosteller-1955]
-/

@[expose] public section

namespace Luce1959

/-! ### §1.C–§1.E: The choice axiom and its ratio scale (pp. 5–24)

Axiom 1 (p. 6) has two parts. Under imperfect discrimination, choice from nested sets composes
multiplicatively, and an alternative never chosen over another may be deleted. On a set with
imperfect discrimination throughout, the axiom yields a ratio scale unique up to its unit (Theorem
3, p. 23). -/

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
  rw [measureReal_def, cond_apply S.measurableSet, Set.inter_singleton_of_mem (mem_coe.2 ha),
    ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def, inv_mul_eq_div]

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

/-! ### §1.G: Just noticeable differences and the trace (pp. 34–37)

A cutoff `π ∈ (1/2, 1)` defines the relations `L(π)`, at least one `π`-jnd larger, and `I(π)`, at
most one `π`-jnd apart (Definition 3, p. 34). Under a ratio scale they form a semiorder (Theorem 5),
and the trace, which orders alternatives by how well they fare against every other, is the weak
order of the scale (Theorem 6). -/

section JustNoticeableDifferences

variable {A : Type*} {v : A → ℝ} {thr : ℝ} {x y z w : A}

/-- `x L(π) y` holds when `P(x, y) > π`, so that `x` is at least one `π`-jnd larger than `y`
(Definition 3, p. 34). -/
def jndL (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  thr < pairwiseProb v x y

/-- `x I(π) y` holds when `1 - π ≤ P(x, y) ≤ π`, so that `x` and `y` are at most one `π`-jnd apart
(Definition 3, p. 34). -/
def jndI (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  1 - thr ≤ pairwiseProb v x y ∧ pairwiseProb v x y ≤ thr

-- Theorem 5, p. 35
theorem jndL_iff (hx : 0 < v x) (hy : 0 < v y) (hthr : thr < 1) :
    jndL v thr x y ↔ thr / (1 - thr) * v y < v x := by
  rw [jndL, pairwiseProb, lt_div_iff₀ (add_pos hx hy), div_mul_eq_mul_div,
    div_lt_iff₀ (sub_pos.2 hthr)]
  constructor <;> intro h <;> linarith

theorem jndI_iff (hx : 0 < v x) (hy : 0 < v y) :
    jndI v thr x y ↔ ¬ jndL v thr x y ∧ ¬ jndL v thr y x := by
  have hc := pairwiseProb_complement hx hy
  simp only [jndI, jndL, not_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem one_lt_odds (hthr₀ : 1 / 2 < thr) (hthr₁ : thr < 1) : 1 < thr / (1 - thr) := by
  rw [one_lt_div (by linarith)]
  linarith

-- Theorem 5, p. 35
theorem jnd_trichotomy (hv : ∀ a, 0 < v a) (hthr₀ : 1 / 2 < thr) (hthr₁ : thr < 1) :
    (jndL v thr x y ∧ ¬ jndL v thr y x ∧ ¬ jndI v thr x y) ∨
      (jndL v thr y x ∧ ¬ jndL v thr x y ∧ ¬ jndI v thr x y) ∨
      (jndI v thr x y ∧ ¬ jndL v thr x y ∧ ¬ jndL v thr y x) := by
  have hk := one_lt_odds hthr₀ hthr₁
  have hasymm : ¬ (jndL v thr x y ∧ jndL v thr y x) := by
    rw [jndL_iff (hv x) (hv y) hthr₁, jndL_iff (hv y) (hv x) hthr₁]
    rintro ⟨h₁, h₂⟩
    nlinarith [hv x, hv y]
  rw [jndI_iff (hv x) (hv y)]
  tauto

-- Theorem 5, p. 35
theorem jndI_refl (hv : ∀ a, 0 < v a) (hthr₀ : 1 / 2 < thr) (hthr₁ : thr < 1) :
    jndI v thr x x := by
  rw [jndI_iff (hv x) (hv x), and_self, jndL_iff (hv x) (hv x) hthr₁, not_lt]
  nlinarith [one_lt_odds hthr₀ hthr₁, hv x]

-- Theorem 5, p. 35
theorem jndL_interval (hv : ∀ a, 0 < v a) (hthr₁ : thr < 1) (hxy : jndL v thr x y)
    (hyz : jndI v thr y z) (hzw : jndL v thr z w) : jndL v thr x w := by
  rw [jndL_iff (hv _) (hv _) hthr₁] at hxy hzw ⊢
  rw [jndI_iff (hv _) (hv _), jndL_iff (hv _) (hv _) hthr₁, jndL_iff (hv _) (hv _) hthr₁] at hyz
  simp only [not_lt] at hyz
  linarith [hyz.2]

-- Theorem 5, p. 35
theorem jndL_no_sandwich (hv : ∀ a, 0 < v a) (hthr₀ : 1 / 2 < thr) (hthr₁ : thr < 1)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) : ¬ (jndI v thr x w ∧ jndI v thr w z) := by
  have hk := one_lt_odds hthr₀ hthr₁
  rintro ⟨hxw, hwz⟩
  rw [jndL_iff (hv _) (hv _) hthr₁] at hxy hyz
  rw [jndI_iff (hv _) (hv _), jndL_iff (hv _) (hv _) hthr₁, jndL_iff (hv _) (hv _) hthr₁]
    at hxw hwz
  simp only [not_lt] at hxw hwz
  nlinarith [hv w, hv z]

/-- In the trace `x ≥ y` holds when `P(x, z) ≥ P(y, z)` for every `z` (Definition 4, p. 37). -/
def traceGe (v : A → ℝ) (x y : A) : Prop :=
  ∀ z : A, pairwiseProb v y z ≤ pairwiseProb v x z

-- Theorem 6, p. 37
theorem traceGe_iff (hv : ∀ a, 0 < v a) : traceGe v x y ↔ v y ≤ v x :=
  ⟨fun h ↦ (pairwiseProb_mono_iff (hv x) (hv y) (hv y)).1 (h y),
    fun h z ↦ (pairwiseProb_mono_iff (hv x) (hv y) (hv z)).2 h⟩

-- Theorem 6, p. 37
theorem theorem6 (hv : ∀ a, 0 < v a) : Std.Total (traceGe v) ∧ IsTrans A (traceGe v) :=
  ⟨⟨fun _ _ ↦ (le_total _ _).imp (traceGe_iff hv).2 (traceGe_iff hv).2⟩,
    ⟨fun _ _ _ h₁ h₂ ↦ (traceGe_iff hv).2 (((traceGe_iff hv).1 h₂).trans ((traceGe_iff hv).1 h₁))⟩⟩

-- Theorem 6, p. 37
theorem traceGe_iff_pairwiseProb (hv : ∀ a, 0 < v a) :
    traceGe v x y ↔ 1 / 2 ≤ pairwiseProb v x y := by
  rw [traceGe_iff hv, pairwiseProb_ge_half_iff (hv x) (hv y)]

end JustNoticeableDifferences

section LogisticUniqueness

open Real

/-! ### §2.A.3: Uniqueness of the logistic curve (pp. 41–42)

If pairwise choice depends only on differences of a scale `u` that takes every real value, the ratio
scale is exponential in `u` and pairwise choice is logistic. Luce reproduces Adams and Messick's
proof, which reduces the claim to Cauchy's functional equation. -/

private theorem exists_eq_mul_of_strictMono (h : ℝ →+ ℝ) (hh : StrictMono h) :
    ∃ k : ℝ, 0 < k ∧ ∀ s, h s = k * s := by
  have hcont : Continuous h :=
    h.continuous_of_isBounded_nhds_zero (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)
      ((Metric.isBounded_Icc (h (-1)) (h 1)).subset hh.monotone.image_Icc_subset)
  refine ⟨h 1, by simpa using hh one_pos, fun s ↦ ?_⟩
  simpa [mul_comm] using map_real_smul h hcont s 1

-- §2, pp. 41–42
theorem logistic_unique {X : Type*} {v u : X → ℝ} {g F : ℝ → ℝ}
    (hu : Function.Surjective u) (hg_pos : ∀ r, 0 < g r) (hg : StrictMono g)
    (hv : ∀ x, v x = g (u x)) (hF : ∀ x y, v x / (v x + v y) = F (u x - u y)) :
    ∃ k : ℝ, 0 < k ∧ (∀ x, v x = g 0 * exp (k * u x)) ∧
      ∀ x y, v x / (v x + v y) = sigmoid (k * (u x - u y)) := by
  have hgF (r s : ℝ) : g r / (g r + g s) = F (r - s) := by
    obtain ⟨x, rfl⟩ := hu r
    obtain ⟨y, rfl⟩ := hu s
    rw [← hv, ← hv, hF]
  have hmul (s t : ℝ) : g s * g t = g 0 * g (s + t) := by
    have h : g (s + t) / (g (s + t) + g s) = g t / (g t + g 0) := by
      rw [hgF, hgF, add_sub_cancel_left, sub_zero]
    rw [div_eq_div_iff (add_pos (hg_pos _) (hg_pos _)).ne'
      (add_pos (hg_pos _) (hg_pos _)).ne'] at h
    linear_combination -h
  let h : ℝ →+ ℝ :=
    { toFun := fun s ↦ log (g s) - log (g 0)
      map_zero' := sub_self _
      map_add' := fun s t ↦ by
        have := congrArg log (hmul s t)
        rw [log_mul (hg_pos s).ne' (hg_pos t).ne', log_mul (hg_pos 0).ne' (hg_pos _).ne'] at this
        linarith }
  obtain ⟨k, hk, hks⟩ := exists_eq_mul_of_strictMono h
    fun a b hab ↦ sub_lt_sub_right (log_lt_log (hg_pos a) (hg hab)) _
  have hgexp (s : ℝ) : g s = g 0 * exp (k * s) := by
    have hs : log (g s) - log (g 0) = k * s := hks s
    rw [← exp_log (hg_pos s), ← exp_log (hg_pos 0), ← exp_add]
    congr 1
    linarith
  refine ⟨k, hk, fun x ↦ by rw [hv, hgexp (u x)], fun x y ↦ ?_⟩
  rw [hv, hv, hgexp (u x), hgexp (u y), ← mul_add, mul_div_mul_left _ _ (hg_pos 0).ne']
  simpa [pairwiseProb, mul_sub] using pairwiseProb_exp (fun a ↦ k * u a) x y

end LogisticUniqueness

section PowerLaw

open Real Set

/-! ### §2.B: The power law (pp. 42–44)

On prothetic continua Luce assumes the linear generalization of Weber's law, under which
`P(x, y) = π` exactly when `x = (1 + c(π)) y + d(π)`, and finds the power scale `A (x + C)^B` (p.
43). He checks by substitution that the power scale solves the equation and cites Luce and Edwards
for uniqueness, which follows here from the uniqueness of the logistic curve in the coordinate
`log (x + C)`. -/

/-- The power scale is `v(x) = A (x + C)^B` (p. 43). -/
noncomputable def powerScale (A C B x : ℝ) : ℝ := A * (x + C) ^ B

variable {A C B x y p : ℝ}

-- p. 44
theorem pairwiseProb_powerScale (hA : 0 < A) (hx : 0 < x + C) (hy : 0 < y + C) :
    pairwiseProb (powerScale A C B) x y = 1 / (1 + ((y + C) / (x + C)) ^ B) := by
  have h₁ : 0 < (x + C) ^ B := rpow_pos_of_pos hx B
  have h₂ : 0 < (y + C) ^ B := rpow_pos_of_pos hy B
  rw [pairwiseProb, powerScale, powerScale, div_rpow hy.le hx.le]
  field_simp

theorem pairwiseProb_powerScale_eq_iff (hA : 0 < A) (hB : 0 < B) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hx : 0 < x + C) (hy : 0 < y + C) :
    pairwiseProb (powerScale A C B) x y = p ↔ x + C = (p / (1 - p)) ^ (1 / B) * (y + C) := by
  have h₂ : 0 < (y + C) ^ B := rpow_pos_of_pos hy B
  have hq : 0 < p / (1 - p) := div_pos hp₀ (sub_pos.2 hp₁)
  have hiff : pairwiseProb (powerScale A C B) x y = p ↔
      ((x + C) / (y + C)) ^ B = p / (1 - p) := by
    have h₁ : 0 < (x + C) ^ B := rpow_pos_of_pos hx B
    rw [pairwiseProb, powerScale, powerScale, div_rpow hx.le hy.le, div_eq_iff (by positivity),
      div_eq_div_iff h₂.ne' (sub_pos.2 hp₁).ne']
    constructor
    · intro h
      apply mul_left_cancel₀ hA.ne'
      linear_combination h
    · intro h
      linear_combination A * h
  rw [hiff, eq_comm, ← rpow_inv_eq hq.le (div_pos hx hy).le hB.ne', eq_div_iff hy.ne', one_div]
  exact eq_comm

-- p. 43
theorem powerScale_weber {c : ℝ} (hA : 0 < A) (hB : 0 < B) (hp₀ : 1 / 2 < p) (hp₁ : p < 1)
    (hc : 1 + c = (p / (1 - p)) ^ (1 / B)) :
    (∀ x y, 0 < x + C → 0 < y + C →
      (pairwiseProb (powerScale A C B) x y = p ↔ x = (1 + c) * y + c * C)) ∧
    B = (log p - log (1 - p)) / log (1 + c) := by
  refine ⟨fun x y hx hy ↦ ?_, ?_⟩
  · rw [pairwiseProb_powerScale_eq_iff hA hB (by linarith) hp₁ hx hy, ← hc]
    constructor <;> intro h <;> linarith
  · have hL : 0 < log p - log (1 - p) := sub_pos.2 (log_lt_log (by linarith) (by linarith))
    rw [hc, log_rpow (div_pos (by linarith) (by linarith)), log_div (by linarith) (by linarith),
      one_div]
    field_simp

-- p. 43
theorem powerScale_unique {v F : ℝ → ℝ} (hv_pos : ∀ x, 0 < x + C → 0 < v x)
    (hv : StrictMonoOn v (Ioi (-C)))
    (hF : ∀ x y, 0 < x + C → 0 < y + C → pairwiseProb v x y = F ((x + C) / (y + C))) :
    ∃ B, 0 < B ∧ ∀ x, 0 < x + C → v x = powerScale (v (1 - C)) C B x := by
  have hmem (r : ℝ) : exp r - C ∈ Ioi (-C) := by simp [exp_pos]
  have hpos (x : Ioi (-C)) : 0 < (x : ℝ) + C := by linarith [mem_Ioi.1 x.2]
  obtain ⟨k, hk, hvk, -⟩ := logistic_unique (X := Ioi (-C)) (v := fun x ↦ v x)
    (u := fun x ↦ log (x + C)) (g := fun r ↦ v (exp r - C)) (F := fun t ↦ F (exp t))
    (fun r ↦ ⟨⟨_, hmem r⟩, by simp⟩) (fun r ↦ hv_pos _ (by simpa using hmem r))
    (fun r s hrs ↦ hv (hmem r) (hmem s) (by simpa using hrs))
    (fun x ↦ by simp [exp_log (hpos x)])
    (fun x y ↦ by
      rw [exp_sub, exp_log (hpos x), exp_log (hpos y), ← hF _ _ (hpos x) (hpos y)]
      rfl)
  refine ⟨k, hk, fun x hx ↦ ?_⟩
  have := hvk ⟨x, mem_Ioi.2 (by linarith)⟩
  simp only [exp_zero] at this
  rw [this, powerScale, rpow_def_of_pos hx, mul_comm (log _) k, sub_eq_add_neg]

theorem jndL_powerScale_iff {thr : ℝ} (hA : 0 < A) (hB : 0 < B) (hthr₀ : 0 < thr)
    (hthr₁ : thr < 1) (hx : 0 < x + C) (hy : 0 < y + C) :
    jndL (powerScale A C B) thr x y ↔ (thr / (1 - thr)) ^ (1 / B) * (y + C) < x + C := by
  have hq : 0 < thr / (1 - thr) := div_pos hthr₀ (sub_pos.2 hthr₁)
  have h₁ : 0 < (x + C) ^ B := rpow_pos_of_pos hx B
  have h₂ : 0 < (y + C) ^ B := rpow_pos_of_pos hy B
  rw [jndL_iff (by unfold powerScale; positivity) (by unfold powerScale; positivity) hthr₁,
    powerScale, powerScale, ← mul_assoc, mul_comm _ A, mul_assoc, mul_lt_mul_iff_right₀ hA,
    ← lt_div_iff₀ h₂, ← div_rpow hx.le hy.le, one_div, ← lt_div_iff₀ hy,
    rpow_inv_lt_iff_of_pos hq.le (div_pos hx hy).le hB]

/-! ### §2.C: Interaction of continua (pp. 47–51)

With an intensity `x` and a second variable `ξ`, Weber's law on each continuum makes the scale a
power function of each variable with the other held fixed, and Luce assumes that the two surfaces
coincide (p. 49). He reaches the form (8) by differentiating twice. Since the equation is affine in
`log x` and `log ξ`, two of its values suffice here, with no assumption of differentiability. -/

-- (x), (8), p. 50
theorem interaction_form {Aξ Bξ Ax Bx : ℝ → ℝ} (hA : ∀ ξ, 0 < ξ → 0 < Aξ ξ)
    (hA' : ∀ x, 0 < x → 0 < Ax x)
    (h : ∀ x ξ, 0 < x → 0 < ξ → Aξ ξ * x ^ Bξ ξ = Ax x * ξ ^ Bx x) :
    ∃ K b b' c : ℝ, 0 < K ∧ ∀ x ξ, 0 < x → 0 < ξ →
      Aξ ξ * x ^ Bξ ξ = K * ξ ^ b' * x ^ (b + c * log ξ) := by
  have hl (x ξ : ℝ) (hx : 0 < x) (hξ : 0 < ξ) :
      log (Aξ ξ) + Bξ ξ * log x = log (Ax x) + Bx x * log ξ := by
    have := congrArg log (h x ξ hx hξ)
    rwa [log_mul (hA ξ hξ).ne' (rpow_pos_of_pos hx _).ne', log_mul (hA' x hx).ne'
      (rpow_pos_of_pos hξ _).ne', log_rpow hx, log_rpow hξ] at this
  refine ⟨Ax 1, Bξ 1, Bx 1, Bx (exp 1) - Bx 1, hA' 1 one_pos, fun x ξ hx hξ ↦ ?_⟩
  have h₁ := hl 1 ξ one_pos hξ
  have h₂ := hl 1 1 one_pos one_pos
  have h₃ := hl (exp 1) ξ (exp_pos 1) hξ
  have h₄ := hl (exp 1) 1 (exp_pos 1) one_pos
  simp only [log_one, mul_zero, add_zero, log_exp, mul_one] at h₁ h₂ h₃ h₄
  have hB : Bξ ξ = Bξ 1 + (Bx (exp 1) - Bx 1) * log ξ := by linarith
  have hK := mul_pos (hA' 1 one_pos) (rpow_pos_of_pos hξ (Bx 1))
  apply log_injOn_pos (mul_pos (hA ξ hξ) (rpow_pos_of_pos hx _))
    (mul_pos hK (rpow_pos_of_pos hx _))
  rw [log_mul (hA ξ hξ).ne' (rpow_pos_of_pos hx _).ne', log_rpow hx, log_mul hK.ne'
    (rpow_pos_of_pos hx _).ne', log_mul (hA' 1 one_pos).ne' (rpow_pos_of_pos hξ _).ne',
    log_rpow hξ, log_rpow hx, h₁, hB]

-- (8), p. 50
theorem pairwiseProb_interaction {K b b' c ξ : ℝ} (hK : 0 < K) (hξ : 0 < ξ) (hx : 0 < x)
    (hy : 0 < y) :
    pairwiseProb (fun x ↦ K * ξ ^ b' * x ^ (b + c * log ξ)) x y =
      1 / (1 + (y / x) ^ (b + c * log ξ)) := by
  have h := pairwiseProb_powerScale (A := K * ξ ^ b') (C := 0) (B := b + c * log ξ) (x := x)
    (y := y) (by positivity) (by simpa using hx) (by simpa using hy)
  simp only [add_zero] at h
  convert h using 2
  funext x
  simp [powerScale]

end PowerLaw

section Thurstone

/-! ### §2.D: Discriminal processes (pp. 54–58)

In Thurstone's model each stimulus `a` produces a discriminal process `U ω a`, and the stimulus
whose process is the largest is judged the largest. Choice from `T` is then the random utility model
on the processes of `T` (`ProbabilityTheory.choiceProb`), Luce's integral (9) when the processes are
independent. Judging the smallest is judging the largest of the processes `-U ω a`, his (10). With
three stimuli the probabilities that `x` is judged the largest and the smallest differ by
`P(x, y) + P(x, z) - 1`, and Theorem 7 (p. 57) shows that the two judgments cannot both satisfy
Axiom 1. -/

open MeasureTheory ProbabilityTheory Finset

namespace ChoiceFn

variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Ω]
  {U : Ω → A → ℝ}

/-- The system of choice probabilities of discriminal processes `U ω a` whose ties have probability
zero. Choice from `T` is the random utility model on the processes of `T`, so `P_T(a)` is the
probability that the process of `a` is the largest of them, equation (9) for independent processes
(p. 56). -/
noncomputable def ofRandomUtility (P : Measure Ω) [IsProbabilityMeasure P] (hU : Measurable U)
    (hties : ∀ j k, j ≠ k → P {ω | U ω j = U ω k} = 0) : ChoiceFn A where
  prob T := ∑ a : T, choiceProb (P.map fun ω (j : T) ↦ U ω j) a • Measure.dirac (a : A)
  isProbabilityMeasure_prob T hT := by
    have : Nonempty T := hT.to_subtype
    have hV : Measurable fun ω (j : T) ↦ U ω j := by fun_prop
    refine ⟨?_⟩
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    refine sum_choiceProb _ fun j k hjk ↦ ?_
    rw [Measure.map_apply hV (measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply k))]
    exact hties j k (Subtype.coe_ne_coe.2 hjk)
  prob_compl T := by
    simp [Measure.dirac_apply' _ T.measurableSet.compl]

variable {P : Measure Ω} [IsProbabilityMeasure P] (hU : Measurable U)
  (hties : ∀ j k, j ≠ k → P {ω | U ω j = U ω k} = 0)

theorem ofRandomUtility_prob_singleton {T : Finset A} {a : A} (ha : a ∈ T) :
    (ofRandomUtility P hU hties).prob T {a} = P {ω | ∀ j ∈ T, j ≠ a → U ω j < U ω a} := by
  have hV : Measurable fun ω (j : T) ↦ U ω j := by fun_prop
  simp only [ofRandomUtility, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single ⟨a, ha⟩ (fun b _ hb ↦ by simp [Subtype.coe_ne_coe.2 hb]) (by simp),
    Measure.dirac_apply_of_mem (Set.mem_singleton a), mul_one, choiceProb_map P hV]
  congr 1
  ext ω
  simp [Subtype.forall]

variable [DecidableEq A]

theorem binary_ofRandomUtility {x y : A} (hxy : x ≠ y) :
    (ofRandomUtility P hU hties).binary x y = P.real {ω | U ω y < U ω x} := by
  rw [binary, measureReal_def, ofRandomUtility_prob_singleton hU hties (mem_insert_self x {y}),
    measureReal_def]
  congr 2
  ext ω
  simp [hxy.symm]

private theorem ratio_largest_sub_smallest_ne {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hne : x / (x + y) + x / (x + z) ≠ 1) :
    x / (x + y + z) - y * z / (x * y + x * z + y * z) ≠ x / (x + y) + x / (x + z) - 1 := by
  intro h
  have hq : 0 < x * y + x * z + y * z := by positivity
  have hrhs : x / (x + y) + x / (x + z) - 1 = (x ^ 2 - y * z) / ((x + y) * (x + z)) := by
    field_simp; ring
  have hlhs : x / (x + y + z) - y * z / (x * y + x * z + y * z) =
      (x ^ 2 - y * z) * (y + z) / ((x + y + z) * (x * y + x * z + y * z)) := by
    field_simp; ring
  have hsq : x ^ 2 - y * z ≠ 0 := fun h0 ↦ hne (by
    have : x / (x + y) + x / (x + z) - 1 = 0 := by rw [hrhs, h0, zero_div]
    linarith)
  rw [hlhs, hrhs, div_eq_div_iff (by positivity) (by positivity)] at h
  have h5 : (y + z) * ((x + y) * (x + z)) = (x + y + z) * (x * y + x * z + y * z) :=
    mul_left_cancel₀ hsq (by linarith)
  nlinarith [mul_pos (mul_pos hx hy) hz]

private theorem theorem7_arith {px py pz qx qy qz : ℝ} (hpx : 0 < px) (hpy : 0 < py)
    (hpz : 0 < pz) (hqx : 0 < qx) (hqy : 0 < qy) (hqz : 0 < qz) (hp : px + py + pz = 1)
    (hq : qx + qy + qz = 1) (hxy : qx / (qx + qy) = py / (py + px))
    (hxz : qx / (qx + qz) = pz / (pz + px)) (hne : px / (px + py) + px / (px + pz) ≠ 1) :
    px - qx ≠ px / (px + py) + px / (px + pz) - 1 := by
  rw [div_eq_div_iff (by positivity) (by positivity)] at hxy hxz
  have hqx' : qx = py * pz / (px * py + px * pz + py * pz) := by
    rw [eq_div_iff (by positivity)]
    linear_combination pz * hxy + py * hxz + py * pz * hq
  have := ratio_largest_sub_smallest_ne hpx hpy hpz hne
  rwa [hp, div_one, ← hqx'] at this

-- Axiom 1, Theorem 7, p. 57
theorem theorem7 {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (himp : (ofRandomUtility P hU hties).ImperfectOn {x, y, z})
    (hne : (ofRandomUtility P hU hties).binary x y + (ofRandomUtility P hU hties).binary x z ≠ 1) :
    ¬ ((ofRandomUtility P hU hties).HasChoiceAxiom ∧
      (ofRandomUtility P hU.neg fun j k hjk ↦ by simpa using hties j k hjk).HasChoiceAxiom) := by
  rintro ⟨hL, hS⟩
  set L := ofRandomUtility P hU hties
  set S := ofRandomUtility P hU.neg fun j k hjk ↦ by simpa using hties j k hjk
  have hSL (r s : A) (hrs : r ≠ s) : S.binary r s = L.binary s r := by
    rw [binary_ofRandomUtility _ _ hrs, binary_ofRandomUtility _ _ hrs.symm]
    simp
  have himpS : S.ImperfectOn {x, y, z} := fun r hr s hs hrs ↦ by
    rw [hSL r s hrs]
    exact himp s hs r hr hrs.symm
  obtain ⟨hp, hpL⟩ := hL.binaryRatioScaleOn_prob himp
  obtain ⟨hq, hqS⟩ := hS.binaryRatioScaleOn_prob himpS
  have hsum (cf : ChoiceFn A) : (cf.prob {x, y, z}).real {x} + (cf.prob {x, y, z}).real {y} +
      (cf.prob {x, y, z}).real {z} = 1 := by
    rw [← cf.sum_prob_real (insert_nonempty x {y, z}), sum_insert (by simp [hxy, hxz]),
      sum_pair hyz, add_assoc]
  -- the probabilities that `x` is judged the largest and the smallest differ by
  -- `P(x, y) + P(x, z) - 1`, by inclusion-exclusion with null ties
  have hid : (L.prob {x, y, z}).real {x} - (S.prob {x, y, z}).real {x} =
      L.binary x y + L.binary x z - 1 := by
    have hA : MeasurableSet {ω | U ω y < U ω x} := measurableSet_lt (by fun_prop) (by fun_prop)
    have hB : MeasurableSet {ω | U ω z < U ω x} := measurableSet_lt (by fun_prop) (by fun_prop)
    have hae : {ω | U ω x < U ω y ∧ U ω x < U ω z} =ᵐ[P]
        ({ω | U ω y < U ω x} ∪ {ω | U ω z < U ω x})ᶜ := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hties x y hxy),
        measure_eq_zero_iff_ae_notMem.1 (hties x z hxz)] with ω h1 h2
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, not_or, not_lt] at h1 h2 ⊢
      rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
      tauto
    have hL' : {ω | ∀ j ∈ ({x, y, z} : Finset A), j ≠ x → U ω j < U ω x} =
        {ω | U ω y < U ω x} ∩ {ω | U ω z < U ω x} := by
      ext ω
      simp [hxy.symm, hxz.symm]
    have hS' : {ω | ∀ j ∈ ({x, y, z} : Finset A), j ≠ x → (-U) ω j < (-U) ω x} =
        {ω | U ω x < U ω y ∧ U ω x < U ω z} := by
      ext ω
      simp [hxy.symm, hxz.symm]
    rw [measureReal_def, measureReal_def, ofRandomUtility_prob_singleton _ _ (by simp),
      ofRandomUtility_prob_singleton _ _ (by simp), hL', hS', ← measureReal_def,
      ← measureReal_def, measureReal_congr hae, probReal_compl_eq_one_sub (hA.union hB),
      binary_ofRandomUtility _ _ hxy, binary_ofRandomUtility _ _ hxz]
    linarith [measureReal_union_add_inter (μ := P) (s := {ω | U ω y < U ω x}) hB]
  have mem (a : A) (ha : a = x ∨ a = y ∨ a = z) : a ∈ (↑({x, y, z} : Finset A) : Set A) := by
    simpa using ha
  have hxy' := hSL x y hxy
  have hxz' := hSL x z hxz
  rw [hqS x (mem x (by simp)) y (mem y (by simp)) hxy, hpL y (mem y (by simp)) x (mem x (by simp))
    hxy.symm] at hxy'
  rw [hqS x (mem x (by simp)) z (mem z (by simp)) hxz, hpL z (mem z (by simp)) x (mem x (by simp))
    hxz.symm] at hxz'
  rw [hpL x (mem x (by simp)) y (mem y (by simp)) hxy, hpL x (mem x (by simp)) z (mem z (by simp))
    hxz] at hid hne
  simp only [pairwiseProb] at hid hne hxy' hxz'
  exact theorem7_arith (hp x (mem x (by simp))) (hp y (mem y (by simp))) (hp z (mem z (by simp)))
    (hq x (mem x (by simp))) (hq y (mem y (by simp))) (hq z (mem z (by simp))) (hsum L) (hsum S)
    hxy' hxz' hne hid

end ChoiceFn

end Thurstone

section Detection

open Real MeasureTheory ProbabilityTheory Set SignalDetection

/-! ### §2.E: Signal detectability theory (pp. 58–64)

In the Yes-No experiment Luce applies the choice axiom to the two responses, with a signal parameter
`α` and a response bias `v` among the scale values (p. 60). He contrasts the response bias with the
criterion of signal detectability theory, yet the resulting model is exactly a logistic observer
with a criterion. The two-alternative forced choice is the Yes-No model with `α²` in place of `α`
(p. 62), since the subject makes "in effect, two Yes-No decisions", so it doubles the logistic
sensitivity, while the normal model multiplies its sensitivity by `√2`. -/

/-- `yesNoProb α v b` is the probability of affirming the signal in the axiom-1 Yes-No model with
signal parameter `α` and response bias `v`, on signal trials (`b = true`) and noise trials
(`b = false`) (p. 61). -/
noncomputable def yesNoProb (α v : ℝ) : Bool → ℝ
  | true => α / (α + v)
  | false => 1 / (1 + v)

/-- `forcedChoiceProb α v b` is the probability of choosing the first interval in the axiom-1
two-alternative forced choice, when the signal is in the first interval (`b = true`) or the second
(`b = false`) (p. 62). -/
noncomputable def forcedChoiceProb (α v : ℝ) : Bool → ℝ
  | true => α / (α + v)
  | false => 1 / (1 + α * v)

variable {α v : ℝ}

-- Axiom 1, p. 61
theorem yesNoProb_roc (hα : 0 < α) (hv : 0 < v) :
    yesNoProb α v true = α * yesNoProb α v false / ((α - 1) * yesNoProb α v false + 1) := by
  have h : 1 + v ≠ 0 := by positivity
  simp only [yesNoProb]
  rw [show (α - 1) * (1 / (1 + v)) + 1 = (α + v) / (1 + v) by field_simp; ring]
  field_simp

-- p. 62
theorem forcedChoiceProb_eq_yesNoProb (hα : 0 < α) :
    forcedChoiceProb α v = yesNoProb (α ^ 2) (α * v) := by
  funext b
  cases b
  · simp [forcedChoiceProb, yesNoProb]
  · simp only [forcedChoiceProb, yesNoProb]
    rw [sq, ← mul_add, mul_div_mul_left _ _ hα.ne']

-- p. 62
theorem forcedChoiceProb_roc (hα : 0 < α) (hv : 0 < v) :
    forcedChoiceProb α v true =
      α ^ 2 * forcedChoiceProb α v false / ((α ^ 2 - 1) * forcedChoiceProb α v false + 1) := by
  rw [forcedChoiceProb_eq_yesNoProb hα]
  exact yesNoProb_roc (by positivity) (by positivity)

theorem yesNoProb_eq_logistic (hα : 0 < α) (hv : 0 < v) (b : Bool) :
    yesNoProb α v b =
      (locationExperiment logisticMeasure (log α) b).real (Ioi (log v - log α / 2)) := by
  cases b
  · rw [← falseAlarmRate, falseAlarmRate_logisticMeasure,
      show -(log α / 2) - (log v - log α / 2) = -log v by ring, sigmoid_neg, sigmoid_log hv,
      yesNoProb]
    field_simp
    ring
  · rw [← hitRate, hitRate_logisticMeasure,
      show log α / 2 - (log v - log α / 2) = log (α / v) by rw [log_div hα.ne' hv.ne']; ring,
      sigmoid_log (div_pos hα hv), yesNoProb]
    field_simp

theorem forcedChoiceProb_eq_logistic (hα : 0 < α) (hv : 0 < v) (b : Bool) :
    forcedChoiceProb α v b =
      (locationExperiment logisticMeasure (2 * log α) b).real (Ioi (log v)) := by
  rw [forcedChoiceProb_eq_yesNoProb hα, yesNoProb_eq_logistic (by positivity) (by positivity),
    log_pow, log_mul hα.ne' hv.ne']
  congr 3
  ring

end Detection

section Ranking

open Finset

variable {A : Type*}

private theorem sublist_cons_of_ne {a b : A} {l r : List A} (h : b ≠ a) :
    (b :: l).Sublist (a :: r) ↔ (b :: l).Sublist r := by
  rw [List.sublist_cons_iff]
  simp [h]

variable [DecidableEq A]

/-! ### §2.F: Rank orderings (pp. 68–74)

The ranking postulate (p. 72) ranks first an alternative chosen from the whole set and then ranks
the rest by the same rule, so under a ratio scale the probability of a ranking is a product of
choices from shrinking sets. -/

/-- Under the ranking postulate with ratio scale `v`, a ranking has the probability that its first
alternative is chosen from the whole ranking by the ratio rule, times the probability of the rest
(p. 72). -/
noncomputable def rankProb (v : A → ℝ) : List A → ℝ
  | [] => 1
  | a :: rest => ratioProb v (a :: rest).toFinset a * rankProb v rest

/-- The rankings of `T` are the lists without repetition whose elements are those of `T`. -/
noncomputable def allRankings (T : Finset A) : Finset (List A) :=
  T.val.toList.permutations.toFinset

theorem mem_allRankings_iff {T : Finset A} {r : List A} :
    r ∈ allRankings T ↔ r.toFinset = T ∧ r.Nodup := by
  have hT : T.val.toList.Nodup := by rw [← Multiset.coe_nodup, Multiset.coe_toList]; exact T.nodup
  simp only [allRankings, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    refine ⟨?_, h.nodup_iff.2 hT⟩
    ext x
    rw [List.mem_toFinset, h.mem_iff, Multiset.mem_toList, Finset.mem_val]
  · rintro ⟨hfs, hnd⟩
    rw [List.perm_ext_iff_of_nodup hnd hT]
    intro x
    rw [← List.mem_toFinset, hfs, Multiset.mem_toList, Finset.mem_val]

private theorem cons_mem_allRankings_iff {T : Finset A} {a : A} {r : List A} :
    a :: r ∈ allRankings T ↔ a ∈ T ∧ r ∈ allRankings (T.erase a) := by
  simp only [mem_allRankings_iff, List.toFinset_cons, List.nodup_cons]
  constructor
  · rintro ⟨rfl, ha, hr⟩
    exact ⟨mem_insert_self _ _, by rw [erase_insert (by simpa using ha)], hr⟩
  · rintro ⟨ha, hr, hnd⟩
    exact ⟨by rw [hr, insert_erase ha], fun h ↦ notMem_erase a T (hr ▸ List.mem_toFinset.2 h), hnd⟩

private theorem sum_allRankings {T : Finset A} (hT : T.Nonempty) (f : List A → ℝ) :
    ∑ r ∈ allRankings T, f r = ∑ a ∈ T, ∑ r ∈ allRankings (T.erase a), f (a :: r) := by
  have hsplit :
      allRankings T = T.biUnion fun a ↦ (allRankings (T.erase a)).image (List.cons a) := by
    ext r
    simp only [mem_biUnion, mem_image]
    constructor
    · intro hr
      obtain ⟨a, r, rfl⟩ : ∃ a r', r = a :: r' := by
        cases r with
        | nil => exact absurd (mem_allRankings_iff.1 hr).1 (by simpa using hT.ne_empty.symm)
        | cons a r' => exact ⟨a, r', rfl⟩
      exact ⟨a, (cons_mem_allRankings_iff.1 hr).1, r, (cons_mem_allRankings_iff.1 hr).2, rfl⟩
    · rintro ⟨a, ha, r, hr, rfl⟩
      exact cons_mem_allRankings_iff.2 ⟨ha, hr⟩
  rw [hsplit, sum_biUnion fun a _ b _ hab ↦ disjoint_left.2 fun r ha hb ↦ by
    obtain ⟨_, _, rfl⟩ := mem_image.1 ha
    obtain ⟨_, _, h⟩ := mem_image.1 hb
    exact hab (List.cons.inj h).1.symm]
  exact sum_congr rfl fun a _ ↦ sum_image fun _ _ _ _ h ↦ (List.cons.inj h).2

private theorem rankProb_cons_of_mem {v : A → ℝ} {T : Finset A} {a : A} {r : List A}
    (hr : a :: r ∈ allRankings T) : rankProb v (a :: r) = ratioProb v T a * rankProb v r := by
  rw [rankProb, (mem_allRankings_iff.1 hr).1]

private theorem sum_rankProb {v : A → ℝ} (T : Finset A) (hv : ∀ a ∈ T, 0 < v a) :
    ∑ r ∈ allRankings T, rankProb v r = 1 := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp [allRankings, rankProb]
    rw [sum_allRankings hT, ← ratioProb_sum_eq_one v T (sum_pos hv hT).ne']
    refine sum_congr rfl fun a ha ↦ ?_
    rw [sum_congr rfl fun r hr ↦ rankProb_cons_of_mem (cons_mem_allRankings_iff.2 ⟨ha, hr⟩),
      ← mul_sum, ih _ (erase_ssubset ha) fun b hb ↦ hv b (mem_of_mem_erase hb), mul_one]

private theorem sum_rankProb_sublist {v : A → ℝ} {x y : A} (hxy : x ≠ y) (T : Finset A)
    (hx : x ∈ T) (hy : y ∈ T)
    (hv : ∀ a ∈ T, 0 < v a) :
    ∑ r ∈ (allRankings T).filter ([x, y].Sublist ·), rankProb v r = pairwiseProb v x y := by
  induction T using Finset.strongInduction with
  | H T ih =>
    have hT : T.Nonempty := ⟨x, hx⟩
    have hyx : y ∈ T.erase x := mem_erase.2 ⟨hxy.symm, hy⟩
    have hfirst (a : A) (ha : a ∈ T) :
        ∑ r ∈ allRankings (T.erase a),
            (if [x, y].Sublist (a :: r) then rankProb v (a :: r) else 0) =
          ratioProb v T a * ∑ r ∈ allRankings (T.erase a),
            (if [x, y].Sublist (a :: r) then rankProb v r else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun r hr ↦ ?_
      split_ifs
      · exact rankProb_cons_of_mem (cons_mem_allRankings_iff.2 ⟨ha, hr⟩)
      · rw [mul_zero]
    -- `x` ranked first: `y` lies below it in every ranking of the rest
    have hX : ∑ r ∈ allRankings (T.erase x),
        (if [x, y].Sublist (x :: r) then rankProb v r else 0) = 1 := by
      rw [← sum_rankProb (T.erase x) fun b hb ↦ hv b (mem_of_mem_erase hb)]
      refine sum_congr rfl fun r hr ↦ ite_eq_left ?_
      rw [List.cons_sublist_cons, List.singleton_sublist, ← List.mem_toFinset,
        (mem_allRankings_iff.1 hr).1]
      exact hyx
    -- `y` ranked first: `x` cannot lie above it
    have hY : ∑ r ∈ allRankings (T.erase y),
        (if [x, y].Sublist (y :: r) then rankProb v r else 0) = 0 := by
      refine sum_eq_zero fun r hr ↦ ite_eq_right fun h ↦ ?_
      rw [sublist_cons_of_ne hxy] at h
      have hyr : y ∈ r := h.subset (List.mem_cons_of_mem x (List.mem_singleton_self y))
      exact notMem_erase y T ((mem_allRankings_iff.1 hr).1 ▸ List.mem_toFinset.2 hyr)
    -- another alternative ranked first: the rest is a ranking of a smaller set
    have hZ (z : A) (hz : z ∈ (T.erase x).erase y) : ∑ r ∈ allRankings (T.erase z),
        (if [x, y].Sublist (z :: r) then rankProb v r else 0) = pairwiseProb v x y := by
      have hzy := ne_of_mem_erase hz
      have hzx := ne_of_mem_erase (mem_of_mem_erase hz)
      have hzT := mem_of_mem_erase (mem_of_mem_erase hz)
      simp_rw [sublist_cons_of_ne hzx.symm]
      rw [← sum_filter]
      exact ih _ (erase_ssubset hzT) (mem_erase.2 ⟨hzx.symm, hx⟩) (mem_erase.2 ⟨hzy.symm, hy⟩)
        fun b hb ↦ hv b (mem_of_mem_erase hb)
    rw [sum_filter, sum_allRankings hT, sum_congr rfl fun a ha ↦ hfirst a ha,
      ← add_sum_erase T _ hx, ← add_sum_erase (T.erase x) _ hyx, hX, hY,
      sum_congr rfl fun z hz ↦ by rw [hZ z hz], ← sum_mul, mul_one, mul_zero, zero_add]
    have hsum := ratioProb_sum_eq_one v T (sum_pos hv hT).ne'
    rw [← add_sum_erase T _ hx, ← add_sum_erase (T.erase x) _ hyx] at hsum
    have hxy' : v x + v y ≠ 0 := (add_pos (hv x hx) (hv y hy)).ne'
    have hS : ∑ b ∈ T, v b ≠ 0 := (sum_pos hv hT).ne'
    have hsplit : ratioProb v T x = pairwiseProb v x y * (ratioProb v T x + ratioProb v T y) := by
      rw [ratioProb_eq_div v T x hx, ratioProb_eq_div v T y hy, pairwiseProb, ← add_div]
      field_simp
    linear_combination hsplit + pairwiseProb v x y * hsum

private theorem rankProb_nonneg {v : A → ℝ} {r : List A} (hv : ∀ a ∈ r, 0 ≤ v a) :
    0 ≤ rankProb v r := by
  induction r with
  | nil => exact zero_le_one
  | cons a rest ih =>
    refine mul_nonneg ?_ (ih fun b hb ↦ hv b (List.mem_cons_of_mem a hb))
    unfold ratioProb
    split_ifs
    · exact div_nonneg (hv a (List.mem_cons_self ..)) (sum_nonneg fun b hb ↦
        hv b (List.mem_toFinset.1 hb))
    · exact le_rfl

open MeasureTheory

/-- The distribution of the rankings of `T` under the ranking postulate puts the mass `rankProb v r`
on each ranking `r` of `T`. -/
noncomputable def rankMeasure (v : A → ℝ) (T : Finset A) : Measure (List A) :=
  ∑ r ∈ allRankings T, ENNReal.ofReal (rankProb v r) • Measure.dirac r

theorem rankMeasure_apply (v : A → ℝ) (T : Finset A) (s : Set (List A)) [DecidablePred (· ∈ s)] :
    rankMeasure v T s = ∑ r ∈ (allRankings T).filter (· ∈ s), ENNReal.ofReal (rankProb v r) := by
  rw [sum_filter]
  simp [rankMeasure, Set.indicator_apply]

private theorem rankMeasure_apply_of_pos {v : A → ℝ} {T : Finset A} (hv : ∀ a ∈ T, 0 < v a)
    (s : Set (List A)) [DecidablePred (· ∈ s)] :
    rankMeasure v T s = ENNReal.ofReal (∑ r ∈ (allRankings T).filter (· ∈ s), rankProb v r) := by
  rw [rankMeasure_apply, ENNReal.ofReal_sum_of_nonneg fun r hr ↦ rankProb_nonneg fun a ha ↦ ?_]
  have hrT := (mem_allRankings_iff.1 (mem_filter.1 hr).1).1
  exact (hv a (by rw [← hrT]; exact List.mem_toFinset.2 ha)).le

theorem isProbabilityMeasure_rankMeasure {v : A → ℝ} {T : Finset A} (hv : ∀ a ∈ T, 0 < v a) :
    IsProbabilityMeasure (rankMeasure v T) :=
  ⟨by classical rw [rankMeasure_apply_of_pos hv, filter_true_of_mem fun _ _ ↦ Set.mem_univ _,
    sum_rankProb T hv, ENNReal.ofReal_one]⟩

-- Theorem 9, p. 72
theorem theorem9 {v : A → ℝ} {x y : A} (hxy : x ≠ y) {T : Finset A} (hx : x ∈ T) (hy : y ∈ T)
    (hv : ∀ a ∈ T, 0 < v a) :
    rankMeasure v T {r | [x, y].Sublist r} = ENNReal.ofReal (pairwiseProb v x y) := by
  rw [rankMeasure_apply_of_pos hv]
  exact congrArg ENNReal.ofReal (sum_rankProb_sublist hxy T hx hy hv)

-- Axiom 1, Theorem 8, p. 69
theorem theorem8 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (x + y + z) * (y / (y + z)) = x * y / (x * y + x * z + y * z) * (x / (x + y)) ↔
      x / (x + y) = y / (y + z) := by
  rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity),
    div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have : z * (y ^ 2 - x * z) * (x * y) = 0 := by linear_combination h
    have hz' : z * (x * y) ≠ 0 := by positivity
    have : y ^ 2 - x * z = 0 := by
      rcases mul_eq_zero.1 this with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd h'' hz.ne'
        · exact h''
      · exact absurd h' (by positivity)
    linear_combination -this
  · intro h
    linear_combination (-(x * y * z)) * h

end Ranking

section Utility

/-! ### §3.B–D: Decomposable preference structures (pp. 78–90)

A gamble `aρb` has the outcome `a` if the event `ρ` occurs and `b` otherwise. A decomposable
preference structure couples preference among gambles and pure alternatives with the subjective
likelihood of events through the decomposition axiom (p. 78). If some pure alternatives are
discriminated imperfectly, the events fall into at most three classes of equal likelihood (Theorem
10, p. 80). -/

variable {A E : Type*} [DecidableEq A] [DecidableEq E] [MeasurableSpace A]
  [MeasurableSingletonClass A] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The gamble `aρb` has the outcome `win` if `event` occurs and `lose` otherwise (p. 78). -/
structure Gamble (A E : Type*) where
  /-- The outcome if the event occurs. -/
  win : A
  /-- The event. -/
  event : E
  /-- The outcome if the event does not occur. -/
  lose : A
  deriving DecidableEq

instance : MeasurableSpace (Gamble A E) := ⊤

instance : DiscreteMeasurableSpace (Gamble A E) := ⟨fun _ ↦ trivial⟩

/-- The alternatives `S(A, E) = (A × E × A) ∪ A` are the gambles and the pure alternatives (p. 78).
-/
abbrev Alternative (A E : Type*) := Gamble A E ⊕ A

/-- A decomposable preference structure couples choice `P` among the alternatives with choice `Q`
among events by subjective likelihood, each satisfying Axiom 1, through Axiom 2 (Definition 5, p.
78). -/
structure DecomposablePreference (A E : Type*) [DecidableEq A] [DecidableEq E] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace E] [MeasurableSingletonClass E] where
  /-- Choice among gambles and pure alternatives by preference. -/
  P : ChoiceFn (Alternative A E)
  /-- Choice among events by subjective likelihood. -/
  Q : ChoiceFn E
  /-- Axiom 2, `P(aρb, aσb) = P(a, b) Q(ρ, σ) + P(b, a) Q(σ, ρ)` for `a ≠ b` (p. 78). -/
  axiom2 : ∀ a b : A, a ≠ b → ∀ ρ σ : E,
    P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      P.binary (.inr a) (.inr b) * Q.binary ρ σ + P.binary (.inr b) (.inr a) * Q.binary σ ρ
  /-- `P` satisfies Axiom 1. -/
  axiom1P : P.HasChoiceAxiom
  /-- `Q` satisfies Axiom 1. -/
  axiom1Q : Q.HasChoiceAxiom

-- Axiom 2
theorem axiom2_unguarded_false [Nontrivial E] [Inhabited A]
    (P : ChoiceFn (Alternative A E)) (Q : ChoiceFn E)
    (h : ∀ (a b : A) (ρ σ : E),
      P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
        P.binary (.inr a) (.inr b) * Q.binary ρ σ + P.binary (.inr b) (.inr a) * Q.binary σ ρ) :
    False := by
  obtain ⟨ρ, σ, hρσ⟩ := exists_pair_ne E
  set a := (default : A)
  have hself := P.binary_self (Sum.inr a)
  have hQc := Q.binary_complement hρσ
  have hne : (Sum.inl ⟨a, ρ, a⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, a⟩ := by
    simpa using hρσ
  have hPc := P.binary_complement hne
  have h1 := h a a ρ σ
  have h2 := h a a σ ρ
  rw [hself] at h1 h2
  linarith

namespace DecomposablePreference

variable (dp : DecomposablePreference A E)

/-- `dp.alt a b` is the choice probability `P(a, b)` between pure alternatives. -/
noncomputable def alt (a b : A) : ℝ := dp.P.binary (.inr a) (.inr b)

/-- `dp.gam g h` is the choice probability `P(g, h)` between gambles. -/
noncomputable def gam (g h : Gamble A E) : ℝ := dp.P.binary (.inl g) (.inl h)

variable {dp}

-- Theorems 13 and 14, pp. 87
theorem gam_of_alt_eq_one {a b : A} (hab : a ≠ b) (h1 : dp.alt a b = 1)
    (ρ σ : E) : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.Q.binary ρ σ := by
  have hc := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  simp only [alt] at h1
  have hba : dp.P.binary (Sum.inr b) (Sum.inr a) = 0 := by linarith
  simp only [gam]
  rw [dp.axiom2 a b hab ρ σ, h1, hba]
  ring

/-- `ρ ≿ σ` holds when `Q(ρ, σ) ≥ 1/2`, so that `ρ` is deemed at least as likely as `σ` (Definition
6, p. 79). -/
def EventPref (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  1 / 2 ≤ dp.Q.binary ρ σ

/-- Events `ρ` and `σ` are equi-likely, `ρ ∼ σ`, when `ρ ≿ σ` and `σ ≿ ρ`. -/
def EventIndiff (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  EventPref dp ρ σ ∧ EventPref dp σ ρ

theorem eventIndiff_refl (dp : DecomposablePreference A E) (ρ : E) :
    EventIndiff dp ρ ρ := by
  unfold EventIndiff EventPref
  rw [dp.Q.binary_self]
  norm_num

theorem EventIndiff.symm {ρ σ : E} (h : EventIndiff dp ρ σ) :
    EventIndiff dp σ ρ := ⟨h.2, h.1⟩

theorem eventIndiff_iff_eq_half {ρ σ : E} (hne : ρ ≠ σ) :
    EventIndiff dp ρ σ ↔ dp.Q.binary ρ σ = 1 / 2 := by
  have hc := dp.Q.binary_complement hne
  unfold EventIndiff EventPref
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

theorem ne_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) : ρ ≠ σ :=
  fun he ↦ h (he ▸ eventIndiff_refl dp ρ)

theorem eventPref_total (ρ σ : E) : EventPref dp ρ σ ∨ EventPref dp σ ρ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · exact .inl (eventIndiff_refl dp ρ).1
  have hc := dp.Q.binary_complement hρσ
  unfold EventPref
  by_contra! h
  linarith [h.1, h.2]

theorem gt_half_or_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) :
    1 / 2 < dp.Q.binary ρ σ ∨ 1 / 2 < dp.Q.binary σ ρ := by
  have hc := dp.Q.binary_complement (ne_of_not_eventIndiff h)
  by_contra! hcon
  exact h ⟨show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2],
    show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2]⟩

/-- A structure is nondegenerate if `P(a, b) ≠ 0, 1/2, 1` for some distinct `a` and `b`, which is
the hypothesis of Theorem 10 (p. 80). -/
def Nondegenerate (dp : DecomposablePreference A E) : Prop :=
  ∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 0 ∧ dp.alt a b ≠ 1 / 2 ∧ dp.alt a b ≠ 1

private theorem alt_pos_pos {a b : A} (hab : a ≠ b) (h0 : dp.alt a b ≠ 0)
    (h1 : dp.alt a b ≠ 1) :
    0 < dp.alt a b ∧ 0 < dp.alt b a ∧ dp.alt a b + dp.alt b a = 1 := by
  have hc : dp.alt a b + dp.alt b a = 1 := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have hp0 : 0 ≤ dp.alt a b := dp.P.binary_nonneg _ _
  have hq0 : 0 ≤ dp.alt b a := dp.P.binary_nonneg _ _
  refine ⟨lt_of_le_of_ne hp0 (Ne.symm h0), ?_, hc⟩
  rcases eq_or_lt_of_le hq0 with heq | hlt
  · exact absurd (by linarith : dp.alt a b = 1) h1
  · exact hlt

private theorem mix_pos {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < p' + (p - p') * q := by
  rcases eq_or_lt_of_le hq1 with rfl | hq
  · linarith
  · nlinarith [mul_pos hp' (show (0 : ℝ) < 1 - q by linarith), mul_nonneg hp.le hq0]

private theorem mix_lt_one {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hpp' : p + p' = 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p' + (p - p') * q < 1 := by
  have h := mix_pos hp' hp hq0 hq1
  nlinarith [h]

private theorem gam_mix {a b : A} (hab : a ≠ b) {x y : E} (hxy : x ≠ y) :
    dp.gam ⟨a, x, b⟩ ⟨a, y, b⟩ =
      dp.alt b a + (dp.alt a b - dp.alt b a) * dp.Q.binary x y := by
  have hq := dp.Q.binary_complement hxy
  simp only [gam, alt]
  rw [dp.axiom2 a b hab x y,
      show dp.Q.binary y x = 1 - dp.Q.binary x y by linarith]
  ring

-- Lemma 5, p. 80
theorem lemma5 {a b : A} (hab : a ≠ b)
    (h0 : dp.alt a b ≠ 0) (hhalf : dp.alt a b ≠ 1 / 2) (h1 : dp.alt a b ≠ 1)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ) :
    dp.alt a b * dp.alt b a *
        (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) +
      (dp.alt a b - dp.alt b a) ^ 2 *
        (dp.Q.binary ρ σ * dp.Q.binary σ τ * dp.Q.binary τ ρ -
          dp.Q.binary ρ τ * dp.Q.binary τ σ * dp.Q.binary σ ρ) = 0 := by
  obtain ⟨hpa, hpb, hsum⟩ := alt_pos_pos hab h0 h1
  have g12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have g23 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hστ
  have g13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hρτ
  have hbnds : ∀ x y : E, x ≠ y →
      0 < dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) ∧
        dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) < 1 := by
    intro x y hxy
    have hmix := gam_mix (dp := dp) hab hxy
    simp only [gam] at hmix
    rw [hmix]
    exact ⟨mix_pos hpa hpb (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y),
      mix_lt_one hpa hpb hsum (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y)⟩
  have himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨a, τ, b⟩} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact hbnds _ _ hρσ
      | exact hbnds _ _ hρσ.symm
      | exact hbnds _ _ hστ
      | exact hbnds _ _ hστ.symm
      | exact hbnds _ _ hρτ
      | exact hbnds _ _ hρτ.symm
  have hcyc := dp.axiom1P.binary_mul_cycle g12 g23 g13 himp
  have e12 := gam_mix (dp := dp) hab hρσ
  have e23 := gam_mix (dp := dp) hab hστ
  have e31 := gam_mix (dp := dp) hab hρτ.symm
  have e13 := gam_mix (dp := dp) hab hρτ
  have e32 := gam_mix (dp := dp) hab hστ.symm
  have e21 := gam_mix (dp := dp) hab hρσ.symm
  simp only [gam] at e12 e23 e31 e13 e32 e21
  rw [e12, e23, e31, e13, e32, e21] at hcyc
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at hcyc ⊢
  have hΔ : dp.alt a b - dp.alt b a ≠ 0 := by
    intro h
    exact hhalf (by linarith)
  refine mul_left_cancel₀ hΔ ?_
  rw [mul_zero]
  linear_combination hcyc

theorem eventPref_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventPref dp ρ σ) (h2 : EventPref dp σ τ) :
    EventPref dp ρ τ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · exact h2
  rcases eq_or_ne σ τ with rfl | hστ
  · exact h1
  rcases eq_or_ne ρ τ with rfl | hρτ
  · exact (eventIndiff_refl dp ρ).1
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  unfold EventPref at h1 h2 ⊢
  by_contra hcon
  push Not at hcon
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hq3 : 1 / 2 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at h5
  set q1 := dp.Q.binary ρ σ with hq1_def
  set q2 := dp.Q.binary σ τ with hq2_def
  set q3 := dp.Q.binary τ ρ with hq3_def
  have hb1 := dp.Q.binary_le_one ρ σ
  have hb2 := dp.Q.binary_le_one σ τ
  have hb3 := dp.Q.binary_le_one τ ρ
  have s0 : (0 : ℝ) ≤ (1 - q2) * (1 - q3) :=
    mul_nonneg (by linarith) (by linarith)
  have s1 : (1 - q1) * ((1 - q2) * (1 - q3)) ≤ q1 * ((1 - q2) * (1 - q3)) :=
    mul_le_mul_of_nonneg_right (by linarith) s0
  have s2 : q1 * ((1 - q2) * (1 - q3)) ≤ q1 * (q2 * (1 - q3)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have s3 : q1 * (q2 * (1 - q3)) ≤ q1 * (q2 * q3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0 : ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0 : ℝ) < 2 * (q1 + q2 + q3) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (show (0 : ℝ) ≤ q1 * q2 * q3 - (1 - q3) * (1 - q2) * (1 - q1) by
        nlinarith [s1, s2, s3])]

-- Lemma 6, p. 80
theorem lemma6 (hnd : Nondegenerate dp) : Std.Total (EventPref dp) ∧ IsTrans E (EventPref dp) :=
  ⟨⟨eventPref_total⟩, ⟨fun _ _ _ ↦ eventPref_trans hnd⟩⟩

theorem eventIndiff_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventIndiff dp ρ σ) (h2 : EventIndiff dp σ τ) :
    EventIndiff dp ρ τ :=
  ⟨eventPref_trans hnd h1.1 h2.1, eventPref_trans hnd h2.2 h1.2⟩

private theorem cubic_of_sum_eq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : x / (x + y) + y / (y + z) + z / (z + x) = 3 / 2) :
    (x - y) * (y - z) * (x - z) = 0 := by
  have h1 : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have h2 : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have h3 : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  field_simp at h
  linear_combination h

-- Lemma 7, p. 81
theorem lemma7 (hnd : Nondegenerate dp) {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ)
    (hρτ : ρ ≠ τ) (himp : dp.Q.ImperfectOn {ρ, σ, τ}) :
    EventIndiff dp ρ σ ∨ EventIndiff dp σ τ ∨ EventIndiff dp ρ τ := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hcyc := dp.axiom1Q.binary_mul_cycle hρσ hστ hρτ himp
  have hzero : dp.alt a b * dp.alt b a *
      (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) = 0 := by
    linear_combination h5 - (dp.alt a b - dp.alt b a) ^ 2 * hcyc
  have hsum32 : dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ = 3 / 2 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  obtain ⟨v, hpos, hrule⟩ := dp.axiom1Q.binaryRatioScaleOn himp
  have mρ : ρ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mσ : σ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mτ : τ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have pρ := hpos ρ mρ
  have pσ := hpos σ mσ
  have pτ := hpos τ mτ
  rw [hrule ρ mρ σ mσ hρσ, hrule σ mσ τ mτ hστ,
      hrule τ mτ ρ mρ (Ne.symm hρτ)] at hsum32
  simp only [pairwiseProb] at hsum32
  have key := cubic_of_sum_eq pρ pσ pτ hsum32
  rcases mul_eq_zero.mp key with h' | hρτ'
  · rcases mul_eq_zero.mp h' with hρσ' | hστ'
    · refine Or.inl ((eventIndiff_iff_eq_half hρσ).mpr ?_)
      rw [hrule ρ mρ σ mσ hρσ]
      exact (pairwiseProb_eq_half_iff pρ pσ).mpr (by linarith)
    · refine Or.inr (Or.inl ((eventIndiff_iff_eq_half hστ).mpr ?_))
      rw [hrule σ mσ τ mτ hστ]
      exact (pairwiseProb_eq_half_iff pσ pτ).mpr (by linarith)
  · refine Or.inr (Or.inr ((eventIndiff_iff_eq_half hρτ).mpr ?_))
    rw [hrule ρ mρ τ mτ hρτ]
    exact (pairwiseProb_eq_half_iff pρ pτ).mpr (by linarith)

private theorem boost (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : dp.Q.binary ρ σ = 1) (h2 : 1 / 2 < dp.Q.binary σ τ) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hσρ : dp.Q.binary σ ρ = 0 := by
    linarith [dp.Q.binary_complement hρσ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h1, hσρ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0 : ℝ) < 2 * (1 + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg one_pos.le (dp.Q.binary_nonneg σ τ))
        (dp.Q.binary_nonneg τ ρ))]

private theorem boost' (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : dp.Q.binary σ τ = 1) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hτσ : dp.Q.binary τ σ = 0 := by
    linarith [dp.Q.binary_complement hστ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h2, hτσ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0 : ℝ) < 2 * (dp.Q.binary ρ σ + 1 + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg (dp.Q.binary_nonneg ρ σ) one_pos.le)
        (dp.Q.binary_nonneg τ ρ))]

private theorem no_strict_cycle (hnd : Nondegenerate dp) {ρ σ τ : E} (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ρ) : False := by
  have hle : EventPref dp ρ τ :=
    eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
  have hc := dp.Q.binary_complement hρτ
  unfold EventPref at hle
  linarith

private theorem binary_eq_one_of_lt (hnd : Nondegenerate dp) {ρ σ τ : E}
    (nρσ : ¬EventIndiff dp ρ σ) (nρτ : ¬EventIndiff dp ρ τ) (nστ : ¬EventIndiff dp σ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ) : dp.Q.binary ρ τ = 1 := by
  have dρσ := ne_of_not_eventIndiff nρσ
  have dρτ := ne_of_not_eventIndiff nρτ
  have dστ := ne_of_not_eventIndiff nστ
  have hρτ : 1 / 2 < dp.Q.binary ρ τ := by
    have hle := eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
    unfold EventPref at hle
    exact lt_of_le_of_ne hle fun he ↦ nρτ ((eventIndiff_iff_eq_half dρτ).mpr he.symm)
  by_cases hA : dp.Q.binary ρ σ = 1
  · exact boost hnd dρσ dστ dρτ hA h2
  by_cases hB : dp.Q.binary σ τ = 1
  · exact boost' hnd dρσ dστ dρτ h1 hB
  by_contra hC
  have core : ∀ u w : E, u ≠ w → 1 / 2 < dp.Q.binary u w → dp.Q.binary u w ≠ 1 →
      (0 < dp.Q.binary u w ∧ dp.Q.binary u w < 1) ∧
        0 < dp.Q.binary w u ∧ dp.Q.binary w u < 1 := by
    intro u w huw hgt hne1
    have hc := dp.Q.binary_complement huw
    have hlt := lt_of_le_of_ne (dp.Q.binary_le_one u w) hne1
    exact ⟨⟨by linarith, hlt⟩, by constructor <;> linarith⟩
  have himp : dp.Q.ImperfectOn {ρ, σ, τ} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact (core _ _ dρσ h1 hA).1
    · exact (core _ _ dρτ hρτ hC).1
    · exact (core _ _ dρσ h1 hA).2
    · exact absurd rfl hxy
    · exact (core _ _ dστ h2 hB).1
    · exact (core _ _ dρτ hρτ hC).2
    · exact (core _ _ dστ h2 hB).2
    · exact absurd rfl hxy
  rcases lemma7 hnd dρσ dστ dρτ himp with h | h | h
  · exact nρσ h
  · exact nστ h
  · exact nρτ h

private theorem no_four_chain (hnd : Nondegenerate dp) {ρ σ τ ω : E}
    (nρσ : ¬EventIndiff dp ρ σ) (nρτ : ¬EventIndiff dp ρ τ)
    (nρω : ¬EventIndiff dp ρ ω) (nστ : ¬EventIndiff dp σ τ)
    (nτω : ¬EventIndiff dp τ ω)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ω) : False := by
  have dρτ := ne_of_not_eventIndiff nρτ
  have dρω := ne_of_not_eventIndiff nρω
  have dτω := ne_of_not_eventIndiff nτω
  have hQρτ := binary_eq_one_of_lt hnd nρσ nρτ nστ h1 h2
  have hQρω : dp.Q.binary ρ ω = 1 := boost hnd dρτ dτω dρω hQρτ h3
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone dρτ dτω dρω
  have hτρ : dp.Q.binary τ ρ = 0 := by
    linarith [dp.Q.binary_complement dρτ]
  have hωρ : dp.Q.binary ω ρ = 0 := by
    linarith [dp.Q.binary_complement dρω]
  rw [hQρτ, hτρ, hωρ] at h5
  have h5' : dp.alt a b * dp.alt b a * (2 * dp.Q.binary τ ω - 1) = 0 := by
    linear_combination h5
  have : dp.Q.binary τ ω = 1 / 2 := by
    rcases mul_eq_zero.mp h5' with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  exact nτω ((eventIndiff_iff_eq_half dτω).mpr this)

private theorem no_chain_insert (hnd : Nondegenerate dp) {a b c ω : E}
    (nab : ¬EventIndiff dp a b) (nac : ¬EventIndiff dp a c)
    (naω : ¬EventIndiff dp a ω) (nbc : ¬EventIndiff dp b c)
    (nbω : ¬EventIndiff dp b ω) (ncω : ¬EventIndiff dp c ω)
    (sab : 1 / 2 < dp.Q.binary a b) (sbc : 1 / 2 < dp.Q.binary b c) :
    False := by
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    fun n h ↦ n h.symm
  rcases gt_half_or_of_not_eventIndiff naω with haω | hωa
  · rcases gt_half_or_of_not_eventIndiff nbω with hbω | hωb
    · rcases gt_half_or_of_not_eventIndiff ncω with hcω | hωc
      · exact no_four_chain hnd nab nac naω nbc ncω sab sbc hcω
      · exact no_four_chain hnd nab naω nac nbω (N ncω) sab hbω hωc
    · exact no_four_chain hnd naω nab nac (N nbω) nbc haω hωb sbc
  · exact no_four_chain hnd (N naω) (N nbω) (N ncω) nab nbc hωa sab sbc

-- Lemma 8, p. 81
theorem lemma8 (hnd : Nondegenerate dp) (ρ σ τ ω : E) :
    EventIndiff dp ρ σ ∨ EventIndiff dp ρ τ ∨ EventIndiff dp ρ ω ∨
      EventIndiff dp σ τ ∨ EventIndiff dp σ ω ∨ EventIndiff dp τ ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨nρσ, nρτ, nρω, nστ, nσω, nτω⟩ := hcon
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    fun n h ↦ n h.symm
  rcases gt_half_or_of_not_eventIndiff nρσ with h1 | h1'
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρσ nρτ nρω nστ nσω nτω h1 h2
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nρτ) h1 h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρτ nρσ nρω (N nστ) nτω nσω h3 h2'
      · exact no_chain_insert hnd (N nρτ) (N nστ) nτω nρσ nρω nσω h3' h1
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd (N nρσ) nστ nσω nρτ nρω nτω h1' h3
      · exact no_chain_insert hnd nστ (N nρσ) nσω (N nρτ) nτω nρω h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nστ) h1' h3 h2'
      · exact no_chain_insert hnd (N nστ) (N nρτ) nτω (N nρσ) nσω nρω h2' h1'

-- Theorem 10, p. 80
theorem theorem10 (hnd : Nondegenerate dp) :
    Equivalence (EventIndiff dp) ∧ ∀ ρ σ τ ω : E, EventIndiff dp ρ σ ∨ EventIndiff dp ρ τ ∨
      EventIndiff dp ρ ω ∨ EventIndiff dp σ τ ∨ EventIndiff dp σ ω ∨ EventIndiff dp τ ω :=
  ⟨⟨eventIndiff_refl dp, EventIndiff.symm, eventIndiff_trans hnd⟩, lemma8 hnd⟩

private theorem q_congr_left (hnd : Nondegenerate dp) {ρ ρ' σ : E}
    (h : EventIndiff dp ρ ρ') (hρσ : ρ ≠ σ) (hρ'σ : ρ' ≠ σ) :
    dp.Q.binary ρ' σ = dp.Q.binary ρ σ := by
  rcases eq_or_ne ρ ρ' with rfl | hρρ'
  · rfl
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have hhalf1 : dp.Q.binary ρ ρ' = 1 / 2 := (eventIndiff_iff_eq_half hρρ').mp h
  have hhalf2 : dp.Q.binary ρ' ρ = 1 / 2 := by
    linarith [dp.Q.binary_complement hρρ']
  have h5 := lemma5 hab h0 hhalf hone hρρ' hρ'σ hρσ
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary σ ρ' = 1 - dp.Q.binary ρ' σ := by
    linarith [dp.Q.binary_complement hρ'σ]
  rw [hhalf1, hhalf2, f1, f2] at h5
  have key : (2 * (dp.alt a b * dp.alt b a) +
      (dp.alt a b - dp.alt b a) ^ 2 / 2) *
      (dp.Q.binary ρ' σ - dp.Q.binary ρ σ) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.mp key with h' | h'
  · nlinarith [mul_pos hpa hpb, sq_nonneg (dp.alt a b - dp.alt b a)]
  · linarith

-- Theorem 11, p. 82
theorem theorem11 (hnd : Nondegenerate dp) {ρ ρ' σ σ' : E}
    (h1 : EventIndiff dp ρ ρ') (h2 : EventIndiff dp σ σ')
    (hρσ : ρ ≠ σ) (hρ'σ' : ρ' ≠ σ') :
    dp.Q.binary ρ σ = dp.Q.binary ρ' σ' := by
  rcases eq_or_ne ρ' σ with rfl | hρ'σ
  · have e1 := (eventIndiff_iff_eq_half hρσ).mp h1
    have e2 := (eventIndiff_iff_eq_half hρ'σ').mp h2
    rw [e1, e2]
  · have s1 : dp.Q.binary ρ' σ = dp.Q.binary ρ σ := q_congr_left hnd h1 hρσ hρ'σ
    have s2 : dp.Q.binary σ' ρ' = dp.Q.binary σ ρ' :=
      q_congr_left hnd h2 (Ne.symm hρ'σ) (Ne.symm hρ'σ')
    have c1 := dp.Q.binary_complement hρ'σ
    have c2 := dp.Q.binary_complement hρ'σ'
    linarith [s1, s2, c1, c2]

-- §3, p. 85
theorem abs_two_mul_alt_sub_one {a b : A} (hab : a ≠ b) (h0 : dp.alt a b ≠ 0)
    (hhalf : dp.alt a b ≠ 1 / 2) (h1 : dp.alt a b ≠ 1) {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ)
    (hρτ : ρ ≠ τ) (hq : dp.Q.binary ρ σ = dp.Q.binary σ τ) (hρτ₁ : dp.Q.binary ρ τ = 1) :
    3 / 4 < dp.Q.binary ρ σ ∧ dp.Q.binary ρ σ < 1 ∧
      |2 * dp.alt a b - 1| = √(4 * dp.Q.binary ρ σ - 3) / (2 * dp.Q.binary ρ σ - 1) := by
  obtain ⟨hp, hp', hsum⟩ := alt_pos_pos hab h0 h1
  have h5 := lemma5 hab h0 hhalf h1 hρσ hστ hρτ
  have e₁ : dp.Q.binary τ ρ = 0 := by linarith [dp.Q.binary_complement hρτ]
  have e₂ : dp.Q.binary τ σ = 1 - dp.Q.binary ρ σ := by linarith [dp.Q.binary_complement hστ]
  have e₃ : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by linarith [dp.Q.binary_complement hρσ]
  have e₄ : dp.alt b a = 1 - dp.alt a b := by linarith
  rw [e₁, e₂, e₃, ← hq, hρτ₁, e₄] at h5
  set p := dp.alt a b
  set q := dp.Q.binary ρ σ
  have key : p * (1 - p) * (4 * q - 3) = (2 * p - 1) ^ 2 * (1 - q) ^ 2 := by
    linear_combination h5
  have hpp : 0 < p * (1 - p) := mul_pos hp (by linarith)
  have hd : 0 < (2 * p - 1) ^ 2 := by
    refine lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 fun h ↦ hhalf ?_))
    linarith
  have hq₁ : q < 1 := by
    refine lt_of_le_of_ne (dp.Q.binary_le_one ρ σ) fun h ↦ ?_
    rw [h] at key
    nlinarith
  have hq₃ : 3 / 4 < q := by
    have : 0 < (2 * p - 1) ^ 2 * (1 - q) ^ 2 := mul_pos hd (pow_pos (sub_pos.2 hq₁) 2)
    nlinarith
  refine ⟨hq₃, hq₁, ?_⟩
  have hsq : 4 * q - 3 = (|2 * p - 1| * (2 * q - 1)) ^ 2 := by
    rw [mul_pow, sq_abs]
    linear_combination 4 * key
  rw [eq_div_iff (by linarith : (0 : ℝ) < 2 * q - 1).ne', hsq,
    Real.sqrt_sq (mul_nonneg (abs_nonneg _) (by linarith))]

/-! #### §3.C: Additional axioms (pp. 83–86)

Axiom 3 identifies `aρb` with `bρ̄a`, Axiom 4 asks that neither all alternatives nor all events be
indifferent, and Axiom 5 posits an event as likely as its complement. Under them the classes are
exactly three, and the imperfect discriminations among pure alternatives share one probability. -/

section BooleanEvents

variable [BooleanAlgebra E]

/-- Axiom 3 asks that `P(aρb, x) = P(bρ̄a, x)` for every `x` other than the two gambles (p. 83). -/
def Complementation (dp : DecomposablePreference A E) : Prop :=
  ∀ (a b : A) (ρ : E) (x : Alternative A E),
    x ≠ .inl ⟨a, ρ, b⟩ → x ≠ .inl ⟨b, ρᶜ, a⟩ →
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x

-- Axiom 3
theorem complementation_unguarded_false [Nontrivial A]
    (dp : DecomposablePreference A E)
    (h : ∀ (a b : A) (ρ : E) (x : Alternative A E),
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x) :
    False := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have h1 : dp.P.binary (.inl ⟨a, ⊥, b⟩) (.inl ⟨b, ⊥ᶜ, a⟩) = 1 := by
    rw [h a b ⊥ (.inl ⟨b, ⊥ᶜ, a⟩)]
    exact dp.P.binary_self _
  have h2 : dp.P.binary (.inl ⟨b, ⊥ᶜ, a⟩) (.inl ⟨a, ⊥, b⟩) = 1 := by
    have e := h b a ⊥ᶜ (.inl ⟨a, ⊥, b⟩)
    rw [compl_compl] at e
    rw [e]
    exact dp.P.binary_self _
  have hne : (Sum.inl ⟨a, ⊥, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, ⊥ᶜ, a⟩ := by
    simp [hab]
  have := dp.P.binary_complement hne
  linarith

/-- Axiom 4 asks for distinct `a` and `b` with `P(a, b) ≠ 1/2` and distinct `ρ` and `σ` with
`Q(ρ, σ) ≠ 1/2` (p. 83). -/
def NontrivialPreference (dp : DecomposablePreference A E) : Prop :=
  (∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 1 / 2) ∧
    ∃ ρ σ : E, ρ ≠ σ ∧ dp.Q.binary ρ σ ≠ 1 / 2

-- Axioms 3 and 4, Lemma 9, p. 84
theorem lemma9 (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) (ρ σ : E) :
    dp.Q.binary ρ σ = dp.Q.binary σᶜ ρᶜ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rw [dp.Q.binary_self, dp.Q.binary_self]
  obtain ⟨⟨a, b, hab, hp⟩, -⟩ := ax4
  have hXY : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have hXY' : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, σᶜ, a⟩ := by
    simp [hab]
  have hY'X' : (Sum.inl ⟨b, σᶜ, a⟩ : Alternative A E) ≠ Sum.inl ⟨b, ρᶜ, a⟩ := by
    simpa using compl_injective.ne (Ne.symm hρσ)
  -- relabel the second gamble `aσb` as `bσ̄a`
  have flipY : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) := by
    have e := ax3 a b σ (.inl ⟨a, ρ, b⟩) hXY hXY'
    have c1 := dp.P.binary_complement hXY
    have c2 := dp.P.binary_complement hXY'
    linarith
  -- relabel the first gamble `aρb` as `bρ̄a`
  have flipX : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) =
      dp.P.binary (.inl ⟨b, ρᶜ, a⟩) (.inl ⟨b, σᶜ, a⟩) :=
    ax3 a b ρ (.inl ⟨b, σᶜ, a⟩) (Ne.symm hXY') hY'X'
  have key := flipY.trans flipX
  rw [dp.axiom2 a b hab ρ σ, dp.axiom2 b a (Ne.symm hab) ρᶜ σᶜ] at key
  have cAB := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have cQ := dp.Q.binary_complement hρσ
  have cQc := dp.Q.binary_complement (show ρᶜ ≠ σᶜ from compl_injective.ne hρσ)
  simp only [alt] at hp
  have hkey : (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) *
      (2 * dp.P.binary (Sum.inr a) (Sum.inr b) - 1) = 0 := by
    linear_combination key -
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQ +
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQc +
      (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) * cAB
  rcases mul_eq_zero.mp hkey with h0 | h0
  · linarith
  · exact absurd (by linarith : dp.P.binary (Sum.inr a) (Sum.inr b) = 1 / 2) hp

/-- An event `ρ` is neutral if `Q(ρ, ρ̄) = 1/2`, and by Lemma 10 the neutral events form Luce's
class `C(1/2)` (p. 85). -/
def Neutral (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  dp.Q.binary ρ ρᶜ = 1 / 2

theorem neutral_compl_iff [Nontrivial E] (ρ : E) :
    Neutral dp ρᶜ ↔ Neutral dp ρ := by
  have hc := dp.Q.binary_complement (show ρ ≠ ρᶜ from (compl_ne_self (a := ρ)).symm)
  unfold Neutral
  rw [compl_compl]
  constructor <;> intro h <;> linarith

-- Lemma 10, p. 84
theorem neutral_indifferent [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (hσ : Neutral dp σ) (hρσ : ρ ≠ σ) :
    dp.Q.binary ρ σ = 1 / 2 := by
  have iρ : EventIndiff dp ρ ρᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mpr hρ
  have iσ : EventIndiff dp σ σᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := σ)).symm).mpr hσ
  have h11 := theorem11 hnd iρ iσ hρσ (compl_injective.ne hρσ)
  have h9 := lemma9 ax3 ax4 ρᶜ σᶜ
  rw [compl_compl, compl_compl] at h9
  have hc := dp.Q.binary_complement hρσ
  linarith [h11, h9, hc]

/-- Axiom 5 posits an event as likely as its complement (p. 84). -/
def HasNeutralEvent (dp : DecomposablePreference A E) : Prop :=
  ∃ ε : E, dp.Q.binary ε εᶜ = 1 / 2

-- Lemma 10, p. 84
theorem neutral_of_indiff_neutral [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (h : EventIndiff dp σ ρ) : Neutral dp σ := by
  rcases eq_or_ne σ ρ with rfl | hne
  · exact hρ
  have hσρ : dp.Q.binary σ ρ = 1 / 2 := (eventIndiff_iff_eq_half hne).mp h
  have h9 := lemma9 ax3 ax4 σ ρ
  have hcc : dp.Q.binary ρᶜ σᶜ = 1 / 2 := by linarith
  have icc : EventIndiff dp σᶜ ρᶜ :=
    ((eventIndiff_iff_eq_half (compl_injective.ne (Ne.symm hne))).mpr hcc).symm
  have h11 := theorem11 hnd h icc (compl_ne_self (a := σ)).symm
    (compl_ne_self (a := ρ)).symm
  unfold Neutral at hρ ⊢
  linarith [h11]

private theorem exists_not_neutral [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) : ∃ ρ : E, ¬Neutral dp ρ := by
  by_contra! hall
  obtain ⟨ρ₀, σ₀, hρσ₀, hq₀⟩ := ax4.2
  exact hq₀ (neutral_indifferent hnd ax3 ax4 (hall ρ₀) (hall σ₀) hρσ₀)

-- Axioms 3–5, Lemma 11, p. 85
theorem lemma11 [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ε ρ : E, ¬EventIndiff dp ε ρ ∧ ¬EventIndiff dp ε ρᶜ ∧
      ¬EventIndiff dp ρ ρᶜ := by
  obtain ⟨ε, hε⟩ := ax5
  obtain ⟨ρ, hρ⟩ := exists_not_neutral hnd ax3 ax4
  exact ⟨ε, ρ, fun h ↦ hρ (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm),
    fun h ↦ hρ ((neutral_compl_iff ρ).mp
      (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm)),
    fun h ↦ hρ ((eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mp h)⟩

-- Axioms 3–5, Theorem 12, p. 84
theorem theorem12 [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ρ₁ ρ₂ ρ₃ : E,
      (¬EventIndiff dp ρ₁ ρ₂ ∧ ¬EventIndiff dp ρ₁ ρ₃ ∧
        ¬EventIndiff dp ρ₂ ρ₃) ∧
      ∀ σ : E, EventIndiff dp σ ρ₁ ∨ EventIndiff dp σ ρ₂ ∨
        EventIndiff dp σ ρ₃ := by
  obtain ⟨ε, ρ, n1, n2, n3⟩ := lemma11 hnd ax3 ax4 ax5
  refine ⟨ε, ρ, ρᶜ, ⟨n1, n2, n3⟩, fun σ ↦ ?_⟩
  rcases lemma8 hnd σ ε ρ ρᶜ with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h n1
  · exact absurd h n2
  · exact absurd h n3

-- Theorem 12, §3, p. 85
theorem exists_class_representatives [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) (ax5 : HasNeutralEvent dp) :
    ∃ ρ σ τ : E, ¬EventIndiff dp ρ σ ∧ ¬EventIndiff dp σ τ ∧ ¬EventIndiff dp ρ τ ∧
      1 / 2 < dp.Q.binary ρ σ ∧ dp.Q.binary ρ σ = dp.Q.binary σ τ ∧ dp.Q.binary ρ τ = 1 := by
  obtain ⟨ε, hε⟩ := ax5
  -- an event more likely than its complement
  obtain ⟨ρ, hρ⟩ : ∃ ρ : E, 1 / 2 < dp.Q.binary ρ ρᶜ := by
    obtain ⟨ρ, hρ⟩ := exists_not_neutral hnd ax3 ax4
    have hc := dp.Q.binary_complement (compl_ne_self (a := ρ)).symm
    rcases lt_or_gt_of_ne (show dp.Q.binary ρ ρᶜ ≠ 1 / 2 from hρ) with h | h
    · exact ⟨ρᶜ, by rw [compl_compl]; linarith⟩
    · exact ⟨ρ, h⟩
  have hρc := dp.Q.binary_complement (compl_ne_self (a := ρ)).symm
  have iε : EventIndiff dp ε εᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := ε)).symm).mpr hε
  have nρε : ¬EventIndiff dp ρ ε := fun h ↦
    hρ.ne' (neutral_of_indiff_neutral hnd ax3 ax4 hε h)
  have nερ : ¬EventIndiff dp ε ρᶜ := fun h ↦
    hρ.ne' ((neutral_compl_iff ρ).mp (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm))
  have nρρ : ¬EventIndiff dp ρ ρᶜ := fun h ↦
    hρ.ne' ((eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mp h)
  have dρε := ne_of_not_eventIndiff nρε
  have dερ := ne_of_not_eventIndiff nερ
  have hq : dp.Q.binary ρ ε = dp.Q.binary ε ρᶜ := by
    rw [lemma9 ax3 ax4 ρ ε]
    exact theorem11 hnd iε.symm (eventIndiff_refl dp ρᶜ)
      (fun h ↦ dρε (compl_injective h).symm) dερ
  -- `ρ ≻ ε`, else `ρ̄ ≻ ε ≻ ρ` against `ρ ≻ ρ̄`
  have hq₁ : 1 / 2 < dp.Q.binary ρ ε := by
    refine (lt_or_gt_of_ne fun h ↦ nρε ((eventIndiff_iff_eq_half dρε).mpr h)).resolve_left
      fun h ↦ ?_
    have hle := eventPref_trans hnd
      (show EventPref dp ρᶜ ε by unfold EventPref; linarith [dp.Q.binary_complement dερ])
      (show EventPref dp ε ρ by unfold EventPref; linarith [dp.Q.binary_complement dρε])
    unfold EventPref at hle
    linarith
  exact ⟨ρ, ε, ρᶜ, nρε, nερ, nρρ, hq₁, hq,
    binary_eq_one_of_lt hnd nρε nρρ nερ hq₁ (by rwa [← hq])⟩

-- Theorem 12, §3, p. 85
theorem exists_abs_two_mul_alt_sub_one [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) (ax5 : HasNeutralEvent dp) :
    ∃ q : ℝ, 3 / 4 < q ∧ q < 1 ∧ ∀ a b : A, a ≠ b → dp.alt a b ≠ 0 → dp.alt a b ≠ 1 / 2 →
      dp.alt a b ≠ 1 → |2 * dp.alt a b - 1| = √(4 * q - 3) / (2 * q - 1) := by
  obtain ⟨ρ, σ, τ, nρσ, nστ, nρτ, -, hq, hρτ⟩ := exists_class_representatives hnd ax3 ax4 ax5
  have dρσ := ne_of_not_eventIndiff nρσ
  have dστ := ne_of_not_eventIndiff nστ
  have dρτ := ne_of_not_eventIndiff nρτ
  obtain ⟨a, b, hab, h0, hhalf, h1⟩ := hnd
  obtain ⟨hq₃, hq₁, -⟩ := abs_two_mul_alt_sub_one hab h0 hhalf h1 dρσ dστ dρτ hq hρτ
  exact ⟨_, hq₃, hq₁, fun a b hab h0 hhalf h1 ↦
    (abs_two_mul_alt_sub_one hab h0 hhalf h1 dρσ dστ dρτ hq hρτ).2.2⟩

end BooleanEvents

/-! #### §3.D: A proposed experiment (pp. 86–90)

Luce's prediction concerns gambles whose outcomes are perfectly discriminated. When two gambles pay
their preferred outcomes on the same event, choice between them is a step function of the event
(Figure 7), and when they pay them on complementary events, the ratio scale obeys a product rule
that suggests factoring it into outcome and event weights. -/

-- Theorem 13, p. 86
theorem theorem13 {a b c d : A} {ρ σ : E}
    (hab : a ≠ b) (hcd : c ≠ d) (ha1 : dp.alt a b = 1) (hc1 : dp.alt c d = 1)
    (himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩}) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = dp.gam ⟨a, σ, b⟩ ⟨c, σ, d⟩ := by
  by_cases hρσ : ρ = σ
  · subst hρσ; rfl
  by_cases hacbd : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := hacbd
    simp only [gam]
    rw [dp.P.binary_self, dp.P.binary_self]
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, gam_of_alt_eq_one hcd hc1]
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have h13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  have h24 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hacbd
  obtain ⟨v, hpos, hrule⟩ := dp.axiom1P.binaryRatioScaleOn himp
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  simp only [gam] at e1 ⊢
  rw [hrule _ (by simp) _ (by simp) h12, hrule _ (by simp) _ (by simp) h34] at e1
  rw [hrule _ (by simp) _ (by simp) h13, hrule _ (by simp) _ (by simp) h24,
      pairwiseProb_eq_pairwiseProb_iff p1 p3 p2 p4]
  exact ((pairwiseProb_eq_pairwiseProb_iff p1 p2 p3 p4).mp e1).trans (mul_comm _ _)

variable [BooleanAlgebra E] in
-- Axiom 3, Theorem 14, p. 89, Theorem 4
theorem theorem14 [Nontrivial E] (ax3 : Complementation dp) {a b c d : A} {ρ σ : E}
    {v : Alternative A E → ℝ} (hab : a ≠ b) (hcd : c ≠ d) (ha1 : dp.alt a b = 1)
    (hd1 : dp.alt d c = 1)
    (hv : dp.P.BinaryRatioScaleOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩,
        .inl ⟨d, ρᶜ, c⟩, .inl ⟨d, σᶜ, c⟩} v) :
    v (.inl ⟨a, ρ, b⟩) * v (.inl ⟨d, ρᶜ, c⟩) = v (.inl ⟨a, σ, b⟩) * v (.inl ⟨d, σᶜ, c⟩) := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rfl
  have hacbd : ¬(a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩
    have := dp.P.binary_complement
      (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
    simp only [alt] at ha1 hd1
    linarith
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  have p5 := hpos (Sum.inl ⟨d, ρᶜ, c⟩) (by simp)
  have p6 := hpos (Sum.inl ⟨d, σᶜ, c⟩) (by simp)
  -- Axiom 3, witnessed against `aρb`, carries the scale from `cρd` to `dρ̄c`
  have hρc : v (.inl ⟨c, ρ, d⟩) = v (.inl ⟨d, ρᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, ρᶜ, c⟩ := by
      simp [(compl_ne_self (a := ρ)).symm]
    have e := ax3 c d ρ (.inl ⟨a, ρ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (pairwiseProb_eq_pairwiseProb_iff p3 p1 p5 p1).mp e
    exact mul_right_cancel₀ (ne_of_gt p1) this
  have hσc : v (.inl ⟨c, σ, d⟩) = v (.inl ⟨d, σᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, σᶜ, c⟩ := by
      simp [(compl_ne_self (a := σ)).symm]
    have e := ax3 c d σ (.inl ⟨a, σ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (pairwiseProb_eq_pairwiseProb_iff p4 p2 p6 p2).mp e
    exact mul_right_cancel₀ (ne_of_gt p2) this
  -- both same-outcome comparisons reduce to `Q(ρ, σ)`
  have hcd0 : dp.alt c d = 0 := by
    have hc := dp.P.binary_complement
      (show (Sum.inr c : Alternative A E) ≠ Sum.inr d by simpa using hcd)
    simp only [alt] at hd1 ⊢
    linarith
  have e2 : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ = dp.Q.binary σ ρ := by
    simp only [gam, alt] at hcd0 hd1 ⊢
    rw [dp.axiom2 c d hcd ρ σ, hcd0, hd1]
    ring
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have e2' : dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = dp.Q.binary ρ σ := by
    have hPc : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ + dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = 1 := by
      simpa [gam] using dp.P.binary_complement h34
    have hQc := dp.Q.binary_complement hρσ
    linarith
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, e2']
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  simp only [gam] at e1
  rw [hrule _ (by simp) _ (by simp) h12,
      hrule _ (by simp) _ (by simp) (Ne.symm h34)] at e1
  have hcross := (pairwiseProb_eq_pairwiseProb_iff p1 p2 p4 p3).mp e1
  rw [hρc, hσc] at hcross
  linarith [hcross, mul_comm (v (.inl ⟨d, σᶜ, c⟩)) (v (.inl ⟨a, σ, b⟩))]

-- Theorem 13, pp. 89–90
theorem gam_of_factored {S : Set (Gamble A E)} {v : Alternative A E → ℝ}
    {w : A → A → ℝ} {φ : E → ℝ}
    (hv : dp.P.BinaryRatioScaleOn (Sum.inl '' S) v) (hφ : ∀ τ, 0 < φ τ)
    (hfac : ∀ x y τ, (⟨x, τ, y⟩ : Gamble A E) ∈ S →
      v (.inl ⟨x, τ, y⟩) = w x y * φ τ)
    {a b c d : A} {ρ : E} (h₁ : (⟨a, ρ, b⟩ : Gamble A E) ∈ S)
    (h₂ : (⟨c, ρ, d⟩ : Gamble A E) ∈ S) (hacbd : ¬(a = c ∧ b = d)) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = w a b / (w a b + w c d) := by
  have hg : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  simp only [gam]
  rw [hv.2 _ ⟨_, h₁, rfl⟩ _ ⟨_, h₂, rfl⟩ hg, pairwiseProb, hfac a b ρ h₁, hfac c d ρ h₂,
    ← add_mul, mul_div_mul_right _ _ (hφ ρ).ne']

end DecomposablePreference

end Utility

section Learning

open Finset Matrix

/-! ### §4: Response-strength operators (pp. 93–106)

A learning event transforms the vector of response strengths, and the choice probabilities follow
from the strengths by the ratio rule. The alpha model takes the transformation to be a nonnegative
matrix, the form Luce derives from the unboundedness, superposition and independence-of-unit
conditions, the beta model multiplies each strength by a constant, and the gamma model adds a
constant as well. -/

variable {A : Type*} [Fintype A]

/-! #### §4.C: The alpha model -/

/-- An operator `M` satisfies the proportional change assumption (p. 97) with constant `a` if it
multiplies the total strength of every positive vector by `a`. -/
def ProportionalChange (M : Matrix A A ℝ) (a : ℝ) : Prop :=
  ∀ v : A → ℝ, (∀ i, 0 < v i) → ∑ i, (M *ᵥ v) i = a * ∑ i, v i

private theorem sum_mulVec_eq_sum_mul (M : Matrix A A ℝ) (v : A → ℝ) :
    ∑ i, (M *ᵥ v) i = ∑ j, (∑ i, M i j) * v j := by
  simp only [mulVec, dotProduct, sum_mul]
  exact sum_comm

variable [DecidableEq A]

-- (1), p. 98
theorem proportionalChange_iff {M : Matrix A A ℝ} {a : ℝ} :
    ProportionalChange M a ↔ ∀ j, ∑ i, M i j = a := by
  classical
  refine ⟨fun h j ↦ ?_, fun h v _ ↦ by simp [sum_mulVec_eq_sum_mul, h, mul_sum]⟩
  have h₁ := h 1 fun _ ↦ one_pos
  have h₂ := h (1 + Pi.single j 1) fun i ↦ by
    rw [Pi.add_apply, Pi.single_apply]; split_ifs <;> norm_num
  simp [mulVec_add, sum_add_distrib, mul_add, h₁] at h₂
  linarith

-- p. 97
theorem ProportionalChange.ratioProb_mulVec {M : Matrix A A ℝ} {a : ℝ}
    (h : ProportionalChange M a) (v : A → ℝ) :
    ratioProb (M *ᵥ v) univ = (a⁻¹ • M) *ᵥ ratioProb v univ := by
  have hsum : ∑ i, (M *ᵥ v) i = a * ∑ i, v i := by
    simp [sum_mulVec_eq_sum_mul, proportionalChange_iff.1 h, mul_sum]
  simp only [ratioProb_univ, hsum, mulVec_smul, smul_mulVec, smul_smul, mul_inv]
  rw [mul_comm]

-- p. 99 [bush-mosteller-1955]
theorem ProportionalChange.pairwiseProb_mulVec {M : Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ}
    (h : ProportionalChange M a) (ha : a ≠ 0) (hM : ∀ i j, 0 ≤ M i j) {v : Fin 2 → ℝ}
    (hv : v 0 + v 1 ≠ 0) :
    pairwiseProb (M *ᵥ v) 0 1 = (M 0 0 - M 0 1) / a * pairwiseProb v 0 1 +
      (1 - (M 0 0 - M 0 1) / a) * (M 0 1 / (M 0 1 + M 1 0)) := by
  have hP (w : Fin 2 → ℝ) : pairwiseProb w 0 1 = ratioProb w univ 0 := by
    simp [pairwiseProb, ratioProb, Fin.sum_univ_two]
  have hcol : M 0 0 + M 1 0 = a := by simpa [Fin.sum_univ_two] using proportionalChange_iff.1 h 0
  have hsum := ratioProb_sum_eq_one v univ (by simpa [Fin.sum_univ_two] using hv)
  rw [hP, hP, h.ratioProb_mulVec]
  simp only [Fin.sum_univ_two] at hsum
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  rcases eq_or_ne (M 0 1 + M 1 0) 0 with h' | h'
  · have : M 0 1 = 0 := by linarith [hM 0 1, hM 1 0]
    simp [this, div_eq_inv_mul, mul_assoc]
  · field_simp
    linear_combination (M 0 1 + M 1 0) * M 0 1 * hsum + M 0 1 * hcol

/-! #### §4.D: The beta model -/

-- p. 100
theorem eq_mul_of_independenceOfUnit {f : ℝ → ℝ} (h : ∀ k > 0, ∀ x > 0, f (k * x) = k * f x)
    {x : ℝ} (hx : 0 < x) : f x = f 1 * x := by
  simpa [mul_comm] using h x hx 1 one_pos

-- (i), p. 101
theorem ratioProb_mul_ratioProb (β : A → ℝ) {v : A → ℝ} (hv : ∑ j, v j ≠ 0) :
    ratioProb (β * ratioProb v univ) univ = ratioProb (β * v) univ := by
  rw [ratioProb_univ v, show β * ((∑ j, v j)⁻¹ • v) = (∑ j, v j)⁻¹ • (β * v) from
    mul_smul_comm _ _ _, ratioProb_smul (inv_ne_zero hv)]

-- p. 101
theorem ratioProb_mul_comm (β γ : A → ℝ) {p : A → ℝ} (hβ : ∑ j, β j * p j ≠ 0)
    (hγ : ∑ j, γ j * p j ≠ 0) :
    ratioProb (β * ratioProb (γ * p) univ) univ = ratioProb (γ * ratioProb (β * p) univ) univ := by
  rw [ratioProb_mul_ratioProb β (v := γ * p) hγ,
    ratioProb_mul_ratioProb γ (v := β * p) hβ, mul_left_comm]

-- (i), p. 101
theorem ratioProb_update_mul (i : A) (β : ℝ) {v : A → ℝ}
    (hv : ∑ j, v j ≠ 0) (j : A) :
    ratioProb (Function.update (1 : A → ℝ) i β * v) univ j =
      Function.update (1 : A → ℝ) i β j * ratioProb v univ j /
        (1 + (β - 1) * ratioProb v univ i) := by
  have hs : ∑ k, Function.update (1 : A → ℝ) i β k * ratioProb v univ k =
      1 + (β - 1) * ratioProb v univ i := by
    have h1 := ratioProb_sum_eq_one v univ hv
    rw [← add_sum_erase _ _ (mem_univ i)] at h1 ⊢
    rw [sum_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_erase hk)]]
    simp only [Function.update_self, Pi.one_apply, one_mul]
    linarith
  rw [← ratioProb_mul_ratioProb _ hv, ratioProb_eq_div _ _ _ (mem_univ _)]
  simp only [Pi.mul_apply, hs]

-- p. 102
theorem ratioProb_mul_fin_two (β : Fin 2 → ℝ) (hβ : β 1 ≠ 0) (v : Fin 2 → ℝ) :
    ratioProb (β * v) univ =
      ratioProb (Function.update (1 : Fin 2 → ℝ) 0 (β 0 / β 1) * v) univ := by
  conv_rhs => rw [← ratioProb_smul hβ, ← smul_mul_assoc]
  congr 2
  ext i; fin_cases i <;> simp [mul_div_cancel₀ _ hβ]

/-! #### §4.E: The gamma model -/

-- p. 106
theorem not_exists_ratioProb_gamma [Nontrivial A] {β γ : A → ℝ} (hβ : ∀ i, 0 < β i)
    (hγ : ∀ i, 0 ≤ γ i) (hγ₀ : γ ≠ 0) :
    ¬∃ F : (A → ℝ) → A → ℝ, ∀ v : A → ℝ, (∀ i, 0 < v i) →
      ratioProb (β * v + γ) univ = F (ratioProb v univ) := by
  classical
  rintro ⟨F, hF⟩
  obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := by
    by_contra! h
    exact hγ₀ (funext h)
  obtain ⟨j, hj⟩ := exists_ne i
  have pos (w : A → ℝ) (hw : ∀ k, 0 < w k) : 0 < ∑ k, (β * w + γ) k :=
    sum_pos (fun k _ ↦ by simp only [Pi.add_apply, Pi.mul_apply]; nlinarith [hβ k, hw k, hγ k])
      univ_nonempty
  have key (v : A → ℝ) (hv : ∀ k, 0 < v k) : β i * v i * γ j = γ i * (β j * v j) := by
    have hv2 (k : A) : 0 < ((2 : ℝ) • v) k := by simp [hv k]
    have e : ratioProb (β * ((2 : ℝ) • v) + γ) univ = ratioProb (β * v + γ) univ := by
      rw [hF _ hv2, hF _ hv, ratioProb_smul two_ne_zero]
    have ei := congrFun e i
    have ej := congrFun e j
    rw [ratioProb_eq_div _ _ _ (mem_univ _), ratioProb_eq_div _ _ _ (mem_univ _)] at ei ej
    rw [div_eq_div_iff (pos _ hv2).ne' (pos _ hv).ne'] at ei ej
    have : (β * ((2 : ℝ) • v) + γ) i * (β * v + γ) j = (β * ((2 : ℝ) • v) + γ) j * (β * v + γ) i :=
      mul_right_cancel₀ (pos _ hv).ne'
        (by linear_combination (β * v + γ) j * ei - (β * v + γ) i * ej)
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  have h₁ := key 1 fun _ ↦ one_pos
  have h₂ := key (Function.update 1 i 2) fun k ↦ by
    rcases eq_or_ne k i with rfl | hk <;> simp [*]
  simp only [Pi.one_apply, mul_one, Function.update_self, Function.update_of_ne hj] at h₁ h₂
  have hγj : γ j = 0 := by nlinarith [hβ i]
  exact hi (by nlinarith [hβ j])

end Learning

section PartialReinforcement

open Finset Matrix Polynomial

/-! #### §4.F: Partial reinforcement (pp. 107–110)

In a partial reinforcement experiment the organism chooses between `aρb` and `aρ̄b`, with `a` a
reward and `b` nothing, and Theorem 14 makes the product of their strengths independent of the
event. An alpha or gamma operator that keeps this product fixed confines the strengths to a few
values unless it does not learn or reduces to a beta operator, and a beta operator needs only
`β₁ β₂ = 1`. -/

variable {A E : Type*} [DecidableEq A] [DecidableEq E] [BooleanAlgebra E] [Nontrivial E]
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace E] [MeasurableSingletonClass E]

private theorem encard_le_of_isRoot {S : Set ℝ} {p : ℝ[X]} (hp : p ≠ 0) {n : ℕ}
    (hn : p.natDegree ≤ n) (h : ∀ x ∈ S, p.IsRoot x) : S.encard ≤ n :=
  calc S.encard ≤ (p.roots.toFinset : Set ℝ).encard :=
        Set.encard_le_encard fun x hx ↦ by simpa [mem_roots hp] using h x hx
    _ ≤ n := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact_mod_cast (Multiset.toFinset_card_le _).trans ((card_roots' p).trans hn)

-- Theorem 14, p. 108
theorem DecomposablePreference.strength_mul_strength_compl {dp : DecomposablePreference A E}
    (ax3 : dp.Complementation) {a b : A} {ρ σ : E} {v : Alternative A E → ℝ} (hab : a ≠ b)
    (ha : dp.alt a b = 1)
    (hv : dp.P.BinaryRatioScaleOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨b, ρ, a⟩, .inl ⟨b, σ, a⟩,
        .inl ⟨a, ρᶜ, b⟩, .inl ⟨a, σᶜ, b⟩} v) :
    v (.inl ⟨a, ρ, b⟩) * v (.inl ⟨a, ρᶜ, b⟩) = v (.inl ⟨a, σ, b⟩) * v (.inl ⟨a, σᶜ, b⟩) :=
  DecomposablePreference.theorem14 ax3 hab hab.symm ha ha hv

-- pp. 108–109
theorem ProportionalChange.encard_le_four_or {M : Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ}
    (h : ProportionalChange M a) (hM : ∀ i j, 0 ≤ M i j) {K : ℝ} (hK : 0 < K) :
    {x : ℝ | 0 < x ∧ (M *ᵥ ![x, K / x]) 0 * (M *ᵥ ![x, K / x]) 1 = K}.encard ≤ 4 ∨
      M = 1 ∨ M = !![0, 1; 1, 0] := by
  have hcol := proportionalChange_iff.1 h
  simp only [Fin.sum_univ_two] at hcol
  have h₀ := hcol 0
  have h₁ := hcol 1
  by_cases hc : M 0 0 * M 1 0 = 0 ∧ M 0 1 * M 1 1 = 0 ∧ M 1 0 * M 0 1 + M 0 0 * M 1 1 = 1
  · obtain ⟨h4, h0, h2⟩ := hc
    right
    rcases mul_eq_zero.1 h4 with h00 | h10
    · have h11 : M 1 1 = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · simp [h, h00] at h2
        · exact h
      have h01 : M 0 1 = 1 := by nlinarith [hM 0 1]
      right
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
    · have h01 : M 0 1 = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · simp [h, h10] at h2
      have h00 : M 0 0 = 1 := by nlinarith [hM 0 0]
      left
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
  · left
    refine encard_le_of_isRoot (p := C (M 0 0 * M 1 0) * X ^ 4 +
      C ((M 1 0 * M 0 1 + M 0 0 * M 1 1 - 1) * K) * X ^ 2 + C (M 0 1 * M 1 1 * K ^ 2))
      (fun hp ↦ hc ?_) (by compute_degree) ?_
    · have c4 := congrArg (coeff · 4) hp
      have c2 := congrArg (coeff · 2) hp
      have c0 := congrArg (coeff · 0) hp
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_zero] at c4 c2 c0
      norm_num at c4 c2 c0
      exact ⟨mul_eq_zero.2 c4, by simpa [hK.ne'] using c0, by
        rcases c2 with c2 | c2 <;> [linarith; exact absurd c2 hK.ne']⟩
    · rintro x ⟨hx, hxK⟩
      simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] at hxK
      simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      field_simp at hxK
      linear_combination hxK

-- p. 109
theorem ratioProb_mul_eq_of_mul_eq {β : Fin 2 → ℝ} {K x : ℝ} (hK : 0 < K) (hx : 0 < x)
    (h : β 0 * x * (β 1 * (K / x)) = K) (v : Fin 2 → ℝ) :
    ratioProb (β * v) univ = ratioProb (Function.update (1 : Fin 2 → ℝ) 0 (β 0 ^ 2) * v) univ := by
  have hβ : β 0 * β 1 = 1 := by
    field_simp at h
    nlinarith
  have h₁ := right_ne_zero_of_mul_eq_one hβ
  rw [ratioProb_mul_fin_two β h₁, show β 0 / β 1 = β 0 ^ 2 by
    rw [div_eq_iff h₁]; linear_combination -β 0 * hβ]

-- p. 110
theorem encard_le_two_or_gamma {β γ : Fin 2 → ℝ} {K : ℝ} (hK : 0 < K) :
    {x : ℝ | 0 < x ∧ (β 0 * x + γ 0) * (β 1 * (K / x) + γ 1) = K}.encard ≤ 2 ∨
      (β = 0 ∧ γ 0 * γ 1 = K) ∨ (γ = 0 ∧ β 0 * β 1 = 1) := by
  by_cases hc : β 0 * γ 1 = 0 ∧ (β 0 * β 1 - 1) * K + γ 0 * γ 1 = 0 ∧ γ 0 * β 1 = 0
  · obtain ⟨hA, hB, hC⟩ := hc
    right
    rcases eq_or_ne (β 0) 0 with h0 | h0
    · have hγ : γ 0 * γ 1 = K := by simp [h0] at hB; linarith
      have h1 : β 1 = 0 := by
        rcases mul_eq_zero.1 hC with h | h
        · simp [h] at hγ; linarith
        · exact h
      exact .inl ⟨funext fun i ↦ by fin_cases i <;> simp [h0, h1], hγ⟩
    · have hγ1 : γ 1 = 0 := (mul_eq_zero.1 hA).resolve_left h0
      have hβ : β 0 * β 1 = 1 := by
        simp only [hγ1, mul_zero, add_zero] at hB
        rcases mul_eq_zero.1 hB with h | h
        · linarith
        · exact absurd h hK.ne'
      have hγ0 : γ 0 = 0 := (mul_eq_zero.1 hC).resolve_right (right_ne_zero_of_mul_eq_one hβ)
      exact .inr ⟨funext fun i ↦ by fin_cases i <;> simp [hγ0, hγ1], hβ⟩
  · left
    refine encard_le_of_isRoot (p := C (β 0 * γ 1) * X ^ 2 +
      C ((β 0 * β 1 - 1) * K + γ 0 * γ 1) * X + C (γ 0 * β 1 * K))
      (fun hp ↦ hc ?_) (by compute_degree) ?_
    · have c2 := congrArg (coeff · 2) hp
      have c1 := congrArg (coeff · 1) hp
      have c0 := congrArg (coeff · 0) hp
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c2 c1 c0
      norm_num at c2 c1 c0
      exact ⟨mul_eq_zero.2 c2, c1, by simpa [hK.ne'] using c0⟩
    · rintro x ⟨hx, hxK⟩
      simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      field_simp at hxK
      linear_combination hxK

end PartialReinforcement

section BetaAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! #### §4.G: Asymptotic properties of the beta model (pp. 111–120)

With two alternatives and two outcomes, the ratio `vₙ` of the response strengths is a Markov chain
that moves by one of four steps on the log scale. Three equations govern its expectations, the
moment recursion (10), the identity (11), and the drift (16) of the expected log ratio, and from
them Theorems 15–18 relate the limit of `E(Pₙ)` to the moments of `vₙ` and `1/vₙ`. Each second part
is the first part for the model with the alternatives exchanged. -/

/-- The beta model for two alternatives and two outcomes multiplies the ratio `v = v(1)/v(2)` of the
response strengths by `β₁ⱼ` when alternative 1 is chosen and outcome `j` occurs, and divides it by
`β₂ⱼ` when alternative 2 is chosen, where outcome 1 follows the choice of `i` with probability `πᵢ`
(p. 112). -/
structure BetaLearner where
  /-- The multiplier of `v` after choice 1 and outcome 1. -/
  β₁₁ : ℝ
  /-- The multiplier of `v` after choice 1 and outcome 2. -/
  β₁₂ : ℝ
  /-- The divisor of `v` after choice 2 and outcome 1. -/
  β₂₁ : ℝ
  /-- The divisor of `v` after choice 2 and outcome 2. -/
  β₂₂ : ℝ
  /-- The probability of outcome 1 after choice 1. -/
  π₁ : ℝ
  /-- The probability of outcome 1 after choice 2. -/
  π₂ : ℝ
  β₁₁_pos : 0 < β₁₁
  β₁₂_pos : 0 < β₁₂
  β₂₁_pos : 0 < β₂₁
  β₂₂_pos : 0 < β₂₂
  π₁_nonneg : 0 ≤ π₁
  π₁_le_one : π₁ ≤ 1
  π₂_nonneg : 0 ≤ π₂
  π₂_le_one : π₂ ≤ 1

namespace BetaLearner

variable (m : BetaLearner)

/-- The transition (7) moves the log ratio `u = log v` by `log β₁₁`, `log β₁₂`, `−log β₂₁` or
`−log β₂₂` with probabilities `Pπ₁`, `P(1 − π₁)`, `(1 − P)π₂` and `(1 − P)(1 − π₂)`, where `P` is
the sigmoid of `u` (6). -/
noncomputable def kernel : Kernel ℝ ℝ :=
  Kernel.withDensity (Kernel.deterministic (· + Real.log m.β₁₁) (measurable_add_const _))
      (fun u _ ↦ ENNReal.ofReal (Real.sigmoid u * m.π₁)) +
    Kernel.withDensity (Kernel.deterministic (· + Real.log m.β₁₂) (measurable_add_const _))
      (fun u _ ↦ ENNReal.ofReal (Real.sigmoid u * (1 - m.π₁))) +
    Kernel.withDensity (Kernel.deterministic (· - Real.log m.β₂₁) (measurable_sub_const _))
      (fun u _ ↦ ENNReal.ofReal ((1 - Real.sigmoid u) * m.π₂)) +
    Kernel.withDensity (Kernel.deterministic (· - Real.log m.β₂₂) (measurable_sub_const _))
      (fun u _ ↦ ENNReal.ofReal ((1 - Real.sigmoid u) * (1 - m.π₂)))

-- (7)
theorem kernel_apply (u : ℝ) : m.kernel u =
    ENNReal.ofReal (Real.sigmoid u * m.π₁) • Measure.dirac (u + Real.log m.β₁₁) +
    ENNReal.ofReal (Real.sigmoid u * (1 - m.π₁)) • Measure.dirac (u + Real.log m.β₁₂) +
    ENNReal.ofReal ((1 - Real.sigmoid u) * m.π₂) • Measure.dirac (u - Real.log m.β₂₁) +
    ENNReal.ofReal ((1 - Real.sigmoid u) * (1 - m.π₂)) • Measure.dirac (u - Real.log m.β₂₂) := by
  simp only [kernel, FunLike.coe_add, Pi.add_apply]
  rw [Kernel.withDensity_apply _ (by fun_prop), Kernel.withDensity_apply _ (by fun_prop),
    Kernel.withDensity_apply _ (by fun_prop), Kernel.withDensity_apply _ (by fun_prop)]
  simp [Kernel.deterministic_apply]

private theorem w₁_nonneg (u : ℝ) : 0 ≤ Real.sigmoid u * m.π₁ :=
  mul_nonneg (Real.sigmoid_nonneg u) m.π₁_nonneg
private theorem w₂_nonneg (u : ℝ) : 0 ≤ Real.sigmoid u * (1 - m.π₁) :=
  mul_nonneg (Real.sigmoid_nonneg u) (sub_nonneg.2 m.π₁_le_one)
private theorem w₃_nonneg (u : ℝ) : 0 ≤ (1 - Real.sigmoid u) * m.π₂ :=
  mul_nonneg (sub_nonneg.2 (Real.sigmoid_le_one u)) m.π₂_nonneg
private theorem w₄_nonneg (u : ℝ) : 0 ≤ (1 - Real.sigmoid u) * (1 - m.π₂) :=
  mul_nonneg (sub_nonneg.2 (Real.sigmoid_le_one u)) (sub_nonneg.2 m.π₂_le_one)

-- (7)
theorem integral_kernel (f : ℝ → ℝ) (u : ℝ) : ∫ x, f x ∂m.kernel u =
    Real.sigmoid u * m.π₁ * f (u + Real.log m.β₁₁) +
    Real.sigmoid u * (1 - m.π₁) * f (u + Real.log m.β₁₂) +
    (1 - Real.sigmoid u) * m.π₂ * f (u - Real.log m.β₂₁) +
    (1 - Real.sigmoid u) * (1 - m.π₂) * f (u - Real.log m.β₂₂) := by
  have hi (c : ℝ) (a : ℝ) : Integrable f (ENNReal.ofReal c • Measure.dirac a) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [kernel_apply, integral_add_measure (((hi _ _).add_measure (hi _ _)).add_measure (hi _ _))
    (hi _ _), integral_add_measure ((hi _ _).add_measure (hi _ _)) (hi _ _),
    integral_add_measure (hi _ _) (hi _ _)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (m.w₁_nonneg u), ENNReal.toReal_ofReal (m.w₂_nonneg u),
    ENNReal.toReal_ofReal (m.w₃_nonneg u), ENNReal.toReal_ofReal (m.w₄_nonneg u)]

theorem kernel_apply_univ (u : ℝ) : m.kernel u Set.univ = 1 := by
  simp only [kernel_apply, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_add (m.w₁_nonneg u) (m.w₂_nonneg u),
    ← ENNReal.ofReal_add (add_nonneg (m.w₁_nonneg u) (m.w₂_nonneg u)) (m.w₃_nonneg u),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (m.w₁_nonneg u) (m.w₂_nonneg u))
      (m.w₃_nonneg u)) (m.w₄_nonneg u), ← ENNReal.ofReal_one]
  congr 1
  ring

instance : IsMarkovKernel m.kernel := ⟨fun u ↦ ⟨m.kernel_apply_univ u⟩⟩

/-- `m.law μ₀ n` is the distribution of the log ratio on trial `n` from the initial distribution
`μ₀`. -/
noncomputable def law (μ₀ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => μ₀
  | n + 1 => m.kernel ∘ₘ law μ₀ n

instance isProbabilityMeasure_law (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (n : ℕ) :
    IsProbabilityMeasure (m.law μ₀ n) := by
  induction n with
  | zero => exact ‹_›
  | succ n ih => exact inferInstanceAs (IsProbabilityMeasure (m.kernel ∘ₘ m.law μ₀ n))

variable {m}

private theorem integrable_sigmoid_mul {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g μ) (c : ℝ) :
    Integrable (fun u ↦ Real.sigmoid u * c * g u) μ :=
  hg.bdd_mul (c := |c|) (by fun_prop) (.of_forall fun u ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sigmoid_nonneg u)]
    exact mul_le_of_le_one_left (abs_nonneg c) (Real.sigmoid_le_one u))

private theorem integrable_one_sub_sigmoid_mul {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g μ)
    (c : ℝ) : Integrable (fun u ↦ (1 - Real.sigmoid u) * c * g u) μ :=
  hg.bdd_mul (c := |c|) (by fun_prop) (.of_forall fun u ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.2 (Real.sigmoid_le_one u))]
    exact mul_le_of_le_one_left (abs_nonneg c) (by linarith [Real.sigmoid_pos u]))

variable (m)

theorem integral_law_succ (μ₀ : Measure ℝ) (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f)
    (hi : ∀ c, Integrable (fun u ↦ f (u + c)) (m.law μ₀ n)) :
    Integrable f (m.law μ₀ (n + 1)) ∧
      ∫ x, f x ∂m.law μ₀ (n + 1) = ∫ u, ∫ x, f x ∂m.kernel u ∂m.law μ₀ n := by
  have hi' (c : ℝ) : Integrable (fun u ↦ f (u - c)) (m.law μ₀ n) := by
    simpa [sub_eq_add_neg] using hi (-c)
  have hsum (g : ℝ → ℝ) (hg : ∀ c, Integrable (fun u ↦ g (u + c)) (m.law μ₀ n))
      (hg' : ∀ c, Integrable (fun u ↦ g (u - c)) (m.law μ₀ n)) :
      Integrable (fun u ↦ Real.sigmoid u * m.π₁ * g (u + Real.log m.β₁₁) +
        Real.sigmoid u * (1 - m.π₁) * g (u + Real.log m.β₁₂) +
        (1 - Real.sigmoid u) * m.π₂ * g (u - Real.log m.β₂₁) +
        (1 - Real.sigmoid u) * (1 - m.π₂) * g (u - Real.log m.β₂₂)) (m.law μ₀ n) :=
    (((integrable_sigmoid_mul (hg _) _).add (integrable_sigmoid_mul (hg _) _)).add
      (integrable_one_sub_sigmoid_mul (hg' _) _)).add (integrable_one_sub_sigmoid_mul (hg' _) _)
  have hint : Integrable f (m.law μ₀ (n + 1)) := by
    show Integrable f (m.kernel ∘ₘ m.law μ₀ n)
    rw [Measure.integrable_comp_iff hf.aestronglyMeasurable]
    refine ⟨.of_forall fun u ↦ ?_, ?_⟩
    · have hd (c a : ℝ) : Integrable f (ENNReal.ofReal c • Measure.dirac a) :=
        (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
      rw [kernel_apply]
      exact (((hd _ _).add_measure (hd _ _)).add_measure (hd _ _)).add_measure (hd _ _)
    · simp_rw [integral_kernel]
      exact hsum (fun x ↦ ‖f x‖) (fun c ↦ (hi c).norm) (fun c ↦ (hi' c).norm)
  refine ⟨hint, ?_⟩
  show ∫ x, f x ∂(m.kernel ∘ₘ m.law μ₀ n) = _
  rw [Measure.comp_eq_comp_const_apply, ProbabilityTheory.Kernel.integral_comp
    (by rwa [← Measure.comp_eq_comp_const_apply])]
  simp [Kernel.const_apply]

theorem integrable_exp_law {μ₀ : Measure ℝ} (hμ₀ : ∀ t, Integrable (fun u ↦ Real.exp (t * u)) μ₀)
    (n : ℕ) (t : ℝ) : Integrable (fun u ↦ Real.exp (t * u)) (m.law μ₀ n) := by
  induction n generalizing t with
  | zero => exact hμ₀ t
  | succ n ih =>
    refine (m.integral_law_succ μ₀ n (by fun_prop) fun c ↦ ?_).1
    simpa [mul_add, Real.exp_add, mul_comm] using (ih t).mul_const (Real.exp (t * c))

/-- The constant `A(k)` of (9) is `π₁β₁₁ᵏ + (1 − π₁)β₁₂ᵏ`. -/
noncomputable def A (k : ℝ) : ℝ := m.π₁ * m.β₁₁ ^ k + (1 - m.π₁) * m.β₁₂ ^ k

/-- The constant `B(k)` of (9) is `π₂/β₂₁ᵏ + (1 − π₂)/β₂₂ᵏ`. -/
noncomputable def B (k : ℝ) : ℝ := m.π₂ / m.β₂₁ ^ k + (1 - m.π₂) / m.β₂₂ ^ k

-- (8)
theorem integral_exp_kernel (k u : ℝ) : ∫ x, Real.exp (k * x) ∂m.kernel u =
    (m.A k - m.B k) * Real.sigmoid u * Real.exp (k * u) + m.B k * Real.exp (k * u) := by
  have up {β : ℝ} (hβ : 0 < β) : Real.exp (k * (u + Real.log β)) = Real.exp (k * u) * β ^ k := by
    rw [Real.rpow_def_of_pos hβ, ← Real.exp_add]; ring_nf
  have dn {β : ℝ} (hβ : 0 < β) : Real.exp (k * (u - Real.log β)) = Real.exp (k * u) / β ^ k := by
    rw [Real.rpow_def_of_pos hβ, ← Real.exp_sub]; ring_nf
  rw [integral_kernel, up m.β₁₁_pos, up m.β₁₂_pos, dn m.β₂₁_pos, dn m.β₂₂_pos, A, B]
  ring

-- (11)
theorem sigmoid_mul_exp (u : ℝ) : Real.sigmoid u * Real.exp u = Real.exp u - Real.sigmoid u := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

variable {μ₀ : Measure ℝ}

private theorem abs_le_exp_add_exp (u : ℝ) : |u| ≤ Real.exp u + Real.exp (-u) := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]; linarith [Real.add_one_le_exp u, Real.exp_pos (-u)]
  · rw [abs_of_nonpos h]; linarith [Real.add_one_le_exp (-u), Real.exp_pos u]

/-- `m.swap` is the model with the two alternatives exchanged, whose ratio of strengths is `1/v`. -/
def swap : BetaLearner where
  β₁₁ := m.β₂₁
  β₁₂ := m.β₂₂
  β₂₁ := m.β₁₁
  β₂₂ := m.β₁₂
  π₁ := m.π₂
  π₂ := m.π₁
  β₁₁_pos := m.β₂₁_pos
  β₁₂_pos := m.β₂₂_pos
  β₂₁_pos := m.β₁₁_pos
  β₂₂_pos := m.β₁₂_pos
  π₁_nonneg := m.π₂_nonneg
  π₁_le_one := m.π₂_le_one
  π₂_nonneg := m.π₁_nonneg
  π₂_le_one := m.π₁_le_one

theorem swap_A (k : ℝ) : m.swap.A k = m.B (-k) := by
  simp [swap, A, B, Real.rpow_neg m.β₂₁_pos.le, Real.rpow_neg m.β₂₂_pos.le, div_eq_mul_inv]

theorem swap_B (k : ℝ) : m.swap.B k = m.A (-k) := by
  simp [swap, A, B, Real.rpow_neg m.β₁₁_pos.le, Real.rpow_neg m.β₁₂_pos.le, div_eq_mul_inv]

theorem swap_kernel (u : ℝ) : m.swap.kernel u = (m.kernel (-u)).map Neg.neg := by
  simp only [kernel_apply, Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_dirac' measurable_neg,
    Real.sigmoid_neg, swap, neg_add, neg_neg, sub_eq_add_neg]
  abel_nf

theorem law_swap (n : ℕ) : m.swap.law (μ₀.map Neg.neg) n = (m.law μ₀ n).map Neg.neg := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show m.swap.kernel ∘ₘ m.swap.law _ n = (m.kernel ∘ₘ m.law μ₀ n).map Neg.neg
    rw [ih, Measure.map_comp _ _ measurable_neg]
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _),
      Measure.bind_apply hs (Kernel.aemeasurable _),
      lintegral_map (Kernel.measurable_coe _ hs) measurable_neg]
    simp [swap_kernel, Kernel.map_apply _ measurable_neg]

/-- The exponent `σ₁` of (14) solves `β₁₁^σ₁ = 1/β₁₂`, so it counts the occurrences of `E₁₁` that
undo one occurrence of `E₁₂`. -/
noncomputable def σ₁ : ℝ := -Real.log m.β₁₂ / Real.log m.β₁₁

/-- The exponent `σ₂` of (14) solves `β₂₁^σ₂ = 1/β₂₂`. -/
noncomputable def σ₂ : ℝ := -Real.log m.β₂₂ / Real.log m.β₂₁

/-- The drift coefficient of (16) multiplies `E(Pₙ) − P*` in the change of the expected log ratio.
-/
noncomputable def drift : ℝ :=
  Real.log m.β₁₁ * (m.π₁ * (m.σ₁ + 1) - m.σ₁) + Real.log m.β₂₁ * (m.π₂ * (m.σ₂ + 1) - m.σ₂)

/-- The probability `P*` of (15) is the limit of `E(Pₙ)` under the conditions of Theorem 17. -/
noncomputable def Pstar : ℝ :=
  (m.π₂ * (m.σ₂ + 1) - m.σ₂) /
    (Real.log m.β₁₁ / Real.log m.β₂₁ * (m.π₁ * (m.σ₁ + 1) - m.σ₁) + (m.π₂ * (m.σ₂ + 1) - m.σ₂))

theorem integrable_sigmoid_law [IsProbabilityMeasure μ₀] (n : ℕ) :
    Integrable (fun u ↦ Real.sigmoid u) (m.law μ₀ n) :=
  (integrable_const (1 : ℝ)).mono' (by fun_prop) (.of_forall fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sigmoid_nonneg u)]; exact Real.sigmoid_le_one u)

theorem integral_law_swap (f : ℝ → ℝ) (n : ℕ) :
    ∫ x, f x ∂m.swap.law (μ₀.map Neg.neg) n = ∫ u, f (-u) ∂m.law μ₀ n := by
  rw [law_swap]
  exact integral_map_equiv (MeasurableEquiv.neg ℝ) f

theorem integral_sigmoid_law_swap [IsProbabilityMeasure μ₀] (n : ℕ) :
    ∫ x, Real.sigmoid x ∂m.swap.law (μ₀.map Neg.neg) n = 1 - ∫ u, Real.sigmoid u ∂m.law μ₀ n := by
  rw [integral_law_swap]
  simp_rw [Real.sigmoid_neg]
  rw [integral_sub (integrable_const 1) (m.integrable_sigmoid_law n)]
  simp

private theorem A_one_pos : 0 < m.A 1 := by
  simp only [A, Real.rpow_one]
  rcases eq_or_lt_of_le m.π₁_nonneg with h | h
  · rw [← h]; simp [m.β₁₂_pos]
  · nlinarith [mul_pos h m.β₁₁_pos, mul_nonneg (sub_nonneg.2 m.π₁_le_one) m.β₁₂_pos.le]

private theorem B_one_pos : 0 < m.B 1 := by
  simp only [B, Real.rpow_one]
  have := div_nonneg m.π₂_nonneg m.β₂₁_pos.le
  have := div_nonneg (sub_nonneg.2 m.π₂_le_one) m.β₂₂_pos.le
  rcases eq_or_lt_of_le m.π₂_nonneg with h | h
  · rw [← h]; simp [m.β₂₂_pos]
  · linarith [div_pos h m.β₂₁_pos]

variable (hμ₀ : ∀ t, Integrable (fun u ↦ Real.exp (t * u)) μ₀)
include hμ₀

theorem integrable_sigmoid_mul_exp_law (n : ℕ) (t : ℝ) :
    Integrable (fun u ↦ Real.sigmoid u * Real.exp (t * u)) (m.law μ₀ n) := by
  simpa using integrable_sigmoid_mul (m.integrable_exp_law hμ₀ n t) 1

-- (8), (10)
theorem integral_exp_law_succ (k : ℝ) (n : ℕ) :
    ∫ u, Real.exp (k * u) ∂m.law μ₀ (n + 1) =
      (m.A k - m.B k) * ∫ u, Real.sigmoid u * Real.exp (k * u) ∂m.law μ₀ n +
        m.B k * ∫ u, Real.exp (k * u) ∂m.law μ₀ n := by
  rw [(m.integral_law_succ μ₀ n (by fun_prop) fun c ↦ by
      simpa [mul_add, Real.exp_add, mul_comm] using
        (m.integrable_exp_law hμ₀ n k).mul_const (Real.exp (k * c))).2]
  simp_rw [integral_exp_kernel, mul_assoc]
  rw [integral_add ((m.integrable_sigmoid_mul_exp_law hμ₀ n k).const_mul _)
    ((m.integrable_exp_law hμ₀ n k).const_mul _), integral_const_mul, integral_const_mul]

theorem integrable_id_law (n : ℕ) : Integrable (fun u ↦ u) (m.law μ₀ n) := by
  refine Integrable.mono' ((m.integrable_exp_law hμ₀ n 1).add (m.integrable_exp_law hμ₀ n (-1)))
    (by fun_prop) (.of_forall fun u ↦ ?_)
  simpa using abs_le_exp_add_exp u

-- (16)
theorem integral_law_succ_sub [IsProbabilityMeasure μ₀] (h₁ : m.β₁₁ ≠ 1) (h₂ : m.β₂₁ ≠ 1)
    (hd : m.drift ≠ 0) (n : ℕ) :
    ∫ u, u ∂m.law μ₀ (n + 1) - ∫ u, u ∂m.law μ₀ n =
      m.drift * (∫ u, Real.sigmoid u ∂m.law μ₀ n - m.Pstar) := by
  have l₁ := Real.log_ne_zero_of_pos_of_ne_one m.β₁₁_pos h₁
  have l₂ := Real.log_ne_zero_of_pos_of_ne_one m.β₂₁_pos h₂
  set a := m.π₁ * Real.log m.β₁₁ + (1 - m.π₁) * Real.log m.β₁₂
  set b := m.π₂ * Real.log m.β₂₁ + (1 - m.π₂) * Real.log m.β₂₂
  have ha : m.π₁ * (m.σ₁ + 1) - m.σ₁ = a / Real.log m.β₁₁ := by
    simp only [σ₁, a]; field_simp; ring
  have hb : m.π₂ * (m.σ₂ + 1) - m.σ₂ = b / Real.log m.β₂₁ := by
    simp only [σ₂, b]; field_simp; ring
  have hdr : m.drift = a + b := by
    simp only [drift, ha, hb]; field_simp
  have hab : a + b ≠ 0 := hdr ▸ hd
  have hP : m.drift * m.Pstar = b := by
    rw [hdr, Pstar, ha, hb]
    field_simp
  have hk (u : ℝ) : ∫ x, x ∂m.kernel u = u + (a + b) * Real.sigmoid u - b := by
    rw [integral_kernel]; simp only [a, b]; ring
  rw [(m.integral_law_succ μ₀ n (f := fun x ↦ x) measurable_id fun c ↦
      (m.integrable_id_law hμ₀ n).add (integrable_const c)).2]
  simp_rw [hk]
  have i₁ : Integrable (fun u ↦ u + (a + b) * Real.sigmoid u) (m.law μ₀ n) :=
    (m.integrable_id_law hμ₀ n).add ((m.integrable_sigmoid_law n).const_mul _)
  rw [integral_sub i₁ (integrable_const b), integral_add (m.integrable_id_law hμ₀ n)
      ((m.integrable_sigmoid_law n).const_mul _), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [mul_sub, hP, hdr]
  ring

-- (11)
theorem integral_sigmoid_mul_exp_succ (t : ℝ) (n : ℕ) :
    ∫ u, Real.sigmoid u * Real.exp ((t + 1) * u) ∂m.law μ₀ n =
      ∫ u, Real.exp ((t + 1) * u) ∂m.law μ₀ n -
        ∫ u, Real.sigmoid u * Real.exp (t * u) ∂m.law μ₀ n := by
  rw [← integral_sub (m.integrable_exp_law hμ₀ n _) (m.integrable_sigmoid_mul_exp_law hμ₀ n t)]
  congr 1 with u
  have := sigmoid_mul_exp u
  rw [add_mul, one_mul, Real.exp_add]
  linear_combination Real.exp (t * u) * this

-- (10), (11)
theorem integral_exp_law_succ_one (n : ℕ) :
    ∫ u, Real.exp u ∂m.law μ₀ (n + 1) =
      m.A 1 * ∫ u, Real.exp u ∂m.law μ₀ n - (m.A 1 - m.B 1) * ∫ u, Real.sigmoid u ∂m.law μ₀ n := by
  have h := m.integral_exp_law_succ hμ₀ 1 n
  have h' := m.integral_sigmoid_mul_exp_succ hμ₀ 0 n
  simp only [zero_add, one_mul, zero_mul, Real.exp_zero, mul_one] at h h'
  rw [h, h']
  ring

private theorem integrable_exp_map_neg :
    ∀ t, Integrable (fun u ↦ Real.exp (t * u)) (μ₀.map Neg.neg) := fun t ↦ by
  refine (integrable_map_equiv (MeasurableEquiv.neg ℝ) _).2 ?_
  simpa [Function.comp_def] using hμ₀ (-t)

-- (17)
private theorem tendsto_sigmoid_mul_exp {j : ℕ} {L : ℝ}
    (hL : Tendsto (fun n ↦ ∫ u, Real.exp (((j + 1 : ℕ) : ℝ) * u) ∂m.law μ₀ n) atTop (𝓝 L))
    (hAB : m.A (j + 1 : ℕ) ≠ m.B (j + 1 : ℕ)) :
    Tendsto (fun n ↦ ∫ u, Real.sigmoid u * Real.exp (j * u) ∂m.law μ₀ n) atTop
      (𝓝 ((m.A (j + 1 : ℕ) - 1) * L / (m.A (j + 1 : ℕ) - m.B (j + 1 : ℕ)))) := by
  have key (n : ℕ) : ∫ u, Real.sigmoid u * Real.exp (j * u) ∂m.law μ₀ n =
      (m.A (j + 1 : ℕ) * ∫ u, Real.exp (((j + 1 : ℕ) : ℝ) * u) ∂m.law μ₀ n -
        ∫ u, Real.exp (((j + 1 : ℕ) : ℝ) * u) ∂m.law μ₀ (n + 1)) /
        (m.A (j + 1 : ℕ) - m.B (j + 1 : ℕ)) := by
    rw [eq_div_iff (sub_ne_zero.2 hAB), m.integral_exp_law_succ hμ₀,
      Nat.cast_succ, m.integral_sigmoid_mul_exp_succ hμ₀]
    ring
  simp_rw [key]
  refine Tendsto.div_const ?_ _
  convert (hL.const_mul _).sub ((tendsto_add_atTop_iff_nat 1).2 hL) using 2
  ring

-- Theorem 15, (i), p. 114
theorem theorem15 [IsProbabilityMeasure μ₀] {k : ℕ} (hk : 1 ≤ k) {L : ℕ → ℝ}
    (hL : ∀ i ∈ Finset.Icc 1 k,
      Tendsto (fun n ↦ ∫ u, Real.exp (i * u) ∂m.law μ₀ n) atTop (𝓝 (L i)))
    (hAB : ∀ i ∈ Finset.Icc 1 k, m.A i ≠ m.B i) (hA : ∀ i ∈ Finset.Icc 1 k, m.A i ≠ 1) :
    ∃ p, Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 p) ∧
      L k = (m.A k - m.B k) / (m.A k - 1) *
        (∏ i ∈ Finset.Ico 1 k, (1 - m.B i) / (m.A i - 1)) * p := by
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk⟩
  have hp := m.tendsto_sigmoid_mul_exp hμ₀ (j := 0) (hL 1 h1) (hAB 1 h1)
  simp only [Nat.cast_zero, zero_mul, Real.exp_zero, mul_one, zero_add, Nat.cast_one] at hp
  refine ⟨_, hp, ?_⟩
  -- the recursion between consecutive limits
  have step (j : ℕ) (hj : j ∈ Finset.Ico 1 k) :
      (1 - m.B j) * L j = (m.A j - m.B j) * ((m.A (j + 1 : ℕ) - 1) * L (j + 1) /
        (m.A (j + 1 : ℕ) - m.B (j + 1 : ℕ))) := by
    obtain ⟨hj1, hjk⟩ := Finset.mem_Ico.1 hj
    have hjI : j ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨hj1, hjk.le⟩
    have hj1I : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, hjk⟩
    have hM := m.tendsto_sigmoid_mul_exp hμ₀ (hL (j + 1) hj1I) (hAB (j + 1) hj1I)
    have h := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 (hL j hjI))
      (((hM.const_mul (m.A j - m.B j)).add ((hL j hjI).const_mul (m.B j))).congr
        fun n ↦ (m.integral_exp_law_succ hμ₀ j n).symm)
    linear_combination h
  -- induction on the order of the moment
  suffices main : ∀ k', 1 ≤ k' → k' ≤ k → L k' = (m.A k' - m.B k') / (m.A k' - 1) *
      (∏ i ∈ Finset.Ico 1 k', (1 - m.B i) / (m.A i - 1)) *
        ((m.A 1 - 1) * L 1 / (m.A 1 - m.B 1)) from main k hk le_rfl
  have hA' (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ k) : m.A i - 1 ≠ 0 :=
    sub_ne_zero.2 (hA i (Finset.mem_Icc.2 ⟨h1, hi⟩))
  have hAB' (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ k) : m.A i - m.B i ≠ 0 :=
    sub_ne_zero.2 (hAB i (Finset.mem_Icc.2 ⟨h1, hi⟩))
  intro k' hk'
  induction k', hk' using Nat.le_induction with
  | base =>
    intro _
    have := hA' 1 le_rfl hk
    have := hAB' 1 le_rfl hk
    simp only [Finset.Ico_self, Finset.prod_empty, mul_one, Nat.cast_one] at *
    field_simp
  | succ k' hk' ih =>
    intro hk'k
    have := hA' k' hk' (by omega)
    have := hAB' k' hk' (by omega)
    have := hA' (k' + 1) (by omega) hk'k
    have := hAB' (k' + 1) (by omega) hk'k
    have h₁ : m.A 1 - m.B 1 ≠ 0 := by simpa using hAB' 1 le_rfl hk
    have hs := step k' (Finset.mem_Ico.2 ⟨hk', hk'k⟩)
    rw [ih (by omega)] at hs
    rw [Finset.prod_Ico_succ_top hk']
    push_cast at *
    field_simp at hs ⊢
    linear_combination -hs

-- Theorem 15, (ii), p. 114
theorem theorem15_inv [IsProbabilityMeasure μ₀] {k : ℕ} (hk : 1 ≤ k) {L : ℕ → ℝ}
    (hL : ∀ i ∈ Finset.Icc 1 k,
      Tendsto (fun n ↦ ∫ u, Real.exp (-i * u) ∂m.law μ₀ n) atTop (𝓝 (L i)))
    (hBA : ∀ i ∈ Finset.Icc 1 k, m.B (-i) ≠ m.A (-i)) (hB : ∀ i ∈ Finset.Icc 1 k, m.B (-i) ≠ 1) :
    ∃ p, Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 p) ∧
      L k = (m.A (-k) - m.B (-k)) / (1 - m.B (-k)) *
        (∏ i ∈ Finset.Ico 1 k, (m.A (-i) - 1) / (1 - m.B (-i))) * (1 - p) := by
  obtain ⟨p, hp, hLk⟩ := m.swap.theorem15 (integrable_exp_map_neg hμ₀) hk (L := L)
    (fun i hi ↦ by simpa [integral_law_swap] using hL i hi)
    (fun i hi ↦ by simpa [swap_A, swap_B] using hBA i hi)
    (fun i hi ↦ by simpa [swap_A] using hB i hi)
  have e (x y : ℝ) : (x - y) / (x - 1) = (y - x) / (1 - x) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  have e' (x y : ℝ) : (1 - x) / (y - 1) = (x - 1) / (1 - y) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  refine ⟨1 - p, ?_, ?_⟩
  · simp_rw [integral_sigmoid_law_swap] at hp
    simpa using tendsto_const_nhds.sub hp (a := 1)
  · rw [hLk, swap_A, swap_B, e, sub_sub_cancel]
    congr 2
    exact Finset.prod_congr rfl fun i _ ↦ by rw [swap_A, swap_B, e']

-- Theorem 15, p. 115
theorem theorem15_corollary [IsProbabilityMeasure μ₀]
    (h : (∃ L, Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop (𝓝 L)) ∧ m.A 1 ≠ m.B 1 ∨
      (∃ L, Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop (𝓝 L)) ∧
        m.B (-1) ≠ m.A (-1)) :
    ∃ p, Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 p) := by
  rcases h with ⟨⟨L, hL⟩, hAB⟩ | ⟨⟨L, hL⟩, hBA⟩
  · have := m.tendsto_sigmoid_mul_exp hμ₀ (j := 0) (by simpa using hL) (by simpa using hAB)
    exact ⟨_, by simpa using this⟩
  · have := m.swap.tendsto_sigmoid_mul_exp (integrable_exp_map_neg hμ₀) (j := 0)
      (by simpa [integral_law_swap] using hL) (by simpa [swap_A, swap_B] using hBA)
    simp only [Nat.cast_zero, zero_mul, Real.exp_zero, mul_one, integral_sigmoid_law_swap] at this
    exact ⟨_, by simpa using tendsto_const_nhds.sub this (a := 1)⟩

private theorem integral_sigmoid_le [IsProbabilityMeasure μ₀] (n : ℕ) :
    ∫ u, Real.sigmoid u ∂m.law μ₀ n ≤ ∫ u, Real.exp u ∂m.law μ₀ n :=
  integral_mono (m.integrable_sigmoid_law n) (by simpa using m.integrable_exp_law hμ₀ n 1)
    fun u ↦ by nlinarith [sigmoid_mul_exp u, Real.sigmoid_pos u, Real.exp_pos u]

private theorem exp_integral_le [IsProbabilityMeasure μ₀] (n : ℕ) (t : ℝ) :
    Real.exp (t * ∫ u, u ∂m.law μ₀ n) ≤ ∫ u, Real.exp (t * u) ∂m.law μ₀ n := by
  rw [← integral_const_mul]
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (.of_forall fun _ ↦ Set.mem_univ _) ((m.integrable_id_law hμ₀ n).const_mul t)
    (m.integrable_exp_law hμ₀ n t)

private theorem integral_exp_pos [IsProbabilityMeasure μ₀] (n : ℕ) (t : ℝ) :
    0 < ∫ u, Real.exp (t * u) ∂m.law μ₀ n :=
  (Real.exp_pos _).trans_le (m.exp_integral_le hμ₀ n t)

private theorem one_le_integral_exp_mul [IsProbabilityMeasure μ₀] (n : ℕ) :
    1 ≤ (∫ u, Real.exp u ∂m.law μ₀ n) * ∫ u, Real.exp (-u) ∂m.law μ₀ n := by
  have h₁ := m.exp_integral_le hμ₀ n 1
  have h₂ := m.exp_integral_le hμ₀ n (-1)
  simp only [one_mul, neg_one_mul] at h₁ h₂
  calc (1 : ℝ) = Real.exp (∫ u, u ∂m.law μ₀ n) * Real.exp (-∫ u, u ∂m.law μ₀ n) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ _ := mul_le_mul h₁ h₂ (Real.exp_pos _).le ((Real.exp_pos _).le.trans h₁)

-- Theorem 16, (i), p. 115
theorem theorem16 [IsProbabilityMeasure μ₀] {L : ℝ}
    (hL : Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop (𝓝 L)) :
    (L = 0 → Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop atTop) ∧
    (Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 0) → m.A 1 ≠ 1 → L = 0) := by
  refine ⟨fun hL0 ↦ ⟨?_, ?_⟩, fun hq hA ↦ ?_⟩
  · subst hL0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun n ↦ integral_nonneg fun u ↦ (Real.sigmoid_pos u).le) (m.integral_sigmoid_le hμ₀)
  · subst hL0
    have hpos (n : ℕ) : 0 < ∫ u, Real.exp u ∂m.law μ₀ n := by
      simpa using m.integral_exp_pos hμ₀ n 1
    have h := (tendsto_nhdsWithin_iff.2 ⟨hL, .of_forall hpos⟩).inv_tendsto_nhdsGT_zero
    refine tendsto_atTop_mono (fun n ↦ ?_) h
    rw [Pi.inv_apply, inv_le_iff_one_le_mul₀ (hpos n)]
    exact (m.one_le_integral_exp_mul hμ₀ n).trans_eq (mul_comm _ _)
  · have h := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 hL)
      (((hL.const_mul (m.A 1)).sub (hq.const_mul (m.A 1 - m.B 1))).congr
        fun n ↦ (m.integral_exp_law_succ_one hμ₀ n).symm)
    have : (m.A 1 - 1) * L = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hA)

-- Theorem 16, (ii), p. 116
theorem theorem16_inv [IsProbabilityMeasure μ₀] {L : ℝ}
    (hL : Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop (𝓝 L)) :
    (L = 0 → Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 1) ∧
      Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop atTop) ∧
    (Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 1) → m.B (-1) ≠ 1 → L = 0) := by
  have h := m.swap.theorem16 (integrable_exp_map_neg hμ₀) (L := L)
    (by simpa [integral_law_swap] using hL)
  simp only [integral_sigmoid_law_swap] at h
  simp only [integral_law_swap, neg_neg, swap_A] at h
  have e : Tendsto (fun n ↦ 1 - ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 0) ↔
      Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 1) := by
    constructor <;> intro h'
    · simpa using tendsto_const_nhds.sub h' (a := 1)
    · simpa using tendsto_const_nhds.sub h' (a := 1)
  simpa [e] using h

private theorem tendsto_integral_exp_of_cesaro [IsProbabilityMeasure μ₀] {K : ℝ} (hK : 0 < K)
    (t : ℝ)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * (t * ∫ u, u ∂m.law μ₀ n - t * ∫ u, u ∂m.law μ₀ 0))
      atTop (𝓝 K)) :
    Tendsto (fun n ↦ ∫ u, Real.exp (t * u) ∂m.law μ₀ n) atTop atTop := by
  have hl : Tendsto (fun n ↦ t * ∫ u, u ∂m.law μ₀ n) atTop atTop := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hK h
    have h' : Tendsto (fun n ↦ t * ∫ u, u ∂m.law μ₀ n - t * ∫ u, u ∂m.law μ₀ 0) atTop atTop :=
      this.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ by
        have : (n : ℝ) ≠ 0 := by positivity
        field_simp)
    simpa using tendsto_atTop_add_const_right _ (t * ∫ u, u ∂m.law μ₀ 0) h'
  refine tendsto_atTop_mono (fun n ↦ ?_) hl
  rw [← integral_const_mul]
  refine integral_mono ((m.integrable_id_law hμ₀ n).const_mul t) (m.integrable_exp_law hμ₀ n t)
    fun u ↦ ?_
  linarith [Real.add_one_le_exp (t * u)]

-- (16), Theorem 17, p. 116
theorem theorem17 [IsProbabilityMeasure μ₀] (h₁ : m.β₁₁ ≠ 1) (h₂ : m.β₂₁ ≠ 1) (hd : m.drift ≠ 0)
    {p : ℝ} (hp : Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 p)) :
    p = m.Pstar ∨ Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop atTop ∨
      Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop atTop := by
  set l := fun n ↦ ∫ u, u ∂m.law μ₀ n
  have hdiff : Tendsto (fun n ↦ l (n + 1) - l n) atTop (𝓝 (m.drift * (p - m.Pstar))) := by
    simp_rw [l, m.integral_law_succ_sub hμ₀ h₁ h₂ hd]
    exact (hp.sub_const _).const_mul _
  have hc := hdiff.cesaro
  simp_rw [Finset.sum_range_sub (f := l)] at hc
  rcases lt_trichotomy (m.drift * (p - m.Pstar)) 0 with hK | hK | hK
  · refine .inr (.inr ?_)
    simpa using m.tendsto_integral_exp_of_cesaro hμ₀ (neg_pos.2 hK) (-1)
      (hc.neg.congr fun n ↦ by ring)
  · exact .inl (sub_eq_zero.1 ((mul_eq_zero.1 hK).resolve_left hd))
  · refine .inr (.inl ?_)
    simpa using m.tendsto_integral_exp_of_cesaro hμ₀ hK 1 (by simpa using hc)

-- (16), Theorem 17, p. 117
theorem theorem17_corollary [IsProbabilityMeasure μ₀] (h₁ : m.β₁₁ ≠ 1) (h₂ : m.β₂₁ ≠ 1)
    (hd : m.drift ≠ 0) {L L' : ℝ}
    (hL : Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop (𝓝 L))
    (hL' : Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop (𝓝 L'))
    (hAB : m.A 1 ≠ m.B 1 ∨ m.B (-1) ≠ m.A (-1)) :
    Tendsto (fun n ↦ ∫ u, Real.sigmoid u ∂m.law μ₀ n) atTop (𝓝 m.Pstar) := by
  obtain ⟨p, hp⟩ := m.theorem15_corollary hμ₀
    (hAB.imp (fun h ↦ ⟨⟨L, hL⟩, h⟩) fun h ↦ ⟨⟨L', hL'⟩, h⟩)
  rcases m.theorem17 hμ₀ h₁ h₂ hd hp with h | h | h
  · exact h ▸ hp
  · exact absurd h (not_tendsto_atTop_of_tendsto_nhds hL)
  · exact absurd h (not_tendsto_atTop_of_tendsto_nhds hL')

private theorem integral_exp_law_succ_mem (n : ℕ) :
    min (m.A 1) (m.B 1) * ∫ u, Real.exp u ∂m.law μ₀ n ≤ ∫ u, Real.exp u ∂m.law μ₀ (n + 1) ∧
      ∫ u, Real.exp u ∂m.law μ₀ (n + 1) ≤ max (m.A 1) (m.B 1) * ∫ u, Real.exp u ∂m.law μ₀ n := by
  have h := m.integral_exp_law_succ hμ₀ 1 n
  simp only [one_mul] at h
  have hP : 0 ≤ ∫ u, Real.sigmoid u * Real.exp u ∂m.law μ₀ n :=
    integral_nonneg fun u ↦ (mul_pos (Real.sigmoid_pos u) (Real.exp_pos u)).le
  have hP' : ∫ u, Real.sigmoid u * Real.exp u ∂m.law μ₀ n ≤ ∫ u, Real.exp u ∂m.law μ₀ n :=
    integral_mono (by simpa using m.integrable_sigmoid_mul_exp_law hμ₀ n 1)
      (by simpa using m.integrable_exp_law hμ₀ n 1) fun u ↦
        mul_le_of_le_one_left (Real.exp_pos u).le (Real.sigmoid_le_one u)
  rw [h]
  constructor <;> nlinarith [min_le_left (m.A 1) (m.B 1), min_le_right (m.A 1) (m.B 1),
    le_max_left (m.A 1) (m.B 1), le_max_right (m.A 1) (m.B 1)]

-- Theorem 18, (i), p. 117
theorem theorem18 [IsProbabilityMeasure μ₀] :
    (1 < m.A 1 → 1 < m.B 1 → Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop atTop) ∧
    (m.A 1 < 1 → m.B 1 < 1 → Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop (𝓝 0)) ∧
    (Tendsto (fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n) atTop atTop → 1 ≤ m.A 1) := by
  set e := fun n ↦ ∫ u, Real.exp u ∂m.law μ₀ n
  have he (n : ℕ) : 0 < e n := by simpa using m.integral_exp_pos hμ₀ n 1
  have hmin : 0 ≤ min (m.A 1) (m.B 1) := le_min m.A_one_pos.le m.B_one_pos.le
  have lower (n : ℕ) : min (m.A 1) (m.B 1) ^ n * e 0 ≤ e n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_comm _ (min _ _), mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih hmin).trans (m.integral_exp_law_succ_mem hμ₀ n).1
  have upper (n : ℕ) : e n ≤ max (m.A 1) (m.B 1) ^ n * e 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_comm _ (max _ _), mul_assoc]
      exact (m.integral_exp_law_succ_mem hμ₀ n).2.trans
        (mul_le_mul_of_nonneg_left ih (hmin.trans (min_le_max)))
  refine ⟨fun hA hB ↦ ?_, fun hA hB ↦ ?_, fun hL ↦ ?_⟩
  · exact tendsto_atTop_mono lower
      ((tendsto_pow_atTop_atTop_of_one_lt (lt_min hA hB)).atTop_mul_const (he 0))
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (hmin.trans min_le_max) (max_lt hA hB)).mul_const
      (e 0)
    rw [zero_mul] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun n ↦ (he n).le) upper
  · by_contra! hA
    set M := |m.A 1 - m.B 1| / (1 - m.A 1)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hL.eventually_gt_atTop M)
    have hdec (n : ℕ) (hn : N ≤ n) : e (n + 1) < e n := by
      have h := m.integral_exp_law_succ_one hμ₀ n
      have hq0 : 0 ≤ ∫ u, Real.sigmoid u ∂m.law μ₀ n :=
        integral_nonneg fun u ↦ (Real.sigmoid_pos u).le
      have hq1 : ∫ u, Real.sigmoid u ∂m.law μ₀ n ≤ 1 := by
        calc _ ≤ ∫ _, (1 : ℝ) ∂m.law μ₀ n :=
              integral_mono (m.integrable_sigmoid_law n) (integrable_const 1)
                fun u ↦ Real.sigmoid_le_one u
          _ = 1 := by simp
      have hM : M < e n := hN n hn
      rw [div_lt_iff₀ (by linarith)] at hM
      show ∫ u, Real.exp u ∂m.law μ₀ (n + 1) < e n
      rw [h]
      cases abs_cases (m.A 1 - m.B 1) <;> nlinarith
    have hle (n : ℕ) (hn : N ≤ n) : e n ≤ e N := by
      induction n, hn using Nat.le_induction with
      | base => exact le_rfl
      | succ n hn ih => exact (hdec n hn).le.trans ih
    obtain ⟨n, hn, hnN⟩ := ((hL.eventually_gt_atTop (e N)).and (eventually_ge_atTop N)).exists
    linarith [hle n hnN]

-- Theorem 18, (ii), p. 117
theorem theorem18_inv [IsProbabilityMeasure μ₀] :
    (1 < m.A (-1) → 1 < m.B (-1) →
      Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop atTop) ∧
    (m.A (-1) < 1 → m.B (-1) < 1 →
      Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop (𝓝 0)) ∧
    (Tendsto (fun n ↦ ∫ u, Real.exp (-u) ∂m.law μ₀ n) atTop atTop → 1 ≤ m.B (-1)) := by
  have h := m.swap.theorem18 (integrable_exp_map_neg hμ₀) (μ₀ := μ₀.map Neg.neg)
  simp only [integral_law_swap, swap_A, swap_B] at h
  exact ⟨fun hA hB ↦ h.1 hB hA, fun hA hB ↦ h.2.1 hB hA, h.2.2⟩

end BetaLearner

-- Lemma 12, p. 119
theorem lemma12 {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    Real.log x / (x - 1) < y / (y - 1) * Real.log y := by
  have h₁ := Real.log_lt_sub_one_of_pos (by linarith) (ne_of_gt hx)
  have h₂ := Real.log_lt_sub_one_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < y))
    (inv_ne_one.2 (ne_of_gt hy))
  rw [Real.log_inv] at h₂
  have h₃ : y - 1 < y * Real.log y := by
    have := mul_lt_mul_of_pos_left h₂ (show (0 : ℝ) < y by linarith)
    rw [mul_sub, mul_inv_cancel₀ (by linarith), mul_one, mul_neg] at this
    linarith
  calc Real.log x / (x - 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    _ < y / (y - 1) * Real.log y := by
      rw [div_mul_eq_mul_div, one_lt_div (by linarith)]; exact h₃

-- (0, 1), (14), Theorem 19, p. 119
theorem theorem19 {x y : ℝ} (hx : 1 < x) (hy₀ : 0 < y) (hy : y < 1) :
    (1 - y) / (x - y) < -Real.log y / Real.log x / (-Real.log y / Real.log x + 1) ∧
      -Real.log y / Real.log x / (-Real.log y / Real.log x + 1) < x * (1 - y) / (x - y) := by
  have ha := Real.log_pos hx
  have hb := neg_pos.2 (Real.log_neg hy₀ hy)
  have hy' : 1 < y⁻¹ := (one_lt_inv₀ hy₀).2 hy
  have hσ : -Real.log y / Real.log x / (-Real.log y / Real.log x + 1) =
      -Real.log y / (Real.log x + -Real.log y) := by
    field_simp
    ring
  have U := lemma12 hy' hx
  have L := lemma12 hx hy'
  rw [Real.log_inv] at U L
  have e₁ : -Real.log y / (y⁻¹ - 1) = -Real.log y * y / (1 - y) := by
    field_simp
  have e₂ : y⁻¹ / (y⁻¹ - 1) * -Real.log y = -Real.log y / (1 - y) := by
    field_simp
  rw [e₁, div_mul_eq_mul_div, div_lt_div_iff₀ (by linarith) (by linarith)] at U
  rw [e₂, div_lt_div_iff₀ (by linarith) (by linarith)] at L
  rw [hσ, div_lt_div_iff₀ (by linarith) (by linarith), div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> nlinarith

end BetaAsymptotics

end Luce1959
