module

public import Linglib.Data.Examples.WaldonEtAl2023
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Waldon et al. (2023): On the Context Dependence of Artifact Noun Interpretation

Waldon, Condoravdi, Levin and Degen ask how a policy goal shapes the boundary of an artifact
noun category, as in *no electronic devices are allowed in the theater* read with the goal of
limiting light or of limiting noise. Following Sassoon and Fadlon, an artifact noun denotes an
additive, weighted measure over several dimensions. The paper makes the weights contextual: an
explicit goal weights the category measure by `γ` and the goal-relevant feature by `1 − γ`, and
with no goal stated the goal weight is split by the goals' plausibility. With a uniform
threshold and an even prior, the posterior that an object is prohibited is the measure itself.
The Goal Insensitive hypothesis is `γ = 1`; the experiment's Bayesian analysis estimates `γ` at
about 0.76, with 1 outside the credible interval.

## Main statements

* `prohibitionPosterior_eq`: the posterior that an object is prohibited is its measure.
* `not_threshold_shift`: one goal raising an object and lowering another is not a shift of the
  standard of comparison.

## Implementation notes

Objects and goals are types, and the category, feature and plausibility measures of the
norming studies are the fields of `Norming`, bounded as the slider scales are, in place of
values retyped from the paper; every prediction is stated over them and over `γ`. The
posterior is the Bayes ratio with the threshold marginalized by Lebesgue measure on `[0, m]`.
The paper's examples are the rows of `Data.Examples.WaldonEtAl2023`.

## References

* [waldon-etal-2023]
* [sassoon-fadlon-2017]
* [kennedy-2007]
* [lassiter-goodman-2017]
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace WaldonEtAl2023

variable {O G : Type*} [Fintype G]

/-! ### The norming data and the contextual measure -/

/-- The norming studies (§3.1) supply the category-membership measure `cat` and the
goal-relevant feature measures, on the unit interval, and the plausibility of the goals, a
distribution. -/
structure Norming (O G : Type*) [Fintype G] where
  cat : O → ℝ
  feature : G → O → ℝ
  plausibility : G → ℝ
  cat_mem : ∀ o, cat o ∈ Set.Icc 0 1
  feature_mem : ∀ g o, feature g o ∈ Set.Icc 0 1
  plausibility_nonneg : ∀ g, 0 ≤ plausibility g
  plausibility_sum : ∑ g, plausibility g = 1

/-- An experimental condition states no goal or an explicit policy goal. -/
inductive Condition (G : Type*)
  | neutral
  | explicit (g : G)

variable (N : Norming O G) (γ : ℝ)

/-- The goal-weighted measure of the artifact noun, (13) under an explicit goal and (14) with
the goal weight split by plausibility, is a weighted sum of the category and the goal
dimensions. -/
noncomputable def measure : Condition G → O → ℝ
  | .explicit g => fun o ↦ γ * N.cat o + (1 - γ) * N.feature g o
  | .neutral => fun o ↦ γ * N.cat o + (1 - γ) * ∑ g, N.plausibility g * N.feature g o

theorem measure_explicit (g : G) (o : O) :
    measure N γ (.explicit g) o = γ * N.cat o + (1 - γ) * N.feature g o := rfl

theorem mix_mem_Icc (o : O) : ∑ g, N.plausibility g * N.feature g o ∈ Set.Icc 0 1 :=
  ⟨Finset.sum_nonneg fun g _ ↦ mul_nonneg (N.plausibility_nonneg g) (N.feature_mem g o).1,
    (Finset.sum_le_sum fun g _ ↦ mul_le_of_le_one_right (N.plausibility_nonneg g)
      (N.feature_mem g o).2).trans_eq N.plausibility_sum⟩

theorem measure_mem_Icc (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (c : Condition G) (o : O) :
    measure N γ c o ∈ Set.Icc 0 1 := by
  have hc := N.cat_mem o
  rcases c with _ | g
  · have hm := mix_mem_Icc N o
    simp only [measure, Set.mem_Icc] at *
    constructor <;> nlinarith
  · have hf := N.feature_mem g o
    rw [measure_explicit]
    simp only [Set.mem_Icc] at *
    constructor <;> nlinarith

/-! ### The interpretive model (12) -/

/-- The probability that a measure meets a standard uniform on the unit interval is the Lebesgue
mass of `[0, m]`. -/
noncomputable def meetsProb (m : ℝ) : ℝ≥0∞ := volume (Set.Icc (0 : ℝ) m)

theorem meetsProb_eq (m : ℝ) : meetsProb m = ENNReal.ofReal m := by
  rw [meetsProb, Real.volume_Icc, sub_zero]

/-- The posterior that an object of measure `m` is prohibited is the Bayes ratio of (12) with an
even prior and the threshold marginalized. -/
noncomputable def prohibitionPosterior (m : ℝ) : ℝ≥0∞ :=
  2⁻¹ * meetsProb m / (2⁻¹ * meetsProb m + 2⁻¹ * (1 - meetsProb m))

/-- The posterior is the measure. -/
theorem prohibitionPosterior_eq {m : ℝ} (hm1 : m ≤ 1) :
    prohibitionPosterior m = ENNReal.ofReal m := by
  have h1 : meetsProb m ≤ 1 := by
    rw [meetsProb_eq, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hm1
  rw [prohibitionPosterior, ← mul_add, add_tsub_cancel_of_le h1, mul_one, meetsProb_eq,
    ENNReal.mul_div_right_comm, ENNReal.div_self (by norm_num) (by norm_num), one_mul]

theorem prohibitionPosterior_lt_iff {m m' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm1' : m' ≤ 1) :
    prohibitionPosterior m < prohibitionPosterior m' ↔ m < m' := by
  rw [prohibitionPosterior_eq hm1, prohibitionPosterior_eq hm1',
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hm0]

/-! ### Goal sensitivity (§4.3) -/

theorem measure_one (c c' : Condition G) (o : O) : measure N 1 c o = measure N 1 c' o := by
  rcases c with _ | g <;> rcases c' with _ | g' <;> simp [measure]

theorem measure_explicit_lt (hγ : γ < 1) {g g' : G} {o : O}
    (h : N.feature g o < N.feature g' o) :
    measure N γ (.explicit g) o < measure N γ (.explicit g') o := by
  rw [measure_explicit, measure_explicit]
  nlinarith

theorem measure_explicit_sub_neutral (g : G) (o : O) :
    measure N γ (.explicit g) o - measure N γ .neutral o =
      (1 - γ) * (N.feature g o - ∑ g', N.plausibility g' * N.feature g' o) := by
  rw [measure_explicit]
  simp only [measure]
  ring

theorem measure_bidirectional (hγ : γ < 1) {g : G} {o o' : O}
    (ho : ∑ g', N.plausibility g' * N.feature g' o < N.feature g o)
    (ho' : N.feature g o' < ∑ g', N.plausibility g' * N.feature g' o') :
    measure N γ .neutral o < measure N γ (.explicit g) o ∧
      measure N γ (.explicit g) o' < measure N γ .neutral o' := by
  constructor
  · have := measure_explicit_sub_neutral N γ g o
    nlinarith
  · have := measure_explicit_sub_neutral N γ g o'
    nlinarith

/-- No single shift of the standard of comparison is bidirectional. With one measure and two
thresholds, an object included under the second but not the first and another included under
the first but not the second cannot both exist. -/
theorem not_threshold_shift (m : O → ℝ) (θ θ' : ℝ) (o o' : O) :
    ¬ ((m o < θ ∧ θ' ≤ m o) ∧ (θ ≤ m o' ∧ m o' < θ')) :=
  fun ⟨⟨h1, h2⟩, h3, h4⟩ ↦ by linarith

end WaldonEtAl2023
