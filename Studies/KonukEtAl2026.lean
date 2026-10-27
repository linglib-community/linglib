module

public import Linglib.Semantics.Causation.CausalStrength
public import Linglib.Semantics.Homogeneity.Plural
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Konuk, Quillien and Mascarenhas (2026): Plural Causes

Konuk, Quillien and Mascarenhas extend the Necessity–Sufficiency Model of Icard, Kominsky and
Knobe from single causes to plural ones, conjunctions of events judged as causes in their own
right. Counterfactual worlds are sampled urn by urn, each urn keeping its actual draw with
probability `s`, the stability, and otherwise redrawn from its prior; a cause's score weights its
sufficiency by its probability and its necessity by the probability of its absence, the
substrate's `CausalStrength.score` over plural causes.

Experiment 1 is a game won with two colored balls out of three urns, Experiment 2 one won with
(A ∧ B) ∨ (C ∧ D). Losses in Experiment 2 are scored against the classical negation of the rule or
its homogeneous negation, after the homogeneity of plural predication described by Križ and
Spector, on which each winning condition's plural predication is false.

## Implementation notes

* Necessity holds the urns outside the plural at their actual draws, as in the worked example of
  p. 448, and the score weights by the plural's sampling probability, its prior at `s = 0`.
* `homogeneousLoss` negates each winning condition over its urns that are white in the actual
  round, which gives both of the paper's homogeneous losses, (2) and that of p. 468.
* Two of the paper's claims about the NSM fail in the model: `intermediate_high_ranked_highest`
  needs `0 < s`, and `partners_scored_alike` contradicts the abnormal deflation of p. 463.

## TODO

* The Counterfactual Effect Size Model of Quillien and Lucas, which p. 451 says ranks the
  intermediate and high pair highest at every stability.
* The `w`-weighted mixture of the two losses, a coin drawn in each counterfactual world
  (p. 465).

## References

* [konuk-et-al-2026]
* [icard-et-al-2017]
* [quillien-lucas-2024]
* [kriz-spector-2021]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal

namespace KonukEtAl2026

open CausalStrength

/-! ### Counterfactual sampling -/

section Sampling

/-- The propensity of an urn keeps its actual draw `x` with probability `s`, the stability, and
otherwise redraws it from the prior `p`. -/
noncomputable def propensity (s p : I) (x : Bool) : Measure Bool :=
  toNNReal s • Measure.dirac x + toNNReal (σ s) • Ber(true, false, p)

instance (s p : I) (x : Bool) : IsProbabilityMeasure (propensity s p x) :=
  ⟨by simp [propensity, ← ENNReal.coe_add]⟩

theorem propensity_real_singleton (s p : I) (x y : Bool) :
    (propensity s p x).real {y} =
      s * (if x = y then 1 else 0) + (1 - s) * (if y then (p : ℝ) else 1 - p) := by
  rw [measureReal_def, propensity, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  cases x <;> cases y <;>
    simp [ENNReal.smul_def, ← ENNReal.coe_mul, ← ENNReal.coe_add, coe_symm_eq]

theorem propensity_singleton_ne_zero {s p : I} (hs : s < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (x y : Bool) : propensity s p x {y} ≠ 0 := by
  have hs' : (s : ℝ) < 1 := hs
  have hp₀' : (0 : ℝ) < p := hp₀
  have hp₁' : (p : ℝ) < 1 := hp₁
  have := s.2.1
  have h : 0 < (propensity s p x).real {y} := by
    rw [propensity_real_singleton]
    cases x <;> cases y <;> simp <;> nlinarith
  exact (ENNReal.toReal_pos_iff.1 h).1.ne'

variable {ι : Type*} [Fintype ι]

/-- The counterfactual distribution samples the urns independently, each by its propensity. -/
noncomputable def sampling (s : I) (p : ι → I) (w₀ : ι → Bool) : Measure (ι → Bool) :=
  Measure.pi fun i ↦ propensity s (p i) (w₀ i)

instance (s : I) (p : ι → I) (w₀ : ι → Bool) : IsProbabilityMeasure (sampling s p w₀) := by
  unfold sampling; infer_instance

/-- The actual causal strength of the plural `S` for the outcome `E` in the round `w₀` is its score
with the counterfactuals sampled at stability `s` from the priors `p`. -/
noncomputable def causalStrength [DecidableEq ι] (s : I) (p : ι → I) (w₀ : ι → Bool)
    (E : Set (ι → Bool)) (S : Finset ι) : ℝ≥0∞ :=
  score (sampling s p w₀) w₀ E S

variable {s : I} {p : ι → I} {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)]
  {w₀ v : ι → Bool} {S T : Finset ι} {E : Set (ι → Bool)}

theorem causalStrength_ne_top [DecidableEq ι] : causalStrength s p w₀ E S ≠ ∞ := score_ne_top

theorem sampling_ne_zero (hs : s < 1) (hp₀ : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1)
    {A : Set (ι → Bool)} (hA : A.Nonempty) : sampling s p w₀ A ≠ 0 := by
  obtain ⟨w, hw⟩ := hA
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (singleton_subset_iff.2 hw)))
  rw [sampling, Measure.pi_singleton]
  exact CanonicallyOrderedAdd.prod_pos.2 fun i _ ↦
    pos_iff_ne_zero.2 (propensity_singleton_ne_zero hs (hp₀ i) (hp₁ i) _ _)

variable [DecidableEq ι]

theorem sampling_cause_lt_one (hs : s < 1) (hp₀ : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1)
    (hS : S.Nonempty) : sampling s p w₀ (cause v S) < 1 := by
  obtain ⟨i, hi⟩ := hS
  have := sampling_ne_zero (w₀ := w₀) hs hp₀ hp₁ (A := (cause v S)ᶜ)
    ⟨Function.update v i (!v i), fun h ↦ by simpa using mem_cause.1 h i hi⟩
  rw [prob_compl_eq_one_sub .of_discrete] at this
  exact lt_of_le_of_ne prob_le_one fun h ↦ this (by rw [h, tsub_self])

theorem sampling_compl_cause_ne_zero (hs : s < 1) (hp₀ : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1)
    (hS : S.Nonempty) : sampling s p w₀ (cause v S)ᶜ ≠ 0 := by
  rw [prob_compl_eq_one_sub .of_discrete]
  exact (tsub_pos_of_lt (sampling_cause_lt_one hs hp₀ hp₁ hS)).ne'

theorem causalStrength_cause_lt_of_ssubset (hs : s < 1) (hp₀ : ∀ i, 0 < p i)
    (hp₁ : ∀ i, p i < 1) {S' : Finset ι} (hS : S.Nonempty) (h : S ⊂ S') (hS' : S' ⊆ T) :
    causalStrength s p w₀ (cause w₀ T) S < causalStrength s p w₀ (cause w₀ T) S' := by
  have hc {U : Finset ι} (hU : U.Nonempty) : sampling s p w₀ (cause w₀ U)ᶜ ≠ 0 :=
    sampling_compl_cause_ne_zero hs hp₀ hp₁ hU
  have hpos : sampling s p w₀ (cause w₀ S) ≠ 0 :=
    sampling_ne_zero hs hp₀ hp₁ ⟨w₀, mem_cause.2 fun _ _ ↦ rfl⟩
  have hlt := sampling_cause_lt_one (w₀ := w₀) (v := w₀) hs hp₀ hp₁
    (Finset.sdiff_nonempty.2 h.not_subset)
  unfold causalStrength sampling at *
  rw [score_pi_cause_lt_iff (h.subset.trans hS') hS' (hc hS) (hc (hS.mono h.subset)),
    ← cause_inter_cause_sdiff h.subset, measure_pi_inter_of_dependsOn dependsOn_cause
      dependsOn_cause Finset.disjoint_sdiff]
  simpa using (ENNReal.mul_lt_mul_iff_right hpos (measure_ne_top _ _)).2 hlt

end Sampling

/-! ### The running example and Experiment 1: threshold games -/

section Threshold

variable {ι : Type*} [DecidableEq ι] {X Y : ι}

section

variable [Fintype ι]

/-- The outcome of a threshold game occurs when two causes or more are present,
`A + B + C ≥ 2` (p. 450). -/
def twoOrMore : Set (ι → Bool) := {w | 2 ≤ (Finset.univ.filter fun i ↦ w i = true).card}

theorem piecewise_mem_twoOrMore_iff (h3 : Fintype.card ι = 3) (hXY : X ≠ Y) (w : ι → Bool) :
    ({X, Y} : Finset ι).piecewise w (fun _ ↦ true) ∈ twoOrMore ↔ w X = true ∨ w Y = true := by
  have hsplit : (Finset.univ.filter fun i ↦
      ({X, Y} : Finset ι).piecewise w (fun _ ↦ true) i = true) =
      ({X, Y} : Finset ι).filter (fun i ↦ w i = true) ∪ (Finset.univ \ {X, Y}) := by
    ext i
    by_cases hi : i ∈ ({X, Y} : Finset ι) <;>
      simp [hi, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]
  have hcard : (Finset.univ \ ({X, Y} : Finset ι)).card = 1 := by
    rw [Finset.card_univ_sdiff, h3, Finset.card_pair hXY]
  have hdisj : Disjoint (({X, Y} : Finset ι).filter fun i ↦ w i = true) (Finset.univ \ {X, Y}) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) Finset.disjoint_sdiff
  rw [twoOrMore, mem_ofPred_eq, hsplit, Finset.card_union_of_disjoint hdisj, hcard,
    Finset.filter_insert, Finset.filter_singleton]
  cases w X <;> cases w Y <;> simp [hXY]

end

theorem setOf_eq_eq_cause_union : {w : ι → Bool | w X = w Y} =
    cause (fun _ ↦ true) {X, Y} ∪ cause (fun _ ↦ false) {X, Y} := by
  ext w
  simp only [mem_ofPred_eq, mem_union, mem_cause, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  cases w X <;> cases w Y <;> simp

variable [Fintype ι] {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)]

/-- In a two-of-three threshold game won with all three causes, a pair scores the probability that
its two causes agree, since it is fully sufficient and is necessary where both its causes are
absent. -/
theorem score_twoOrMore_pair (h3 : Fintype.card ι = 3) (hXY : X ≠ Y)
    (hc : Measure.pi ν ((cause (fun _ ↦ true) {X, Y})ᶜ ∩ twoOrMoreᶜ) ≠ 0) :
    score (Measure.pi ν) (fun _ ↦ true) twoOrMore {X, Y} = Measure.pi ν {w | w X = w Y} := by
  have hforce (w : ι → Bool) : ({X, Y} : Finset ι).piecewise (fun _ ↦ true) w ∈ twoOrMore :=
    le_trans (Finset.card_pair hXY).ge (Finset.card_le_card fun i hi ↦ by
      simp [Finset.piecewise_eq_of_mem _ _ _ hi])
  have hnec : (cause (fun _ ↦ true) {X, Y})ᶜ ∩
      {w | ({X, Y} : Finset ι).piecewise w (fun _ ↦ true) ∉ twoOrMore} =
      cause (fun _ ↦ false) {X, Y} := by
    ext w
    simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, piecewise_mem_twoOrMore_iff h3 hXY,
      mem_cause, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    cases w X <;> cases w Y <;> simp
  have hdisj : Disjoint (cause (fun _ ↦ true) {X, Y}) (cause (fun _ ↦ false) {X, Y}) :=
    Set.disjoint_left.2 fun _ h₁ h₂ ↦ by
      simpa using (mem_cause.1 h₁ X (by simp)).symm.trans (mem_cause.1 h₂ X (by simp))
  rw [score, sufficiency_eq_one hforce hc, mul_one, mul_necessity, hnec, setOf_eq_eq_cause_union,
    measure_union hdisj .of_discrete]

theorem causalStrength_twoOrMore_pair_toReal (h3 : Fintype.card ι = 3) (hXY : X ≠ Y) {s : I}
    (hs : s < 1) {p : ι → I} (hp₀ : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) :
    (causalStrength s p (fun _ ↦ true) twoOrMore {X, Y}).toReal =
      (s + (1 - s) * p X) * (s + (1 - s) * p Y) +
        (1 - s) * (1 - p X) * ((1 - s) * (1 - p Y)) := by
  have hc := sampling_ne_zero (w₀ := fun _ ↦ true) hs hp₀ hp₁
    (A := (cause (fun _ ↦ true) {X, Y})ᶜ ∩ twoOrMoreᶜ) ⟨fun _ ↦ false,
      fun h ↦ by simpa using mem_cause.1 h X (by simp), by simp [twoOrMore]⟩
  unfold causalStrength sampling at *
  rw [score_twoOrMore_pair h3 hXY hc, ← measureReal_def, setOf_eq_eq_cause_union,
    measureReal_union (Set.disjoint_left.2 fun _ h₁ h₂ ↦ by
      simpa using (mem_cause.1 h₁ X (by simp)).symm.trans (mem_cause.1 h₂ X (by simp)))
      .of_discrete, measureReal_pi_cause, measureReal_pi_cause, Finset.prod_pair hXY,
    Finset.prod_pair hXY]
  simp [propensity_real_singleton]

end Threshold

/-- `Dish` lists the dishes of the running example of p. 448. -/
inductive Dish | cheese | cake | pie
  deriving DecidableEq, Fintype

/-- `dishPrior` gives the probability of eating each dish (p. 448). -/
noncomputable def dishPrior : Dish → I
  | .cheese => ⟨1 / 2, by norm_num, by norm_num⟩
  | .cake => ⟨4 / 5, by norm_num, by norm_num⟩
  | .pie => ⟨1 / 10, by norm_num, by norm_num⟩

/-- In the paper's running example, at `s = 0`, eating the cake and the pie scores
0.08 · 1 + 0.92 · 0.18/0.92 = 0.26 for a stomachache from two desserts or more (p. 448). -/
example : (causalStrength 0 dishPrior (fun _ ↦ true) twoOrMore {.cake, .pie}).toReal = 13 / 50 := by
  rw [causalStrength_twoOrMore_pair_toReal rfl (by decide) zero_lt_one
    (fun i ↦ Subtype.coe_lt_coe.1 (by cases i <;> norm_num [dishPrior]))
    (fun i ↦ Subtype.coe_lt_coe.1 (by cases i <;> norm_num [dishPrior]))]
  norm_num [dishPrior]

/-- `Urn₁` names the urns of Experiment 1 by their probability of a colored ball. -/
inductive Urn₁ | low | intermediate | high
  deriving DecidableEq, Fintype

open Urn₁

/-- `prior₁` gives each urn's probability of a colored ball in Experiment 1. -/
noncomputable def prior₁ : Urn₁ → I
  | low => ⟨1 / 20, by norm_num, by norm_num⟩
  | intermediate => ⟨1 / 2, by norm_num, by norm_num⟩
  | high => ⟨19 / 20, by norm_num, by norm_num⟩

section Experiment1

variable {s : I}

private theorem causalStrength_pair₁_toReal (hs : s < 1) {X Y : Urn₁} (hXY : X ≠ Y) :
    (causalStrength s prior₁ (fun _ ↦ true) twoOrMore {X, Y}).toReal =
      (s + (1 - s) * prior₁ X) * (s + (1 - s) * prior₁ Y) +
        (1 - s) * (1 - prior₁ X) * ((1 - s) * (1 - prior₁ Y)) :=
  causalStrength_twoOrMore_pair_toReal rfl hXY hs
    (fun i ↦ Subtype.coe_lt_coe.1 (by cases i <;> norm_num [prior₁]))
    (fun i ↦ Subtype.coe_lt_coe.1 (by cases i <;> norm_num [prior₁]))

/-- The NSM rates the intermediate and high pair highest, beating the low and intermediate pair by
`9/10 · s(1 - s)` exactly when `0 < s` (p. 451). -/
theorem intermediate_high_ranked_highest (hs : s < 1) :
    (causalStrength s prior₁ (fun _ ↦ true) twoOrMore {low, intermediate} <
        causalStrength s prior₁ (fun _ ↦ true) twoOrMore {intermediate, high} ↔ 0 < s) ∧
      causalStrength s prior₁ (fun _ ↦ true) twoOrMore {low, high} <
        causalStrength s prior₁ (fun _ ↦ true) twoOrMore {intermediate, high} := by
  simp only [← ENNReal.toReal_lt_toReal causalStrength_ne_top causalStrength_ne_top]
  rw [causalStrength_pair₁_toReal hs (by decide), causalStrength_pair₁_toReal hs (by decide),
    causalStrength_pair₁_toReal hs (by decide), ← Subtype.coe_lt_coe (x := (0 : I))]
  have h₁ : (s : ℝ) < 1 := hs
  have h₀ : (0 : ℝ) ≤ s := s.2.1
  simp only [prior₁, Set.Icc.coe_zero]
  exact ⟨⟨fun h ↦ by nlinarith [mul_nonneg h₀ (sub_pos.2 h₁).le],
    fun h ↦ by nlinarith [mul_pos h (sub_pos.2 h₁)]⟩, by nlinarith⟩

/-- At the stability `s = 0` of the paper's exposition, the low and intermediate pair and the
intermediate and high pair both score one half. -/
example : (causalStrength 0 prior₁ (fun _ ↦ true) twoOrMore {low, intermediate}).toReal = 1 / 2 ∧
    (causalStrength 0 prior₁ (fun _ ↦ true) twoOrMore {intermediate, high}).toReal = 1 / 2 := by
  rw [causalStrength_pair₁_toReal zero_lt_one (by decide),
    causalStrength_pair₁_toReal zero_lt_one (by decide)]
  norm_num [prior₁]

/-- The NSM rates the low and high pair above the low and intermediate pair only for stabilities
above `9/19` (p. 453). -/
theorem low_high_outscores_low_intermediate_iff (hs : s < 1) :
    causalStrength s prior₁ (fun _ ↦ true) twoOrMore {low, intermediate} <
        causalStrength s prior₁ (fun _ ↦ true) twoOrMore {low, high} ↔ 9 / 19 < (s : ℝ) := by
  rw [← ENNReal.toReal_lt_toReal causalStrength_ne_top causalStrength_ne_top,
    causalStrength_pair₁_toReal hs (by decide), causalStrength_pair₁_toReal hs (by decide)]
  have : (0 : ℝ) < 1 - s := sub_pos.2 hs
  simp only [prior₁]
  constructor <;> intro h <;> nlinarith

end Experiment1

/-! ### Wins and losses under a disjunctive rule -/

section Rule

variable {ι : Type*} (rule : Finset (Finset ι))

/-- A rule lists sufficient conditions for a win, each a set of urns; the player wins when every
urn of some condition gives a colored ball. -/
def win : Set (ι → Bool) := {w | ∃ D ∈ rule, ∀ i ∈ D, w i = true}

/-- The homogeneous loss in the losing round `w₀` negates each winning condition as a plural over
its urns that are white in `w₀`, so that none of them gives a colored ball. -/
def homogeneousLoss (w₀ : ι → Bool) : Set (ι → Bool) :=
  {w | ∀ D ∈ rule, ∀ i ∈ D, w₀ i = false → w i = false}

instance [DecidableEq ι] : DecidablePred (· ∈ win rule) := fun w ↦
  inferInstanceAs (Decidable (∃ D ∈ rule, ∀ i ∈ D, w i = true))

instance [DecidableEq ι] (w₀ : ι → Bool) : DecidablePred (· ∈ homogeneousLoss rule w₀) := fun w ↦
  inferInstanceAs (Decidable (∀ D ∈ rule, ∀ i ∈ D, w₀ i = false → w i = false))

variable {rule} {w w₀ : ι → Bool}

/-- A win is the truth of some condition's plural predication, "the urns of the condition gave
colored balls". -/
theorem mem_win_iff_barePlural :
    w ∈ win rule ↔ ∃ D ∈ rule, Homogeneity.barePlural (fun i w ↦ w i = true) D w = 1 := by
  simp [win, Homogeneity.barePlural, SignType.supervaluation_eq_one_iff]

/-- In a losing round, the homogeneous loss is the homogeneous negation of the rule over the urns
white in that round (pp. 459, 468). -/
theorem mem_homogeneousLoss_iff_barePlural (h : w₀ ∉ win rule) :
    w ∈ homogeneousLoss rule w₀ ↔ ∀ D ∈ rule,
      Homogeneity.barePlural (fun i w ↦ w i = true) (D.filter (w₀ · = false)) w = -1 := by
  simp only [homogeneousLoss, mem_ofPred_eq, Homogeneity.barePlural,
    SignType.supervaluation_eq_neg_one_iff, Finset.mem_filter, and_imp, Bool.not_eq_true]
  refine forall₂_congr fun D hD ↦ (and_iff_right ?_).symm
  by_contra hne
  refine h ⟨D, hD, fun i hi ↦ ?_⟩
  by_contra hi'
  exact hne ⟨i, Finset.mem_filter.2 ⟨hi, by simpa using hi'⟩⟩

/-- A loss falls short of the homogeneous loss of the round where every urn is white exactly when
some condition's plural predication falls in the homogeneity gap. -/
theorem not_mem_homogeneousLoss_iff_indet (hw : w ∉ win rule) :
    w ∉ homogeneousLoss rule (fun _ ↦ false) ↔
      ∃ D ∈ rule, Homogeneity.barePlural (fun i w ↦ w i = true) D w = 0 := by
  simp only [win, mem_ofPred_eq, not_exists, not_and, not_forall] at hw
  simp only [homogeneousLoss, mem_ofPred_eq, Homogeneity.barePlural,
    SignType.supervaluation_eq_zero_iff, not_forall, Bool.not_eq_false, forall_const]
  exact ⟨fun ⟨D, hD, i, hi, h⟩ ↦ ⟨D, hD, ⟨i, hi, h⟩,
      let ⟨j, hj, h'⟩ := hw D hD; ⟨j, hj, h'⟩⟩,
    fun ⟨D, hD, ⟨i, hi, h⟩, _⟩ ↦ ⟨D, hD, i, hi, h⟩⟩

theorem homogeneousLoss_subset_compl_win (h : w₀ ∉ win rule) :
    homogeneousLoss rule w₀ ⊆ (win rule)ᶜ := by
  rintro w hw ⟨D, hD, hall⟩
  refine h ⟨D, hD, fun i hi ↦ ?_⟩
  by_contra h'
  simpa [hall i hi] using hw D hD i hi (by simpa using h')

theorem homogeneousLoss_eq_cause [Fintype ι] (hcover : ∀ i, ∃ D ∈ rule, i ∈ D) :
    homogeneousLoss rule w₀ = cause w₀ (Finset.univ.filter (w₀ · = false)) := by
  ext w
  simp only [homogeneousLoss, mem_ofPred_eq, mem_cause, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨fun h i hi ↦ ?_, fun h D _ i _ hi ↦ by rw [h i hi, hi]⟩
  obtain ⟨D, hD, hiD⟩ := hcover i
  rw [h D hD i hiD hi, hi]

end Rule

/-! ### Single causes under a rule of two conditions -/

section TwoConditions

variable {ι : Type*} [DecidableEq ι] {rule : Finset (Finset ι)} {X Y : ι} {R : Finset ι}
  {w₀ : ι → Bool}

theorem mem_win_pair_iff (hrule : rule = {{X, Y}, R}) {w : ι → Bool} :
    w ∈ win rule ↔ (w X = true ∧ w Y = true) ∨ w ∈ cause (fun _ ↦ true) R := by
  subst hrule
  simp [win, mem_cause]

theorem preimage_update_true_win (hrule : rule = {{X, Y}, R}) (hXY : X ≠ Y) (hXR : X ∉ R) :
    (Function.update · X true) ⁻¹' win rule =
      cause (fun _ ↦ true) {Y} ∪ cause (fun _ ↦ true) R := by
  ext w
  simp [mem_win_pair_iff hrule, update_mem_cause_iff hXR, mem_cause,
    Function.update_of_ne hXY.symm]

theorem preimage_update_false_win (hrule : rule = {{X, Y}, R}) (hXR : X ∉ R) :
    (Function.update · X false) ⁻¹' win rule = cause (fun _ ↦ true) R := by
  ext w
  simp [mem_win_pair_iff hrule, update_mem_cause_iff hXR]

variable [Fintype ι] {ν : ι → Measure Bool} [∀ i, IsProbabilityMeasure (ν i)]

theorem sufficiency_singleton_win (hrule : rule = {{X, Y}, R}) (hXY : X ≠ Y) (hXR : X ∉ R)
    (hYR : Y ∉ R) (hX : w₀ X = true) (hX' : ν X {false} ≠ 0)
    (hR : Measure.pi ν (cause (fun _ ↦ true) R)ᶜ ≠ 0) :
    sufficiency (Measure.pi ν) w₀ (win rule) {X} = ν Y {true} := by
  rw [sufficiency_singleton (by rwa [hX]), hX, Bool.not_true,
    preimage_update_true_win hrule hXY hXR,
    preimage_update_false_win hrule hXR, union_sdiff_right, sdiff_eq,
    measure_pi_inter_of_dependsOn dependsOn_cause (fun _ _ h ↦ by
      simp only [mem_compl_iff, dependsOn_cause h]) (Finset.disjoint_singleton_left.2 hYR),
    measure_pi_cause, Finset.prod_singleton, ENNReal.mul_div_cancel_right hR (measure_ne_top _ _)]

theorem sufficiency_singleton_compl_win (hrule : rule = {{X, Y}, R}) (hXY : X ≠ Y) (hXR : X ∉ R)
    (hYR : Y ∉ R) (hX : w₀ X = false) (hX' : ν X {true} ≠ 0) :
    sufficiency (Measure.pi ν) w₀ (win rule)ᶜ {X} =
      ν Y {true} * Measure.pi ν (cause (fun _ ↦ true) R)ᶜ /
        Measure.pi ν (cause (fun _ ↦ true) {Y} ∪ cause (fun _ ↦ true) R) := by
  rw [sufficiency_singleton (by rwa [hX]), hX, Bool.not_false, preimage_compl, preimage_compl,
    preimage_update_true_win hrule hXY hXR, preimage_update_false_win hrule hXR, compl_compl,
    sdiff_eq, compl_compl, inter_union_distrib_left, compl_inter_self, union_empty, inter_comm,
    measure_pi_inter_of_dependsOn dependsOn_cause (fun _ _ h ↦ by
      simp only [mem_compl_iff, dependsOn_cause h]) (Finset.disjoint_singleton_left.2 hYR),
    measure_pi_cause, Finset.prod_singleton]

end TwoConditions

/-! ### Experiment 2: the disjunctive rule -/

/-- In Experiment 2 the urns `a` and `b` share one color and the urns `c` and `d` the other. -/
inductive Urn₂ | a | b | c | d
  deriving DecidableEq, Fintype

open Urn₂

/-- Under the rule of Experiment 2, (1), the player wins with two balls of one color, from `a` and
`b` or from `c` and `d`. -/
def conditions : Finset (Finset Urn₂) := {{a, b}, {c, d}}

/-- `prior₂` gives each urn's probability of a colored ball in Experiment 2, from its 14, 2, 4 or
19 colored balls out of 20. -/
noncomputable def prior₂ : Urn₂ → I
  | a => ⟨7 / 10, by norm_num, by norm_num⟩
  | b => ⟨1 / 10, by norm_num, by norm_num⟩
  | c => ⟨1 / 5, by norm_num, by norm_num⟩
  | d => ⟨9 / 10, by norm_num, by norm_num⟩

theorem prior₂_pos (i : Urn₂) : 0 < prior₂ i :=
  Subtype.coe_lt_coe.1 (by cases i <;> norm_num [prior₂])

theorem prior₂_lt_one (i : Urn₂) : prior₂ i < 1 :=
  Subtype.coe_lt_coe.1 (by cases i <;> norm_num [prior₂])

/-- `triplePositive` is the round with colored balls from `a`, `b` and `d`, won through `a` and
`b`. -/
def triplePositive : Urn₂ → Bool
  | c => false
  | _ => true

/-- `tripleNegative` is the round with a colored ball from `c` only, lost. -/
def tripleNegative : Urn₂ → Bool
  | c => true
  | _ => false

/-- `partner X` is the other urn of `X`'s color. -/
def partner : Urn₂ → Urn₂
  | a => b
  | b => a
  | c => d
  | d => c

/-- `otherColor X` is the pair of urns of the color `X` does not have. -/
def otherColor : Urn₂ → Finset Urn₂
  | a | b => {c, d}
  | c | d => {a, b}

-- (1)
theorem conditions_eq_partner (X : Urn₂) :
    conditions = {{X, partner X}, otherColor X} ∧ X ≠ partner X ∧ X ∉ otherColor X ∧
      partner X ∉ otherColor X := by
  cases X <;> decide

section Experiment2

variable {s : I}

theorem causalStrength_singleton_win (hs : s < 1) (X : Urn₂) {w₀ : Urn₂ → Bool}
    (hX : w₀ X = true) :
    causalStrength s prior₂ w₀ (win conditions) {X} =
      propensity s (prior₂ X) true {true} *
          propensity s (prior₂ (partner X)) (w₀ (partner X)) {true} +
        if Function.update w₀ X false ∈ win conditions then 0
        else propensity s (prior₂ X) true {false} := by
  obtain ⟨hrule, hXY, hXR, hYR⟩ := conditions_eq_partner X
  have hX' := propensity_singleton_ne_zero hs (prior₂_pos X) (prior₂_lt_one X) true false
  have hR := sampling_ne_zero (w₀ := w₀) hs prior₂_pos prior₂_lt_one
    (A := (cause (fun _ ↦ true) (otherColor X))ᶜ) ⟨fun _ ↦ false, fun h ↦ by
      obtain ⟨i, hi⟩ : (otherColor X).Nonempty := by cases X <;> decide
      simpa using mem_cause.1 h i hi⟩
  unfold causalStrength sampling at *
  rw [score_singleton (by rw [hX]; exact hX'), sufficiency_singleton_win hrule hXY hXR hYR hX
    (by rw [hX]; exact hX') hR, hX]
  rfl

/-! #### The winning rounds -/

/-- In the round where every urn gave a colored ball, neither winning condition is necessary,
since the other still holds (p. 462). -/
theorem same_condition_pair_not_necessary (μ : Measure (Urn₂ → Bool)) :
    necessity μ (fun _ ↦ true) (win conditions) {a, b} = 0 ∧
      necessity μ (fun _ ↦ true) (win conditions) {c, d} = 0 :=
  ⟨necessity_eq_zero (by decide), necessity_eq_zero (by decide)⟩

/-- When every urn gives a colored ball, any pair across the two conditions is necessary to a
positive degree (p. 462). -/
theorem crossing_pair_necessary (hs : s < 1) {X Y : Urn₂} (hX : X ∈ ({a, b} : Finset Urn₂))
    (hY : Y ∈ ({c, d} : Finset Urn₂)) :
    0 < necessity (sampling s prior₂ fun _ ↦ true) (fun _ ↦ true) (win conditions) {X, Y} := by
  rw [necessity, cond_apply .of_discrete]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    (sampling_ne_zero hs prior₂_pos prior₂_lt_one ⟨fun _ ↦ false, ?_⟩)
  simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
  revert X Y; decide

/-- When every urn gives a colored ball, the model scores the two urns of a color alike, contrary to
the reported abnormal deflation (p. 463). -/
theorem partners_scored_alike (hs : s < 1) :
    causalStrength s prior₂ (fun _ ↦ true) (win conditions) {a} =
        causalStrength s prior₂ (fun _ ↦ true) (win conditions) {b} ∧
      causalStrength s prior₂ (fun _ ↦ true) (win conditions) {c} =
        causalStrength s prior₂ (fun _ ↦ true) (win conditions) {d} := by
  rw [causalStrength_singleton_win hs a rfl, causalStrength_singleton_win hs b rfl,
    causalStrength_singleton_win hs c rfl, causalStrength_singleton_win hs d rfl]
  simp only [partner,
    show ∀ X, Function.update (fun _ : Urn₂ ↦ true) X false ∈ win conditions by decide, ite_true,
    add_zero]
  exact ⟨mul_comm _ _, mul_comm _ _⟩

/-- In the round won through `a` and `b`, the pair of `a` and `b` scores one (p. 465). -/
theorem pair_scores_one (hs : s < 1) :
    causalStrength s prior₂ triplePositive (win conditions) {a, b} = 1 :=
  score_eq_one (by decide) (by decide)
    (sampling_ne_zero hs prior₂_pos prior₂_lt_one ⟨fun _ ↦ false, by decide⟩)

/-- In the round won through `a` and `b`, the colored ball from `d` is idle, since removing it
never removes the win (p. 464). -/
theorem idle_urn_not_necessary (μ : Measure (Urn₂ → Bool)) :
    necessity μ triplePositive (win conditions) {d} = 0 :=
  necessity_eq_zero (by decide)

/-- In the round won through `a` and `b`, the rarer colored ball from `b` outscores the one from `a`
(p. 465). -/
theorem triple_positive_abnormal_inflation (hs : s < 1) :
    causalStrength s prior₂ triplePositive (win conditions) {a} <
      causalStrength s prior₂ triplePositive (win conditions) {b} := by
  rw [causalStrength_singleton_win hs a rfl, causalStrength_singleton_win hs b rfl,
    ite_eq_right (by decide), ite_eq_right (by decide), show partner a = b from rfl,
    show partner b = a from rfl, show triplePositive b = true from rfl,
    show triplePositive a = true from rfl, mul_comm,
    ENNReal.add_lt_add_iff_left (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, propensity_real_singleton, propensity_real_singleton]
  have : (s : ℝ) < 1 := hs
  norm_num [prior₂]
  linarith

/-! #### The losing rounds -/

-- p. 467
theorem white_ball_redundant (μ : Measure (Urn₂ → Bool)) (i : Urn₂) :
    necessity μ (fun _ ↦ false) (win conditions)ᶜ {i} = 0 :=
  necessity_eq_zero (by revert i; decide)

-- p. 467
theorem white_ball_indispensable (hs : s < 1) (i : Urn₂) :
    necessity (sampling s prior₂ fun _ ↦ false) (fun _ ↦ false)
      (homogeneousLoss conditions fun _ ↦ false) {i} = 1 :=
  necessity_eq_one (by revert i; decide)
    (sampling_ne_zero hs prior₂_pos prior₂_lt_one ⟨fun _ ↦ true, by revert i; decide⟩)

private theorem deflation_aux {x y K : ℝ} (hy : 0 < y) (hyx : y < x) (hx : x < 1) (hK₀ : 0 ≤ K)
    (hK₁ : K < 1) :
    (1 - x) * (y * (1 - K) / (y + K - y * K)) < (1 - y) * (x * (1 - K) / (x + K - x * K)) := by
  have hdy : 0 < y + K - y * K := by nlinarith
  have hdx : 0 < x + K - x * K := by nlinarith
  rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hdy hdx]
  have key : (1 - y) * (x * (1 - K)) * (y + K - y * K) - (1 - x) * (y * (1 - K)) * (x + K - x * K) =
      (1 - K) * (x - y) * (x * y + K * (1 - x * y)) := by ring
  have : 0 < (1 - K) * (x - y) * (x * y + K * (1 - x * y)) := by
    have : 0 < x * y := by nlinarith
    have : 0 ≤ K * (1 - x * y) := mul_nonneg hK₀ (by nlinarith)
    positivity
  linarith

theorem causalStrength_singleton_compl_win_toReal (hs : s < 1) (X : Urn₂) :
    let q i := (propensity s (prior₂ i) false).real {true}
    let K := ∏ i ∈ otherColor X, q i
    (causalStrength s prior₂ (fun _ ↦ false) (win conditions)ᶜ {X}).toReal =
      (1 - q X) * (q (partner X) * (1 - K) / (q (partner X) + K - q (partner X) * K)) := by
  intro q K
  obtain ⟨hrule, hXY, hXR, hYR⟩ := conditions_eq_partner X
  set μ := Measure.pi fun i ↦ propensity s (prior₂ i) false
  have hK : μ.real (cause (fun _ ↦ true) (otherColor X)) = K := measureReal_pi_cause
  have hYK : μ.real (cause (fun _ ↦ true) {partner X} ∪ cause (fun _ ↦ true) (otherColor X)) =
      q (partner X) + K - q (partner X) * K := by
    have := measureReal_union_add_inter (μ := μ) (s := cause (fun _ ↦ true) {partner X})
      (MeasurableSet.of_discrete (s := cause (fun _ ↦ true) (otherColor X))) (measure_ne_top _ _)
      (measure_ne_top _ _)
    have hY : μ.real (cause (fun _ ↦ true) {partner X}) = q (partner X) := by
      rw [measureReal_pi_cause, Finset.prod_singleton]
    rw [measureReal_def (s := _ ∩ _), measure_pi_inter_of_dependsOn dependsOn_cause
      dependsOn_cause (Finset.disjoint_singleton_left.2 hYR), ENNReal.toReal_mul,
      ← measureReal_def, ← measureReal_def, hY, hK] at this
    linarith
  have hX₀ := propensity_singleton_ne_zero hs (prior₂_pos X) (prior₂_lt_one X) false true
  have hflip : Function.update (fun _ ↦ false) X true ∈ (win conditions)ᶜ := by
    cases X <;> decide
  have hqX : (propensity s (prior₂ X) false).real {false} = 1 - q X := by
    simp only [q, propensity_real_singleton]; simp; ring
  unfold causalStrength sampling
  rw [score_singleton (w₀ := fun _ ↦ false) (by exact hX₀)]
  simp only [Bool.not_false, hflip, ite_true, add_zero]
  rw [sufficiency_singleton_compl_win hrule hXY hXR hYR rfl hX₀, ENNReal.toReal_mul,
    ENNReal.toReal_div, ENNReal.toReal_mul]
  simp only [← measureReal_def]
  rw [hYK, probReal_compl_eq_one_sub .of_discrete, hK, hqX]

/-- Under the classical loss, the likelier white ball scores higher (`b` over `a`, `c` over `d`), an
abnormal deflation contrary to the participants (p. 466). -/
theorem classical_abnormal_deflation (hs : s < 1) :
    causalStrength s prior₂ (fun _ ↦ false) (win conditions)ᶜ {a} <
        causalStrength s prior₂ (fun _ ↦ false) (win conditions)ᶜ {b} ∧
      causalStrength s prior₂ (fun _ ↦ false) (win conditions)ᶜ {d} <
        causalStrength s prior₂ (fun _ ↦ false) (win conditions)ᶜ {c} := by
  have hs' : (s : ℝ) < 1 := hs
  have hq (i : Urn₂) : (propensity s (prior₂ i) false).real {true} = (1 - s) * prior₂ i := by
    simp [propensity_real_singleton]
  simp only [← ENNReal.toReal_lt_toReal causalStrength_ne_top causalStrength_ne_top]
  rw [causalStrength_singleton_compl_win_toReal hs a,
    causalStrength_singleton_compl_win_toReal hs b,
    causalStrength_singleton_compl_win_toReal hs c,
    causalStrength_singleton_compl_win_toReal hs d]
  simp only [partner, otherColor, Finset.prod_pair (show a ≠ b by decide),
    Finset.prod_pair (show c ≠ d by decide)]
  simp only [hq]
  norm_num [prior₂]
  have hs₀ : (0 : ℝ) ≤ s := s.2.1
  constructor <;> apply deflation_aux <;>
    nlinarith [mul_pos (sub_pos.2 hs') (sub_pos.2 hs'), mul_nonneg hs₀ (sub_pos.2 hs').le]

theorem homogeneousLoss_conditions (w₀ : Urn₂ → Bool) :
    homogeneousLoss conditions w₀ = cause w₀ (Finset.univ.filter (w₀ · = false)) :=
  homogeneousLoss_eq_cause (by decide)

/-- Under the homogeneous loss, of two pluralities of white balls the less likely scores higher. -/
theorem homogeneous_lt_iff (hs : s < 1) {w₀ : Urn₂ → Bool} {S S' : Finset Urn₂}
    (hS : ∀ i ∈ S, w₀ i = false) (hS' : ∀ i ∈ S', w₀ i = false) (hne : S.Nonempty)
    (hne' : S'.Nonempty) :
    causalStrength s prior₂ w₀ (homogeneousLoss conditions w₀) S <
        causalStrength s prior₂ w₀ (homogeneousLoss conditions w₀) S' ↔
      ∏ i ∈ S', (propensity s (prior₂ i) false).real {false} <
        ∏ i ∈ S, (propensity s (prior₂ i) false).real {false} := by
  have hc {U : Finset Urn₂} (hU : U.Nonempty) :=
    sampling_compl_cause_ne_zero (w₀ := w₀) (v := w₀) hs prior₂_pos prior₂_lt_one hU
  have hprod {U : Finset Urn₂} (hU : ∀ i ∈ U, w₀ i = false) :
      ∏ i ∈ U, (propensity s (prior₂ i) (w₀ i)).real {w₀ i} =
        ∏ i ∈ U, (propensity s (prior₂ i) false).real {false} :=
    Finset.prod_congr rfl fun i hi ↦ by rw [hU i hi]
  have hsub {U : Finset Urn₂} (hU : ∀ i ∈ U, w₀ i = false) :
      U ⊆ Finset.univ.filter (w₀ · = false) := fun i hi ↦ by simpa using hU i hi
  unfold causalStrength
  rw [homogeneousLoss_conditions]
  unfold sampling at hc ⊢
  rw [score_pi_cause_lt_iff (hsub hS) (hsub hS') (hc hne) (hc hne'),
    ← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, measureReal_pi_cause, measureReal_pi_cause, hprod hS, hprod hS']

/-- Under the homogeneous loss, a plurality of white balls scores higher than any proper part of it
(pp. 467, 469). -/
theorem homogeneous_lt_of_ssubset (hs : s < 1) {w₀ : Urn₂ → Bool} {S S' : Finset Urn₂}
    (hS : S.Nonempty) (h : S ⊂ S') (hS' : ∀ i ∈ S', w₀ i = false) :
    causalStrength s prior₂ w₀ (homogeneousLoss conditions w₀) S <
      causalStrength s prior₂ w₀ (homogeneousLoss conditions w₀) S' := by
  rw [homogeneousLoss_conditions]
  exact causalStrength_cause_lt_of_ssubset hs prior₂_pos prior₂_lt_one hS h
    fun i hi ↦ by simpa using hS' i hi

/-- Under the homogeneous loss, the less likely white ball scores higher, in the all-white round (p.
466) and when `c` gave a colored ball (p. 468). -/
theorem homogeneous_abnormal_inflation (hs : s < 1) :
    (causalStrength s prior₂ (fun _ ↦ false) (homogeneousLoss conditions fun _ ↦ false) {b} <
        causalStrength s prior₂ (fun _ ↦ false) (homogeneousLoss conditions fun _ ↦ false) {a} ∧
      causalStrength s prior₂ (fun _ ↦ false) (homogeneousLoss conditions fun _ ↦ false) {c} <
        causalStrength s prior₂ (fun _ ↦ false) (homogeneousLoss conditions fun _ ↦ false) {d}) ∧
    (causalStrength s prior₂ tripleNegative (homogeneousLoss conditions tripleNegative) {b} <
        causalStrength s prior₂ tripleNegative (homogeneousLoss conditions tripleNegative) {a} ∧
      causalStrength s prior₂ tripleNegative (homogeneousLoss conditions tripleNegative) {b, d} <
        causalStrength s prior₂ tripleNegative (homogeneousLoss conditions tripleNegative)
          {a, d}) := by
  have hs' : (s : ℝ) < 1 := hs
  rw [homogeneous_lt_iff hs (by decide) (by decide) (by decide) (by decide),
    homogeneous_lt_iff hs (by decide) (by decide) (by decide) (by decide),
    homogeneous_lt_iff hs (by decide) (by decide) (by decide) (by decide),
    homogeneous_lt_iff hs (by decide) (by decide) (by decide) (by decide)]
  simp [propensity_real_singleton, prior₂]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, ?_⟩
  nlinarith [mul_pos (sub_pos.2 hs') (sub_pos.2 hs'), mul_nonneg s.2.1 (sub_pos.2 hs').le]

/-- When only `c` gives a colored ball, the white ball from `d` is indispensable for the classical
loss and those from `a` and `b` are redundant (p. 468). -/
theorem classical_triple_negative (hs : s < 1) :
    necessity (sampling s prior₂ tripleNegative) tripleNegative (win conditions)ᶜ {d} = 1 ∧
      necessity (sampling s prior₂ tripleNegative) tripleNegative (win conditions)ᶜ {a} = 0 ∧
      necessity (sampling s prior₂ tripleNegative) tripleNegative (win conditions)ᶜ {b} = 0 :=
  ⟨necessity_eq_one (by decide)
      (sampling_ne_zero hs prior₂_pos prior₂_lt_one ⟨fun _ ↦ true, by decide⟩),
    necessity_eq_zero (by decide), necessity_eq_zero (by decide)⟩

/-- When only `c` gives a colored ball, the homogeneous loss is ¬A ∧ ¬B ∧ ¬D (p. 468). -/
theorem homogeneousLoss_tripleNegative :
    homogeneousLoss conditions tripleNegative = {w | w a = false ∧ w b = false ∧ w d = false} :=
  Set.ext fun w ↦ by revert w; decide

end Experiment2

end KonukEtAl2026
