module

public import Mathlib.Probability.UniformOn
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Attitudes.Preference.ExpectedValue
public import Linglib.Data.Examples.ChungMascarenhas2023

/-!
# Chung and Mascarenhas (2023): Modality, expected utility, and hypothesis testing

This file formalizes the semantics of necessity modals as expected value that Chung and
Mascarenhas propose, together with its applications to the miners puzzle and to two reasoning
fallacies, and the derivations the paper runs against the rival accounts.

Necessity modals share one semantics over a family `R` of relevant propositions: `expectedValue`
is the conditional expectation of the number `countTrue R` of relevant propositions true at a
world ((5) and (7)), equal to the sum of the likelihoods of the evidence (12), and `must φ` holds
when `φ`'s expected value alone clears a threshold `θ` (6). Read deontically the expectation is
`φ`'s expected utility, read epistemically its explanatory value; `ought φ` asks instead that `φ`
be strictly best among the good-enough (17) and follows from `must φ` (`ought_of_must`); `might`
is `must`'s dual with the polar alternative (59); and the §5 plausibility patch `mustPlausible`
adds a reasonably high prior for the prejacent. A prejacent entailing all its evidence has
maximal explanatory value (`expectedValue_eq_card_of_subset`), the §7 question-begging
`P(φ ∣ φ)` and the §5 problem of success, and the deontic reading is Lassiter's expected-value
scale (`toReal_expectedValue`), the paper's "reproduction of Lassiter's analysis". The Korean
conditional evaluative *cip-ey iss-eya toy-n-ta* composes the evaluative predicate, the
conditional, Lassiter's threshold (46) and the *-(e)ya* exhaustifier into exactly (6) (§4, (48)).

In the miners puzzle of Kolodny and MacFarlane (§3.1), stated over any measure satisfying the
paper's assumptions (equiprobable locations independent of the action, with `uniformOn` as
witness) and the ideals (18) of Cariani, Kaufmann and Kaufmann, blocking neither shaft is the
only good-enough option for a threshold between 5 and 9 (26a), the conditional *must* needs one
between 9 and 10 (25b), and no single threshold serves both (`must_thresholds_incompatible`);
`kratzer_miners_unsatisfiable` is the paper's proof sketch (16) that no ordering source lets the
classical account verify all of (15a)–(15c), and `expectedValue_inA_lt_inA_blockNeither` is
footnote 17's observation that blocking neither stays above the expected utility of
indifference. The modal conjunction fallacy (34) and modal base-rate neglect (41) are theorems
about `must` over every measure realizing the paper's printed conditional probabilities, each
with a finite witness model; the Kratzer row of Table 2 is `Modality.necessity_and_left`,
conjunction elimination, which the expected-value `must` escapes.

## Implementation notes

* The paper world-indexes the probability function `Pr_w` (its fn 9); the formalization fixes a
  single measure, as no formalized claim varies the evaluation world.
* Alternative sets are explicit `Set (Set W)` arguments (the paper's fn 8 leaves their source to
  the question under discussion); `might` hard-codes the polar alternative, following §6.
* Printed probabilities enter as hypotheses on conditional measures, decimals as
  `ENNReal.ofReal` values and the miners' utilities as exact numerals; no parallel rational
  arithmetic.
* The alternative log-likelihood formulation ((13)–(14)) and its `might` variant are not
  formalized: the paper sets them aside after noting (6) suffices.

## References

* [W. Chung and S. Mascarenhas, *Modality, expected utility, and hypothesis testing*
  (2023)][chung-mascarenhas-2023]
* [N. Kolodny and J. MacFarlane, *Ifs and oughts* (2010)][kolodny-macfarlane-2010]
* [F. Cariani, M. Kaufmann and S. Kaufmann, *Deliberative modality under epistemic uncertainty*
  (2013)][cariani-kaufmann-kaufmann-2013]
* [A. Kratzer, *Modality* (1991)][kratzer-1991]
* [D. Lassiter, *Measurement and Modality* (2011)][lassiter-2011]
* [D. Lassiter, *Graded Modality* (2017)][lassiter-2017]
* [K. von Fintel and S. Iatridou, *What to do if you want to go to
  Harlem* (2005)][von-fintel-iatridou-2005]
* [A. Tversky and D. Kahneman, *Extensional Versus Intuitive Reasoning: The Conjunction Fallacy in
  Probability Judgment* (1983)][tversky-kahneman-1983]
* [D. Kahneman and A. Tversky, *On the psychology of prediction* (1973)][kahneman-tversky-1973]
-/

@[expose] public section

namespace ChungMascarenhas2023

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

variable {W : Type*} [MeasurableSpace W] [DiscreteMeasurableSpace W] {ι : Type*} [Fintype ι]

/-! ### The measure function and expected value -/

/-- The measure function `μ_EVAL` gives the number of relevant propositions `R i` true at a
world, as the sum of their indicators (7). The relevant propositions are an indexed family and
not a finite set of propositions, so that extensionally coincident rules keep their
multiplicity. -/
noncomputable def countTrue (R : ι → Set W) : W → ℝ≥0∞ :=
  ∑ i, (R i).indicator 1

omit [MeasurableSpace W] [DiscreteMeasurableSpace W] in
@[simp] theorem countTrue_apply (R : ι → Set W) (a : W) [∀ i, Decidable (a ∈ R i)] :
    countTrue R a = (Finset.univ.filter (a ∈ R ·)).card := by
  simp [countTrue, Set.indicator_apply, Finset.sum_boole]

/-- The expected value of `φ` is the conditional expectation of `μ_EVAL` given `φ` (5), expected
utility read deontically and explanatory value read epistemically. -/
noncomputable def expectedValue (p : Measure W) (R : ι → Set W) (φ : Set W) : ℝ≥0∞ :=
  ∫⁻ w, countTrue R w ∂p[|φ]

/-- The expected value of a hypothesis is the sum `Σ_i P(R i ∣ φ)` of the likelihoods of the
relevant propositions (12). -/
theorem expectedValue_eq_sum_cond (p : Measure W) (R : ι → Set W) (φ : Set W) :
    expectedValue p R φ = ∑ i, p[R i | φ] := by
  simp only [expectedValue, countTrue, Finset.sum_apply]
  rw [lintegral_finsetSum _ fun i _ ↦ Measurable.of_discrete]
  exact Finset.sum_congr rfl fun i _ ↦ lintegral_indicator_one MeasurableSet.of_discrete

theorem expectedValue_le_card (p : Measure W) (R : ι → Set W) (φ : Set W) :
    expectedValue p R φ ≤ Fintype.card ι := by
  rw [expectedValue_eq_sum_cond]
  calc ∑ i, p[R i | φ] ≤ ∑ _i : ι, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ ↦ prob_le_one
  _ = Fintype.card ι := by simp

/-- A prejacent entailing every piece of evidence has maximal explanatory value: each
`P(R i ∣ φ)` is the question-begging `P(φ ∣ φ)`, "as high as any probability can get" (§7). -/
theorem expectedValue_eq_card_of_subset (p : Measure W) [IsFiniteMeasure p] (R : ι → Set W)
    (φ : Set W) (hφ : p φ ≠ 0) (h : ∀ i, φ ⊆ R i) : expectedValue p R φ = Fintype.card ι := by
  rw [expectedValue_eq_sum_cond]
  have : ∀ i, p[R i | φ] = 1 := fun i ↦ by
    rw [cond_apply MeasurableSet.of_discrete, Set.inter_eq_left.2 (h i),
      ENNReal.inv_mul_cancel hφ (measure_ne_top _ _)]
  simp [this]

/-- A hypothesis that fully predicts the evidence is weakly best, whatever its prior: the §5
problem of success behind (50)–(51), which the plausibility requirement answers. -/
theorem expectedValue_le_of_cond_eq_one {p : Measure W} {e φ : Set W} (ψ : Set W)
    (h : p[e | φ] = 1) : expectedValue p ![e] ψ ≤ expectedValue p ![e] φ := by
  simp only [expectedValue_eq_sum_cond, Fin.sum_univ_one, Matrix.cons_val_zero, h]
  exact prob_le_one

/-- The deontic reading is Lassiter's expected-value scale with value function `μ_EVAL`: the
paper's §3.1 is "more or less a reproduction of Lassiter's analysis". -/
theorem toReal_expectedValue (p : Measure W) (R : ι → Set W) (φ : Set W) :
    (expectedValue p R φ).toReal =
      Desire.ExpectedValue.expectedValue p (fun w ↦ (countTrue R w).toReal) Set.univ φ := by
  rw [Desire.ExpectedValue.expectedValue, Set.univ_inter, expectedValue,
    integral_toReal Measurable.of_discrete.aemeasurable]
  exact Filter.Eventually.of_forall fun w ↦ by
    simp only [countTrue, Finset.sum_apply]
    exact ENNReal.sum_lt_top.2 fun i _ ↦
      (((R i).indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ zero_le_one).trans_lt
        ENNReal.one_lt_top)

theorem uniformOn_univ_cond_apply [Fintype W] (s t : Set W) [DecidablePred (· ∈ t)]
    [DecidablePred (· ∈ (t ∩ s))] :
    (uniformOn (Set.univ : Set W))[s | t]
      = (Finset.univ.filter (· ∈ t ∩ s)).card / (Finset.univ.filter (· ∈ t)).card := by
  have hc : ∀ u : Set W, ∀ [DecidablePred (· ∈ u)],
      Measure.count u = ((Finset.univ.filter (· ∈ u)).card : ℝ≥0∞) := fun u _ ↦
    (congrArg Measure.count (by ext; simp)).trans (Measure.count_apply_finset _)
  rw [MeasureTheory.uniformOn_cond Set.finite_univ MeasurableSet.of_discrete, Set.univ_inter,
    uniformOn, cond_apply MeasurableSet.of_discrete, div_eq_mul_inv, mul_comm, hc, hc]

theorem expectedValue_uniformOn_univ [Fintype W] (R : ι → Set W) (φ : Set W)
    [DecidablePred (· ∈ φ)] [∀ i, DecidablePred (· ∈ (φ ∩ R i))] :
    expectedValue (uniformOn (Set.univ : Set W)) R φ
      = ((∑ i, (Finset.univ.filter (· ∈ φ ∩ R i)).card : ℕ) : ℝ≥0∞)
          / (Finset.univ.filter (· ∈ φ)).card := by
  simp only [expectedValue_eq_sum_cond, uniformOn_univ_cond_apply, div_eq_mul_inv,
    Finset.sum_mul, Nat.cast_sum]

theorem uniformOn_univ_cond_eq_ofReal [Fintype W] {s t : Set W} [DecidablePred (· ∈ t)]
    [DecidablePred (· ∈ (t ∩ s))] {m n : ℕ} {q : ℝ}
    (hs : (Finset.univ.filter (· ∈ t ∩ s)).card = m) (ht : (Finset.univ.filter (· ∈ t)).card = n)
    (hn : n ≠ 0) (hq : q = m / n) : (uniformOn (Set.univ : Set W))[s | t] = ENNReal.ofReal q := by
  rw [uniformOn_univ_cond_apply, hs, ht, hq,
    ENNReal.ofReal_div_of_pos (by exact_mod_cast hn.bot_lt), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-! ### The operators -/

/-- `must φ` holds iff the expected value of `φ` exceeds the threshold `θ` and no alternative's
does, `φ` being the only good-enough option or explanation (6). -/
def must (p : Measure W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W)) (θ : ℝ≥0∞) : Prop :=
  θ < expectedValue p R φ ∧ ∀ ψ ∈ alts, expectedValue p R ψ ≤ θ

/-- `ought φ` holds iff `φ` is the best good-enough option, above `θ` and of strictly greater
expected value than every alternative (17). -/
def ought (p : Measure W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W)) (θ : ℝ≥0∞) : Prop :=
  θ < expectedValue p R φ ∧ ∀ ψ ∈ alts, expectedValue p R ψ < expectedValue p R φ

/-- `must` with the plausibility requirement of a reasonably high prior for the prejacent (§5),
kept separate as the paper presents it as an add-on. -/
def mustPlausible (p : Measure W) (R : ι → Set W) (φ : Set W) (alts : Set (Set W))
    (θ θplaus : ℝ≥0∞) : Prop :=
  must p R φ alts θ ∧ θplaus ≤ p φ

/-- `might φ` is `¬ must ¬φ`, with the alternative set fixed as the polar alternative (59). -/
def might (p : Measure W) (R : ι → Set W) (φ : Set W) (θ : ℝ≥0∞) : Prop :=
  ¬ must p R φᶜ {φ} θ

variable {p : Measure W} {R : ι → Set W} {φ : Set W} {alts : Set (Set W)} {θ θplaus : ℝ≥0∞}

omit [DiscreteMeasurableSpace W] in
/-- `ought` is the semantics for `must` minus the requirement that `φ` be the only good-enough
alternative (§3.1), after the weak-necessity literature [von-fintel-iatridou-2005]. -/
theorem ought_of_must (h : must p R φ alts θ) : ought p R φ alts θ :=
  ⟨h.1, fun ψ hψ ↦ (h.2 ψ hψ).trans_lt h.1⟩

omit [DiscreteMeasurableSpace W] in
/-- An implausible prejacent is never a `must`, whatever its explanatory value: §5's resolution
of (49) and its 99-lawyers prediction. -/
theorem not_mustPlausible_of_lt (h : p φ < θplaus) : ¬ mustPlausible p R φ alts θ θplaus :=
  fun h' ↦ h.not_ge h'.2

omit [DiscreteMeasurableSpace W] in
/-- The disjunctive truth conditions of `might` that the paper writes out under (59). -/
theorem might_iff : might p R φ θ ↔ expectedValue p R φᶜ ≤ θ ∨ θ < expectedValue p R φ := by
  simp [might, must, imp_iff_not_or, not_lt]

omit [DiscreteMeasurableSpace W] in
/-- *It must be raining, but of course it might not be* is contradictory (§6). -/
theorem not_must_and_might_compl : ¬ (must p R φ {φᶜ} θ ∧ might p R φᶜ θ) :=
  fun ⟨h, h'⟩ ↦ h' (by simpa using h)

/-! ### Korean conditional evaluatives (§4) -/

/-- Lassiter's threshold Θ (46) applied to the conditional *if φ, then eval*, whose denotation
is the conditional expectation of `μ_EVAL` (45). -/
def conditionalEval (p : Measure W) (R : ι → Set W) (φ : Set W) (θ : ℝ≥0∞) : Prop :=
  θ < ∫⁻ w, countTrue R w ∂p[|φ]

/-- The left-hand side of (48), the composition of *cip-ey iss-eya toy-n-ta*: the *-(e)ya*
exhaustifier negates each alternative's thresholded conditional. -/
def koreanConditionalEvaluative (p : Measure W) (R : ι → Set W) (φ : Set W)
    (alts : Set (Set W)) (θ : ℝ≥0∞) : Prop :=
  conditionalEval p R φ θ ∧ ∀ ψ ∈ alts, ¬ conditionalEval p R ψ θ

omit [DiscreteMeasurableSpace W] in
/-- The Korean composition is the `must` semantics (6): this is (48). -/
theorem koreanConditionalEvaluative_iff_must :
    koreanConditionalEvaluative p R φ alts θ ↔ must p R φ alts θ := by
  simp only [koreanConditionalEvaluative, conditionalEval, must, expectedValue, not_lt]

/-! ### The miners puzzle (§3.1) -/

namespace Miners

/-- The actions available in the miners scenario. -/
inductive Action
  | blockA | blockB | blockNeither
  deriving DecidableEq, Fintype

/-- The shaft the miners are in. -/
inductive Shaft
  | A | B
  deriving DecidableEq, Fintype

/-- The six action-by-location worlds of Table 1. -/
abbrev World := Action × Shaft

instance : MeasurableSpace World := ⊤

/-- The proposition that action `a` is taken. -/
abbrev act (a : Action) : Set World := {w | w.1 = a}

/-- The proposition that the miners are in shaft `s`. -/
abbrev inShaft (s : Shaft) : Set World := {w | w.2 = s}

/-- The miners saved at each world (Table 1). -/
def saved : World → ℕ
  | (.blockA, .A) => 10
  | (.blockA, .B) => 0
  | (.blockB, .A) => 0
  | (.blockB, .B) => 10
  | (.blockNeither, _) => 9

/-- The ideals `R_D` of (18), after Cariani, Kaufmann and Kaufmann, are {one miner saved, …, ten
miners saved}: ideal `k` holds where at least `k + 1` miners are saved. An indexed family is
essential, since ideals one through nine coincide in extension on the six worlds. -/
abbrev idealsRD : Fin 10 → Set World := fun k ↦ {w | k.val < saved w}

/-- The uniform prior, the paper's background assumptions in their simplest realization. -/
noncomputable def prior : Measure World := uniformOn Set.univ

instance : Inhabited World := ⟨(.blockNeither, .A)⟩

instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

theorem prior_ne_zero {A : Set World} (h : A.Nonempty) : prior A ≠ 0 := by
  rw [prior, Ne, uniformOn_eq_zero_iff Set.finite_univ, Set.univ_inter]
  exact h.ne_empty

theorem countTrue_idealsRD (w : World) : countTrue idealsRD w = saved w := by
  rw [countTrue_apply, Nat.cast_inj]
  revert w; decide

/-! The expected utilities (19)–(21) and (23) under the paper's stated assumptions: the
locations are equiprobable and independent of the action, and the conditioned propositions
carry mass. -/

/-- Blocking shaft A has expected utility 5 (20). -/
theorem expectedValue_blockA_of_cond (p : Measure World) [IsFiniteMeasure p]
    (h : p[inShaft .A | act .blockA] = 1 / 2) :
    expectedValue p idealsRD (act .blockA) = 5 := by
  rw [expectedValue_eq_sum_cond]
  have hk : ∀ k : Fin 10, act .blockA ∩ idealsRD k = act .blockA ∩ inShaft .A := fun k ↦
    Set.ext fun w ↦ by revert w k; decide
  have hcond : ∀ k : Fin 10, p[idealsRD k | act .blockA] = 1 / 2 := fun k ↦ by
    rw [← h, cond_apply MeasurableSet.of_discrete, cond_apply MeasurableSet.of_discrete, hk]
  simp only [hcond, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, eq_comm, ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  norm_num

/-- Blocking shaft B has expected utility 5 (21). -/
theorem expectedValue_blockB_of_cond (p : Measure World) [IsFiniteMeasure p]
    (h : p[inShaft .B | act .blockB] = 1 / 2) :
    expectedValue p idealsRD (act .blockB) = 5 := by
  rw [expectedValue_eq_sum_cond]
  have hk : ∀ k : Fin 10, act .blockB ∩ idealsRD k = act .blockB ∩ inShaft .B := fun k ↦
    Set.ext fun w ↦ by revert w k; decide
  have hcond : ∀ k : Fin 10, p[idealsRD k | act .blockB] = 1 / 2 := fun k ↦ by
    rw [← h, cond_apply MeasurableSet.of_discrete, cond_apply MeasurableSet.of_discrete, hk]
  simp only [hcond, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, eq_comm, ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  norm_num

/-- Blocking neither shaft has expected utility 9 whatever the distribution (19): one miner
drowns whatever their location. -/
theorem expectedValue_blockNeither_of_ne (p : Measure World) [IsFiniteMeasure p]
    (h : p (act .blockNeither) ≠ 0) : expectedValue p idealsRD (act .blockNeither) = 9 := by
  rw [expectedValue_eq_sum_cond, Fin.sum_univ_castSucc]
  have hk : ∀ k : Fin 9, act .blockNeither ∩ idealsRD k.castSucc = act .blockNeither := fun k ↦
    Set.ext fun w ↦ by revert w k; decide
  have hlast : act .blockNeither ∩ idealsRD (Fin.last 9) = ∅ :=
    Set.ext fun w ↦ by revert w; decide
  have h1 : ∀ k : Fin 9, p[idealsRD k.castSucc | act .blockNeither] = 1 := fun k ↦ by
    rw [cond_apply MeasurableSet.of_discrete, hk, ENNReal.inv_mul_cancel h (measure_ne_top _ _)]
  rw [cond_apply MeasurableSet.of_discrete, hlast]
  simp [h1]

theorem expectedValue_inA_blockNeither_of_ne (p : Measure World) [IsFiniteMeasure p]
    (h : p (inShaft .A ∩ act .blockNeither) ≠ 0) :
    expectedValue p idealsRD (inShaft .A ∩ act .blockNeither) = 9 := by
  rw [expectedValue_eq_sum_cond, Fin.sum_univ_castSucc]
  have hk : ∀ k : Fin 9,
      inShaft .A ∩ act .blockNeither ∩ idealsRD k.castSucc = inShaft .A ∩ act .blockNeither :=
    fun k ↦ Set.ext fun w ↦ by revert w k; decide
  have hlast : inShaft .A ∩ act .blockNeither ∩ idealsRD (Fin.last 9) = ∅ :=
    Set.ext fun w ↦ by revert w; decide
  have h1 : ∀ k : Fin 9, p[idealsRD k.castSucc | inShaft .A ∩ act .blockNeither] = 1 := fun k ↦ by
    rw [cond_apply MeasurableSet.of_discrete, hk, ENNReal.inv_mul_cancel h (measure_ne_top _ _)]
  rw [cond_apply MeasurableSet.of_discrete, hlast]
  simp [h1]

/-- Conditionalized on the miners being in A, blocking A has expected utility 10 (23): the
prejacent realizes every ideal. -/
theorem expectedValue_inA_blockA_of_ne (p : Measure World) [IsFiniteMeasure p]
    (h : p (inShaft .A ∩ act .blockA) ≠ 0) :
    expectedValue p idealsRD (inShaft .A ∩ act .blockA) = 10 :=
  (expectedValue_eq_card_of_subset p idealsRD _ h fun k w hw ↦ by revert w k; decide).trans
    (by simp)

theorem expectedValue_inA_blockB (p : Measure World) [IsFiniteMeasure p] :
    expectedValue p idealsRD (inShaft .A ∩ act .blockB) = 0 := by
  rw [expectedValue_eq_sum_cond]
  have hk : ∀ k : Fin 10, inShaft .A ∩ act .blockB ∩ idealsRD k = ∅ := fun k ↦
    Set.ext fun w ↦ by revert w k; decide
  simp [cond_apply MeasurableSet.of_discrete, hk]

variable {p : Measure World} [IsFiniteMeasure p] {θ : ℝ≥0∞}

/-- *We ought to block neither shaft* holds for any `θ < 9` (22). -/
theorem ought_blockNeither (hbn : p (act .blockNeither) ≠ 0)
    (hA : p[inShaft .A | act .blockA] = 1 / 2) (hB : p[inShaft .B | act .blockB] = 1 / 2)
    (hθ : θ < 9) : ought p idealsRD (act .blockNeither) {act .blockA, act .blockB} θ := by
  refine ⟨expectedValue_blockNeither_of_ne p hbn ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [expectedValue_blockA_of_cond p hA, expectedValue_blockNeither_of_ne p hbn]; norm_num
  · rw [expectedValue_blockB_of_cond p hB, expectedValue_blockNeither_of_ne p hbn]; norm_num

/-- *If the miners are in shaft A, we ought to block shaft A* holds for any `θ < 10`, the
if-clause conditionalizing every expected utility on its antecedent (fn 16, after Lassiter).
This is (24). -/
theorem ought_if_inA_blockA (hbA : p (inShaft .A ∩ act .blockA) ≠ 0)
    (hbn : p (inShaft .A ∩ act .blockNeither) ≠ 0) (hθ : θ < 10) :
    ought p idealsRD (inShaft .A ∩ act .blockA)
      {inShaft .A ∩ act .blockNeither, inShaft .A ∩ act .blockB} θ := by
  refine ⟨expectedValue_inA_blockA_of_ne p hbA ▸ hθ, ?_⟩
  rintro ψ (rfl | rfl)
  · rw [expectedValue_inA_blockNeither_of_ne p hbn, expectedValue_inA_blockA_of_ne p hbA]
    norm_num
  · rw [expectedValue_inA_blockB p, expectedValue_inA_blockA_of_ne p hbA]; norm_num

/-- *We must block neither shaft* holds for `5 ≤ θ < 9`, blocking neither being the only
good-enough option (26a). -/
theorem must_blockNeither (hbn : p (act .blockNeither) ≠ 0)
    (hA : p[inShaft .A | act .blockA] = 1 / 2) (hB : p[inShaft .B | act .blockB] = 1 / 2)
    (h5 : 5 ≤ θ) (h9 : θ < 9) :
    must p idealsRD (act .blockNeither) {act .blockA, act .blockB} θ := by
  refine ⟨expectedValue_blockNeither_of_ne p hbn ▸ h9, ?_⟩
  rintro ψ (rfl | rfl)
  · exact expectedValue_blockA_of_cond p hA ▸ h5
  · exact expectedValue_blockB_of_cond p hB ▸ h5

/-- Read as *must*, (25b) holds for `9 ≤ θ < 10`, since conditionalized on the miners being in A
blocking A is the only good-enough option, with blocking neither sitting at 9. -/
theorem must_if_inA_blockA (hbA : p (inShaft .A ∩ act .blockA) ≠ 0)
    (hbn : p (inShaft .A ∩ act .blockNeither) ≠ 0) (h9 : 9 ≤ θ) (h10 : θ < 10) :
    must p idealsRD (inShaft .A ∩ act .blockA)
      {inShaft .A ∩ act .blockNeither, inShaft .A ∩ act .blockB} θ := by
  refine ⟨expectedValue_inA_blockA_of_ne p hbA ▸ h10, ?_⟩
  rintro ψ (rfl | rfl)
  · exact expectedValue_inA_blockNeither_of_ne p hbn ▸ h9
  · exact expectedValue_inA_blockB p ▸ bot_le

/-- No single threshold verifies both *must* claims, since (26a) needs `θ < 9` while (25b)
needs `9 ≤ θ`; positivity of the two block-neither propositions is all it takes. -/
theorem must_thresholds_incompatible (hbn : p (act .blockNeither) ≠ 0)
    (hAbn : p (inShaft .A ∩ act .blockNeither) ≠ 0) :
    ¬ ∃ θ, must p idealsRD (act .blockNeither) {act .blockA, act .blockB} θ ∧
      must p idealsRD (inShaft .A ∩ act .blockA)
        {inShaft .A ∩ act .blockNeither, inShaft .A ∩ act .blockB} θ := by
  rintro ⟨θ, ⟨h9, -⟩, ⟨-, halts⟩⟩
  have h := halts _ (Set.mem_insert _ _)
  rw [expectedValue_inA_blockNeither_of_ne p hAbn] at h
  rw [expectedValue_blockNeither_of_ne p hbn] at h9
  exact h.not_gt h9

/-! Under the uniform prior the paper's assumptions hold, and footnote 17's indifference
calculation goes through. -/

theorem prior_cond_inShaft (s : Shaft) (a : Action) :
    prior[inShaft s | act a] = 1 / 2 := by
  rw [prior, uniformOn_univ_cond_apply]
  rcases s with _ | _ <;> rcases a with _ | _ | _ <;>
    · rw [show (Finset.univ.filter (· ∈ act _ ∩ inShaft _)).card = 1 by decide,
        show (Finset.univ.filter (· ∈ act _)).card = 2 by decide, Nat.cast_one, Nat.cast_ofNat]

/-- Under the uniform prior, indifference given in-A — the union of the three actions,
footnote 17's comparison point for Lassiter's `must` — has expected utility 19/3. -/
theorem expectedValue_inA : expectedValue prior idealsRD (inShaft .A) = 19 / 3 := by
  rw [prior, expectedValue_uniformOn_univ,
    show (∑ i : Fin 10, (Finset.univ.filter (· ∈ inShaft .A ∩ idealsRD i)).card) = 19 by decide,
    show (Finset.univ.filter (· ∈ inShaft .A)).card = 3 by decide]
  norm_num

/-- Blocking neither stays above indifference given in-A, so a `must` that compares the
alternatives to indifference, as footnote 17 reads Lassiter, cannot verify (25b). -/
theorem expectedValue_inA_lt_inA_blockNeither :
    expectedValue prior idealsRD (inShaft .A)
      < expectedValue prior idealsRD (inShaft .A ∩ act .blockNeither) := by
  rw [expectedValue_inA, expectedValue_inA_blockNeither_of_ne prior
      (prior_ne_zero ⟨(.blockNeither, .A), by constructor <;> rfl⟩),
    ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

/-- The paper's claims are not vacuous: the uniform prior realizes them at `θ = 7`. -/
example :
    must prior idealsRD (act .blockNeither) {act .blockA, act .blockB} 7 :=
  must_blockNeither (prior_ne_zero ⟨(.blockNeither, .A), rfl⟩)
    (prior_cond_inShaft .A .blockA) (prior_cond_inShaft .B .blockB)
    (by norm_num) (by norm_num)

/-! The classical account, run on the same scenario. -/

open Modality in
/-- Following the paper's proof sketch (16), over any modal base whose accessible worlds locate
the miners in one of the two shafts and any ordering source with best worlds — the paper's limit
assumption, its fn 1 — the three *ought* claims of (15) are jointly unsatisfiable on Kratzer's
account [kratzer-1991], the if-clauses restricting the modal base. -/
theorem kratzer_miners_unsatisfiable {V : Type*} (f g : Background V)
    (w : V) (inA inB bA bB bN : V → Prop)
    (hbest : (bestWorlds f g w).Nonempty)
    (hcover : ∀ v ∈ f.accessibleWorlds w, inA v ∨ inB v)
    (hA : ∀ v, bA v → ¬ bN v) (hB : ∀ v, bB v → ¬ bN v) :
    ¬ (necessity f g bN w ∧ necessity (f.restrict inA) g bA w ∧
        necessity (f.restrict inB) g bB w) := by
  rintro ⟨hN, hAB, hBB⟩
  obtain ⟨v, hv⟩ := hbest
  have hacc : v ∈ f.accessibleWorlds w := Preorder.minimals_subset _ _ hv
  have key : ∀ α : V → Prop, α v → v ∈ bestWorlds (f.restrict α) g w := fun α hα ↦
    Preorder.mem_minimals_of_subset (fun _ hu ↦ (Background.mem_accessibleWorlds_restrict.1 hu).1)
      hv
      (Background.mem_accessibleWorlds_restrict.2 ⟨hacc, hα⟩)
  rcases hcover v hacc with h | h
  · exact hA v (hAB v (key inA h)) (hN v hv)
  · exact hB v (hBB v (key inB h)) (hN v hv)

end Miners

/-! ### Modal Linda (§3.2) -/

namespace ModalLinda

/-- In the modal conjunction fallacy ((30)–(34)), for every measure realizing the printed
conditional probabilities and any threshold in `[0.5, 1.5)`, *Linda must be a feminist bank
teller* is true and *Linda must be a bank teller* false, although the feminist tellers are a
subset of the tellers and so no more probable. The expected values are (32) and (33); by
`Modality.necessity_and_left` no Kratzer reading of *must* can pattern this way. -/
theorem modal_conjunction_fallacy (p : Measure W) (R : Fin 2 → Set W)
    (teller feministTeller : Set W) (hsub : feministTeller ⊆ teller)
    (h₁ : p[R 0 | teller] = .ofReal 0.3) (h₂ : p[R 1 | teller] = .ofReal 0.2)
    (h₃ : p[R 0 | feministTeller] = .ofReal 0.8) (h₄ : p[R 1 | feministTeller] = .ofReal 0.7)
    {θ : ℝ≥0∞} (hlo : .ofReal 0.5 ≤ θ) (hhi : θ < .ofReal 1.5) :
    must p R feministTeller {teller} θ ∧ ¬ must p R teller {feministTeller} θ ∧
      p feministTeller ≤ p teller := by
  have hT : expectedValue p R teller = .ofReal 0.5 := by
    rw [expectedValue_eq_sum_cond, Fin.sum_univ_two, h₁, h₂, ← ENNReal.ofReal_add] <;> norm_num
  have hF : expectedValue p R feministTeller = .ofReal 1.5 := by
    rw [expectedValue_eq_sum_cond, Fin.sum_univ_two, h₃, h₄, ← ENNReal.ofReal_add] <;> norm_num
  refine ⟨⟨hF ▸ hhi, ?_⟩, fun h ↦ (hT ▸ h.1).not_ge hlo, measure_mono hsub⟩
  rintro ψ rfl
  exact hT ▸ hlo

/-- The printed probabilities (30)–(31) are consistent: forty equiprobable worlds, ten of them
feminist tellers. -/
theorem exists_model :
    ∃ (p : Measure (Fin 40)) (R : Fin 2 → Set (Fin 40)) (teller feministTeller : Set (Fin 40)),
      feministTeller ⊆ teller ∧
      p[R 0 | teller] = .ofReal 0.3 ∧ p[R 1 | teller] = .ofReal 0.2 ∧
      p[R 0 | feministTeller] = .ofReal 0.8 ∧ p[R 1 | feministTeller] = .ofReal 0.7 := by
  refine ⟨uniformOn Set.univ, ![{w | w.val < 8 ∨ (10 ≤ w.val ∧ w.val < 14)},
    {w | w.val < 7 ∨ w.val = 14}], Set.univ, {w | w.val < 10}, Set.subset_univ _, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact uniformOn_univ_cond_eq_ofReal (m := 12) (n := 40) (by decide) (by decide) (by decide)
      (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 8) (n := 40) (by decide) (by decide) (by decide)
      (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 8) (n := 10) (by decide) (by decide) (by decide)
      (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 7) (n := 10) (by decide) (by decide) (by decide)
      (by norm_num)

end ModalLinda

/-! ### Modal Lawyers and Engineers (§3.3) -/

namespace ModalLawyers

/-- Modal base-rate neglect ((37)–(41)): for every measure realizing the printed conditional
probabilities and any threshold in `[0.63, 1.33)`, *Jack must be an engineer* is true and *Jack
must be a lawyer* false. No hypothesis mentions the prior on `engineer`: explanatory value
conditions only on the hypotheses, which is the neglect. -/
theorem base_rate_neglect (p : Measure W) (R : Fin 2 → Set W) (engineer lawyer : Set W)
    (h₁ : p[R 0 | engineer] = .ofReal 0.78) (h₂ : p[R 1 | engineer] = .ofReal 0.55)
    (h₃ : p[R 0 | lawyer] = .ofReal 0.35) (h₄ : p[R 1 | lawyer] = .ofReal 0.28)
    {θ : ℝ≥0∞} (hlo : .ofReal 0.63 ≤ θ) (hhi : θ < .ofReal 1.33) :
    must p R engineer {lawyer} θ ∧ ¬ must p R lawyer {engineer} θ := by
  have hE : expectedValue p R engineer = .ofReal 1.33 := by
    rw [expectedValue_eq_sum_cond, Fin.sum_univ_two, h₁, h₂, ← ENNReal.ofReal_add] <;> norm_num
  have hL : expectedValue p R lawyer = .ofReal 0.63 := by
    rw [expectedValue_eq_sum_cond, Fin.sum_univ_two, h₃, h₄, ← ENNReal.ofReal_add] <;> norm_num
  refine ⟨⟨hE ▸ hhi, ?_⟩, fun h ↦ (hL ▸ h.1).not_ge hlo⟩
  rintro ψ rfl
  exact hL ▸ hlo

/-- The printed probabilities (37)–(38) are consistent: two hypotheses of a hundred equiprobable
evidence cells each. -/
theorem exists_model :
    ∃ (p : Measure (Fin 2 × Fin 100)) (R : Fin 2 → Set (Fin 2 × Fin 100))
      (engineer lawyer : Set (Fin 2 × Fin 100)),
      Disjoint engineer lawyer ∧
      p[R 0 | engineer] = .ofReal 0.78 ∧ p[R 1 | engineer] = .ofReal 0.55 ∧
      p[R 0 | lawyer] = .ofReal 0.35 ∧ p[R 1 | lawyer] = .ofReal 0.28 := by
  refine ⟨uniformOn Set.univ,
    ![{w | (w.1 = 0 ∧ w.2.val < 78) ∨ (w.1 = 1 ∧ w.2.val < 35)},
      {w | (w.1 = 0 ∧ w.2.val < 55) ∨ (w.1 = 1 ∧ w.2.val < 28)}],
    {w | w.1 = 0}, {w | w.1 = 1}, Set.disjoint_left.2 fun w h0 h1 ↦ by simp_all, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact uniformOn_univ_cond_eq_ofReal (m := 78) (n := 100) (by decide +kernel)
      (by decide +kernel) (by decide) (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 55) (n := 100) (by decide +kernel)
      (by decide +kernel) (by decide) (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 35) (n := 100) (by decide +kernel)
      (by decide +kernel) (by decide) (by norm_num)
  · exact uniformOn_univ_cond_eq_ofReal (m := 28) (n := 100) (by decide +kernel)
      (by decide +kernel) (by decide) (by norm_num)

end ModalLawyers

end ChungMascarenhas2023
