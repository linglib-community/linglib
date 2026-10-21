module

public import Linglib.Core.Probability.GibbsVariational
public import Linglib.Semantics.Questions.Value
public import Studies.DongEtAl2026
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Tsvilodub, Mulligan, Snider, Hawkins and Franke (2026): Act or Clarify? Modeling Sensitivity to Uncertainty and Cost in Communication

The computational model of Experiment 1 explains when an agent asks a clarification question
rather than answering under uncertainty. The questioner has one of two goals, with probability `ε`
on the dispreferred one; a mention-some answer is worth 1 for its goal and 0 for the other, and the
exhaustive answer is worth `1 − δ` for either. The agent clarifies with a probability that is a
logistic function of the expected regret of its best action, which is the value of learning the
goal and van Rooy's value of the clarification question, `min ε δ`, and otherwise answers by a
softmax policy over expected utility. Uncertainty therefore matters only while it stays below the
cost of the exhaustive answer. With `c` read as the cost of asking, as the paper suggests, the gate
softens the clarify-or-commit rule of Dong et al.

## Main statements

* `valueOfInformation_id_eq_expectedRegret`: the expected regret of a best action is the value of
  perfect information.
* `uncertainty_matters_most_when_costly`: uncertainty raises clarification when the exhaustive
  answer is costly and leaves it unchanged when it is cheap.
* `justListThemAll`: with a cheap exhaustive answer, higher uncertainty means more exhaustive
  answers.
* `half_lt_clarifyProb_iff`: the gate favours clarifying exactly when Dong et al.'s agent would.

## Implementation notes

* The gate reads the expected regret of the best action in its value form, the value of
  information of observing the goal, which needs no choice of a maximizer. The paper prints
  `arg max` in the regret where the maximum is meant.
* `ε` is a point of the unit interval and the prior is a Bernoulli measure; the paper's clamp
  `ε ≤ 1/2` is a hypothesis. The softmax policy is the counting measure tilted by `α · EU`; the
  model has no listener.
* The fitted posterior means of Experiment 1 (ε of 0.17 and 0.49, δ of 0.11 and 0.32, τ of 3.60,
  c of 0.18) enter only through the orderings δ_S < ε_L < δ_L < ε_H ≤ 1/2. TooManyToList is not
  entailed: with a costly exhaustive answer, higher uncertainty raises both the gate and the
  policy's mass on the exhaustive answer, which pull the reaction's mass on it in opposite
  directions.
* Experiment 2, which the paper does not model, and the fit and model comparison are not
  formalized.

## References

* [tsvilodub-etal-2026]
* [raiffa-schlaifer-1961]
* [dong-etal-2026]
* [van-rooy-2003]
-/

@[expose] public section

namespace TsvilodubEtAl2026

open MeasureTheory ProbabilityTheory Real
open scoped unitInterval

/-! ### Regret -/

section Regret

variable {W A : Type*} [MeasurableSpace W] (U : W → A → ℝ) (μ : Measure W)

/-- The regret of action `a` at world `w` is what the best action at `w` earns over `a`. -/
noncomputable def regret (w : W) (a : A) : ℝ := (⨆ b, U w b) - U w a

/-- The expected regret of action `a` averages its regret over the belief. -/
noncomputable def expectedRegret (a : A) : ℝ := ∫ w, regret U w a ∂μ

variable {U μ} [Finite W] [MeasurableSingletonClass W] [StandardBorelSpace W] [Nonempty W]
  [IsFiniteMeasure μ]

/-- The expected regret of a best action is the value of observing the world, the expected value
of perfect information. -/
theorem valueOfInformation_id_eq_expectedRegret {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    valueOfInformation (decisionValue U) Kernel.id μ = expectedRegret U μ a := by
  rw [valueOfInformation_id, expectedRegret, ← ha, ← integral_sub .of_finite .of_finite]
  simp only [decisionValue_dirac, regret]

end Regret

/-! ### The decision problem -/

/-- The questioner's goal. -/
inductive Goal where
  | g₁
  | g₂
  deriving DecidableEq, Repr, Fintype, Nonempty

instance : MeasurableSpace Goal := ⊤
instance : DiscreteMeasurableSpace Goal := ⟨fun _ ↦ trivial⟩

/-- A direct answer is one of the two mention-some answers or the exhaustive answer. -/
inductive Response where
  | ms1
  | ms2
  | exh
  deriving DecidableEq, Repr, Fintype, Nonempty

instance : MeasurableSpace Response := ⊤
instance : DiscreteMeasurableSpace Response := ⟨fun _ ↦ trivial⟩

/-- The utilities at exhaustive-answer cost `δ`. -/
def utility (δ : ℝ) : Goal → Response → ℝ
  | .g₁, .ms1 => 1
  | .g₁, .ms2 => 0
  | .g₂, .ms1 => 0
  | .g₂, .ms2 => 1
  | _, .exh => 1 - δ

/-- The prior at uncertainty `ε` puts probability `ε` on the dispreferred goal. -/
noncomputable def prior (ε : I) : Measure Goal := bernoulliMeasure .g₂ .g₁ ε

instance (ε : I) : IsProbabilityMeasure (prior ε) :=
  inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure _ _ _))

/-- The expected utility of an answer in the condition `(ε, δ)`. -/
noncomputable def expectedUtility (ε : I) (δ : ℝ) (r : Response) : ℝ :=
  ∫ g, utility δ g r ∂prior ε

variable {ε εL εH : I} {δ δS δL : ℝ}

@[simp] theorem expectedUtility_ms1 : expectedUtility ε δ .ms1 = 1 - ε := by
  simp [expectedUtility, prior, integral_bernoulliMeasure, utility]

@[simp] theorem expectedUtility_ms2 : expectedUtility ε δ .ms2 = ε := by
  simp [expectedUtility, prior, integral_bernoulliMeasure, utility]

@[simp] theorem expectedUtility_exh : expectedUtility ε δ .exh = 1 - δ := by
  simp [expectedUtility, prior, utility]

private theorem sum_response {β : Type*} [AddCommMonoid β] (f : Response → β) :
    ∑ r, f r = f .ms1 + f .ms2 + f .exh := by
  rw [show ∑ r, f r = f .ms1 + (f .ms2 + (f .exh + 0)) from rfl, add_zero, add_assoc]

theorem decisionValue_utility (hε : (ε : ℝ) ≤ 1 / 2) :
    decisionValue (utility δ) (prior ε) = 1 - min (ε : ℝ) δ := by
  have hb : BddAbove (Set.range (expectedUtility ε δ)) := (Set.finite_range _).bddAbove
  refine le_antisymm (ciSup_le fun r ↦ ?_) ?_
  · change expectedUtility ε δ r ≤ _
    cases r <;> simp <;> linarith [min_le_left (ε : ℝ) δ, min_le_right (ε : ℝ) δ]
  · rcases min_cases (ε : ℝ) δ with ⟨h, _⟩ | ⟨h, _⟩
    · exact le_ciSup_of_le hb .ms1 (by change _ ≤ expectedUtility ε δ _; simp [h])
    · exact le_ciSup_of_le hb .exh (by change _ ≤ expectedUtility ε δ _; simp [h])

theorem valueOfInformation_id_utility (hε : (ε : ℝ) ≤ 1 / 2) (hδ : 0 ≤ δ) :
    valueOfInformation (decisionValue (utility δ)) Kernel.id (prior ε) = min (ε : ℝ) δ := by
  have hbest (g : Goal) : ⨆ r, utility δ g r = 1 := by
    refine le_antisymm (ciSup_le fun r ↦ ?_) ?_
    · cases g <;> cases r <;> simp [utility] <;> linarith
    · cases g
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove .ms1 (by simp [utility])
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove .ms2 (by simp [utility])
  rw [valueOfInformation_id, decisionValue_utility hε]
  simp [hbest]

/-- The clarification question asks which goal the questioner has, the finest question about the
goal, so its value as a question in the sense of [van-rooy-2003] is `min ε δ`. -/
theorem questionUtility_bot (hε : (ε : ℝ) ≤ 1 / 2) (hδ : 0 ≤ δ) :
    Question.utility (utility δ) (prior ε) ⊥ = min (ε : ℝ) δ := by
  rw [Question.utility_bot, valueOfInformation_id_utility hε hδ]

/-! ### The clarification gate -/

/-- The probability of clarifying is the logistic function, with slope `τ` and threshold `c`, of
the value of learning the goal. -/
noncomputable def clarifyProb (τ c : ℝ) (ε : I) (δ : ℝ) : I :=
  unitInterval.sigmoid
    (τ * (valueOfInformation (decisionValue (utility δ)) Kernel.id (prior ε) - c))

theorem coe_clarifyProb (τ c : ℝ) (hε : (ε : ℝ) ≤ 1 / 2) (hδ : 0 ≤ δ) :
    (clarifyProb τ c ε δ : ℝ) = sigmoid (τ * (min (ε : ℝ) δ - c)) := by
  rw [clarifyProb, unitInterval.sigmoid, Subtype.coind_coe, valueOfInformation_id_utility hε hδ]

/-- With a costly exhaustive answer, higher uncertainty means more clarification, the paper's
TL;JustAsk. -/
theorem tl_justAsk {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (hδ : 0 ≤ δ) (hε : εL < εH)
    (hH : (εH : ℝ) ≤ 1 / 2) (hL : (εL : ℝ) < δ) : clarifyProb τ c εL δ < clarifyProb τ c εH δ := by
  have hLH : (εL : ℝ) < εH := hε
  change (clarifyProb τ c εL δ : ℝ) < clarifyProb τ c εH δ
  rw [coe_clarifyProb τ c (hLH.le.trans hH) hδ, coe_clarifyProb τ c hH hδ, min_eq_left hL.le]
  exact sigmoid_lt (mul_lt_mul_of_pos_left (by linarith [lt_min hLH hL]) hτ)

/-- With an exhaustive answer cheaper than either uncertainty, uncertainty makes no difference to
clarification, the paper's NoNeedToAsk. -/
theorem noNeedToAsk (τ c : ℝ) (hδ : 0 ≤ δ) (hL : δ ≤ εL) (hH : δ ≤ εH)
    (hεL : (εL : ℝ) ≤ 1 / 2) (hεH : (εH : ℝ) ≤ 1 / 2) :
    clarifyProb τ c εL δ = clarifyProb τ c εH δ :=
  Subtype.ext <| by
    rw [coe_clarifyProb τ c hεL hδ, coe_clarifyProb τ c hεH hδ, min_eq_right hL, min_eq_right hH]

/-- Once uncertainty exceeds the smaller cost, a costlier exhaustive answer means more
clarification, the main effect of option-space size on clarification in Experiment 1. -/
theorem clarification_rises_with_cost {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (hε : (ε : ℝ) ≤ 1 / 2)
    (hS : 0 ≤ δS) (hεS : δS < ε) (hδ : δS < δL) :
    clarifyProb τ c ε δS < clarifyProb τ c ε δL := by
  change (clarifyProb τ c ε δS : ℝ) < clarifyProb τ c ε δL
  rw [coe_clarifyProb τ c hε hS, coe_clarifyProb τ c hε (hS.trans hδ.le), min_eq_right hεS.le]
  exact sigmoid_lt (mul_lt_mul_of_pos_left (by linarith [lt_min hεS hδ]) hτ)

/-- Uncertainty raises clarification when the exhaustive answer is costly and leaves it unchanged
when it is cheap, the interaction the paper tests. -/
theorem uncertainty_matters_most_when_costly {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (hS : 0 ≤ δS)
    (hSL : δS ≤ εL) (hε : εL < εH) (hH : (εH : ℝ) ≤ 1 / 2) (hL : (εL : ℝ) < δL) :
    clarifyProb τ c εL δS = clarifyProb τ c εH δS ∧
      clarifyProb τ c εL δL < clarifyProb τ c εH δL := by
  have hLH : (εL : ℝ) < εH := hε
  exact ⟨noNeedToAsk τ c hS hSL (hSL.trans hLH.le) (hLH.le.trans hH) hH,
    tl_justAsk hτ c (hS.trans (hSL.trans hL.le)) hε hH hL⟩

/-- Without cost or without uncertainty, the ablated models of the model comparison, the gate is
the same in every condition. -/
theorem clarifyProb_of_ablated (τ c : ℝ) (hε : (ε : ℝ) ≤ 1 / 2) (hδ : 0 ≤ δ)
    (h : (ε : ℝ) = 0 ∨ δ = 0) : (clarifyProb τ c ε δ : ℝ) = sigmoid (τ * (0 - c)) := by
  rw [coe_clarifyProb τ c hε hδ]
  rcases h with h | h <;> simp [h, ε.2.1, hδ]

/-! ### The behavioral policy -/

/-- The behavioral policy at the condition `(ε, δ)` is the softmax of `α · EU`. -/
noncomputable def policy (α : ℝ) (ε : I) (δ : ℝ) : Measure Response :=
  Measure.count.tilted fun r ↦ α * expectedUtility ε δ r

instance (α : ℝ) (ε : I) (δ : ℝ) : IsProbabilityMeasure (policy α ε δ) :=
  isProbabilityMeasure_tilted .of_finite

theorem policy_real_singleton (α : ℝ) (ε : I) (δ : ℝ) (r : Response) :
    (policy α ε δ).real {r} = softmax (fun r ↦ α * expectedUtility ε δ r) r :=
  count_tilted_real_singleton _ r

theorem policy_real_lt_iff {α : ℝ} (hα : 0 < α) {r r' : Response} :
    (policy α ε δ).real {r} < (policy α ε δ).real {r'} ↔
      expectedUtility ε δ r < expectedUtility ε δ r' := by
  rw [policy_real_singleton, policy_real_singleton, softmax_lt_softmax_iff,
    mul_lt_mul_iff_of_pos_left hα]

theorem policy_real_exh_lt {α : ℝ} (hα : 0 < α) (hε : εL < εH) (hH : (εH : ℝ) ≤ 1 / 2) :
    (policy α εL δ).real {.exh} < (policy α εH δ).real {.exh} := by
  have hLH : (εL : ℝ) < εH := hε
  have h₁ : exp (α * εL) < exp (α * (1 - εH)) := exp_lt_exp.2 (by nlinarith)
  have h₂ : 1 < exp (α * (εH - εL)) := one_lt_exp_iff.2 (by nlinarith)
  have e₁ : exp (α * εH) = exp (α * εL) * exp (α * (εH - εL)) := by rw [← exp_add]; ring_nf
  have e₂ : exp (α * (1 - εL)) = exp (α * (1 - εH)) * exp (α * (εH - εL)) := by
    rw [← exp_add]; ring_nf
  simp only [policy_real_singleton, softmax_apply, sum_response, expectedUtility_ms1,
    expectedUtility_ms2, expectedUtility_exh]
  refine div_lt_div_of_pos_left (exp_pos _) (by positivity) ?_
  rw [e₁, e₂]
  nlinarith [mul_pos (sub_pos.2 h₁) (sub_pos.2 h₂)]

/-! ### The layered reaction -/

/-- A reaction either clarifies or commits to a direct answer. -/
inductive Reaction where
  | clarify
  | act (r : Response)
  deriving DecidableEq, Repr

instance : MeasurableSpace Reaction := ⊤
instance : DiscreteMeasurableSpace Reaction := ⟨fun _ ↦ trivial⟩

/-- The reaction clarifies with the gate's probability and otherwise acts by the policy. -/
noncomputable def reaction (τ c α : ℝ) (ε : I) (δ : ℝ) : Measure Reaction :=
  unitInterval.toNNReal (clarifyProb τ c ε δ) • Measure.dirac .clarify +
    unitInterval.toNNReal (σ (clarifyProb τ c ε δ)) • (policy α ε δ).map .act

theorem reaction_real_clarify (τ c α : ℝ) (ε : I) (δ : ℝ) :
    (reaction τ c α ε δ).real {.clarify} = clarifyProb τ c ε δ := by
  have : Reaction.act ⁻¹' {.clarify} = ∅ := by ext; simp
  simp [reaction, measureReal_def, Measure.map_apply .of_discrete (.singleton _), this]

theorem reaction_real_act (τ c α : ℝ) (ε : I) (δ : ℝ) (r : Response) :
    (reaction τ c α ε δ).real {.act r} = (1 - clarifyProb τ c ε δ) * (policy α ε δ).real {r} := by
  have : Reaction.act ⁻¹' {.act r} = {r} := by ext; simp
  simp [reaction, measureReal_def, Measure.map_apply .of_discrete (.singleton _), this]

/-- With an exhaustive answer cheaper than either uncertainty, higher uncertainty means more
exhaustive answers, the paper's JustListThemAll. -/
theorem justListThemAll (τ c : ℝ) {α : ℝ} (hα : 0 < α) (hS : 0 ≤ δS) (hSL : δS ≤ εL)
    (hε : εL < εH) (hH : (εH : ℝ) ≤ 1 / 2) :
    (reaction τ c α εL δS).real {.act .exh} < (reaction τ c α εH δS).real {.act .exh} := by
  have hLH : (εL : ℝ) < εH := hε
  rw [reaction_real_act, reaction_real_act,
    noNeedToAsk τ c hS hSL (hSL.trans hLH.le) (hLH.le.trans hH) hH]
  exact mul_lt_mul_of_pos_left (policy_real_exh_lt hα hε hH)
    (sub_pos.2 (unitInterval.sigmoid_lt_one _))

/-! ### The gate as a softened clarify-or-commit rule -/

/-- The clarification question reveals the goal, so as a question of [dong-etal-2026] it is the
identity kernel, and the gate exceeds one half exactly when their agent, with asking cost `c`,
clarifies. -/
theorem half_lt_clarifyProb_iff {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (ε : I) (δ : ℝ) :
    1 / 2 < (clarifyProb τ c ε δ : ℝ) ↔
      DongEtAl2026.Clarifies (utility δ) (prior ε) (fun _ : Unit ↦ Kernel.id) c {()} := by
  rw [clarifyProb, unitInterval.sigmoid, Subtype.coind_coe, one_div, ← sigmoid_zero,
    sigmoid_lt_iff, mul_pos_iff_of_pos_left hτ]
  exact ⟨fun h ↦ ⟨(), Finset.mem_singleton_self _, h⟩, fun ⟨_, _, h⟩ ↦ h⟩

end TsvilodubEtAl2026
