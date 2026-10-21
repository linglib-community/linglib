module

public import Linglib.Core.Probability.Kernel.Softmax
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Tactic.DeriveFintype

/-!
# Houlihan et al. (2023): Emotion prediction as computation over a generative theory of mind

This file formalizes the inverse planning and computed appraisal modules of
[houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023] for the Split or Steal game. A `Player`
values an outcome by three Fehr–Schmidt base features, money against a reference point and the
two inequities, weighted by preferences and passed through a value function; the expected base
utility of an action under the player's belief about the opponent is (3.1)
(`Setting.expectedBaseUtility`), the softmax policy is (3.3) (`Setting.policy`), and the
observer's inverse inference (3.4) is the posterior kernel of the plan over a finite prior
(`Setting.posterior`). The public game adds the reputation utilities of (3.2), the base
weights an observer of the anonymous game would infer from the action
(`Setting.expectedPublicUtility`).

The direction of the inferences in Figure 2 follows from the covariance form of Bayes' rule:
observing cooperation raises the posterior expectation of any statistic that monovaries with
the expected-utility gap in favour of cooperating, and in Split or Steal that gap increases in
the advantageous-inequity weight and decreases in the money and disadvantageous-inequity
weights. The appraisals of Section 4, achieved utility, prediction error and the two
counterfactuals, then carry structural signs: a cooperator whose opponent stole has a negative
disadvantageous-inequity prediction error and a positive opponent counterfactual, the two
loadings of the learned envy concept, and a player who stole from a cooperator has a negative
advantageous-inequity utility that cooperating would have spared.

## Implementation notes

* The prior over preferences and beliefs is carried by a finite type of simulated players,
  as in the paper's sampled implementation; the value function `ν` is any strictly monotone
  function vanishing at zero, in place of the sign-adjusted logarithm.
* Figure 2's per-weight directions are stated for priors that vary in that weight alone,
  which is what makes the weight monovary with the utility gap; a correlated prior can reverse
  them, and the paper reports only its empirical prior.
* The lesion models of Section 5 are the constant posterior and the restriction to the money
  domain; the learned readout of Section 8 and the fitted concordances are not formalized.

## References

* [houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023]
* [fehr-schmidt-1999]
-/

@[expose] public section

namespace HoulihanEtAl2023

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The game -/

/-- Split (cooperate) or steal (defect). -/
inductive Action where
  | cooperate
  | defect
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Action := ⊤

/-- The action not chosen. -/
def Action.other : Action → Action
  | .cooperate => .defect
  | .defect => .cooperate

@[simp] theorem Action.other_cooperate : Action.other .cooperate = .defect := rfl

@[simp] theorem Action.other_defect : Action.other .defect = .cooperate := rfl

@[simp] theorem Action.other_other (a : Action) : a.other.other = a := by cases a <;> rfl

theorem sum_action {β : Type*} [AddCommMonoid β] (f : Action → β) :
    ∑ a, f a = f .cooperate + f .defect := by
  rw [show ∑ a, f a = f .cooperate + (f .defect + 0) from rfl, add_zero]

/-- Player 1 gets half the pot when both split, all of it when stealing from a splitter, and nothing
otherwise. -/
def payoff (pot : ℝ) : Action → Action → ℝ
  | .cooperate, .cooperate => pot / 2
  | .cooperate, .defect => 0
  | .defect, .cooperate => pot
  | .defect, .defect => 0

/-- Stealing weakly dominates in money. -/
theorem payoff_cooperate_le_defect {pot : ℝ} (hpot : 0 ≤ pot) (a₂ : Action) :
    payoff pot .cooperate a₂ ≤ payoff pot .defect a₂ := by
  (cases a₂ <;> simp [payoff]); linarith

/-- The three base features of an outcome are money and the two inequities of Fehr and Schmidt's
utility. -/
inductive Domain where
  | money
  | aia
  | dia
  deriving DecidableEq, Fintype

theorem sum_domain {β : Type*} [AddCommMonoid β] (f : Domain → β) :
    ∑ d, f d = f .money + f .aia + f .dia := by
  rw [show ∑ d, f d = f .money + (f .aia + (f .dia + 0)) from rfl, add_zero, add_assoc]

/-- The base feature of an outcome in a domain, money measured against the reference point
`ref`. -/
def Domain.feature (pot ref : ℝ) (a₁ a₂ : Action) : Domain → ℝ
  | .money => payoff pot a₁ a₂ - ref
  | .aia => (payoff pot a₁ a₂ - payoff pot a₂ a₁)⁺
  | .dia => (payoff pot a₂ a₁ - payoff pot a₁ a₂)⁺

/-- Money is sought and the inequities are avoided, which gives the signs of (3.1). -/
def Domain.sign : Domain → ℝ
  | .money => 1
  | .aia => -1
  | .dia => -1

/-- The reputation utilities of (3.2) carry the opposite signs, since players want to be seen as
motivated by equality rather than by money. -/
def Domain.repuSign (d : Domain) : ℝ := -d.sign

section Feature

variable {pot ref : ℝ} (hpot : 0 ≤ pot)
include hpot

theorem feature_aia_cooperate (a₂ : Action) : Domain.feature pot ref .cooperate a₂ .aia = 0 := by
  cases a₂
  · simp [Domain.feature, payoff]
  · simp [Domain.feature, payoff, posPart_eq_zero.2 (neg_nonpos.2 hpot)]

theorem feature_aia_defect_cooperate : Domain.feature pot ref .defect .cooperate .aia = pot := by
  simp [Domain.feature, payoff, posPart_eq_self.2 hpot]

theorem feature_dia_defect (a₂ : Action) : Domain.feature pot ref .defect a₂ .dia = 0 := by
  cases a₂
  · simp [Domain.feature, payoff, posPart_eq_zero.2 (neg_nonpos.2 hpot)]
  · simp [Domain.feature, payoff]

theorem feature_dia_cooperate_defect : Domain.feature pot ref .cooperate .defect .dia = pot := by
  simp [Domain.feature, payoff, posPart_eq_self.2 hpot]

omit hpot in
theorem feature_aia_defect_defect : Domain.feature pot ref .defect .defect .aia = 0 := by
  simp [Domain.feature, payoff]

omit hpot in
theorem feature_dia_cooperate_cooperate :
    Domain.feature pot ref .cooperate .cooperate .dia = 0 := by
  simp [Domain.feature, payoff]

omit hpot in
theorem feature_money (a₁ a₂ : Action) :
    Domain.feature pot ref a₁ a₂ .money = payoff pot a₁ a₂ - ref := rfl

end Feature

/-! ### Players and the forward model -/

/-- A simulated player has base preference weights, reputation weights, the belief `π_{a₂}` that the
opponent cooperates, and the reference point `π_Money`. -/
structure Player where
  base : Domain → ℝ
  repu : Domain → ℝ
  belief : ℝ
  reference : ℝ

/-- The belief as a distribution over the opponent's action. -/
def Player.beliefOn (q : Player) : Action → ℝ
  | .cooperate => q.belief
  | .defect => 1 - q.belief

/-- The player after learning the opponent's action (footnote 3). -/
def Player.knowing (q : Player) (a₂ : Action) : Player :=
  { q with belief := if a₂ = .cooperate then 1 else 0 }

/-- The fixed parameters of a game are the value function `ν`, the rationality `lam` of the softmax
(the paper's λ) and the pot. -/
structure Setting where
  ν : ℝ → ℝ
  ν_zero : ν 0 = 0
  ν_strictMono : StrictMono ν
  lam : ℝ
  lam_pos : 0 < lam
  pot : ℝ
  pot_pos : 0 < pot

namespace Setting

variable (S : Setting)

theorem ν_pot_nonneg : 0 ≤ S.ν S.pot := S.ν_zero ▸ S.ν_strictMono.monotone S.pot_pos.le

/-- The subjective utility of an outcome in one domain is the signed, weighted value of its feature,
a summand of (3.1). -/
def domainUtility (q : Player) (a₁ a₂ : Action) (d : Domain) : ℝ :=
  d.sign * q.base d * S.ν (d.feature S.pot q.reference a₁ a₂)

/-- The base utility of an outcome, summed over the domains. -/
def baseUtility (q : Player) (a₁ a₂ : Action) : ℝ := ∑ d, S.domainUtility q a₁ a₂ d

/-- The expected base utility (3.1) of an action under the belief about the opponent. -/
def expectedBaseUtility (q : Player) (a₁ : Action) : ℝ :=
  ∑ a₂, q.beliefOn a₂ * S.baseUtility q a₁ a₂

/-- In the expected-utility gap in favour of cooperating, cooperation forgoes money and risks
disadvantageous inequity, and avoids advantageous inequity. -/
theorem expectedBaseUtility_cooperate_sub_defect (q : Player) :
    S.expectedBaseUtility q .cooperate - S.expectedBaseUtility q .defect =
      q.belief * (q.base .money * (S.ν (S.pot / 2 - q.reference) - S.ν (S.pot - q.reference)) +
        q.base .aia * S.ν S.pot) - (1 - q.belief) * q.base .dia * S.ν S.pot := by
  have hpot := S.pot_pos.le
  simp only [expectedBaseUtility, baseUtility, sum_action, sum_domain, domainUtility, Domain.sign,
    Player.beliefOn, feature_money, feature_aia_cooperate hpot, feature_aia_defect_cooperate hpot,
    feature_aia_defect_defect, feature_dia_defect hpot, feature_dia_cooperate_cooperate,
    feature_dia_cooperate_defect hpot, payoff, S.ν_zero]
  ring

/-- The softmax policy (3.3) at rationality `lam` for a utility `U`. -/
def policy (U : Player → Action → ℝ) (q : Player) : Action → ℝ :=
  Real.softmax (S.lam • U q)

variable (U : Player → Action → ℝ) (q : Player)

/-- With two actions the softmax is the logistic function of the scaled utility gap. -/
theorem policy_eq_sigmoid (a : Action) :
    S.policy U q a = Real.sigmoid (S.lam * (U q a - U q a.other)) := by
  rw [policy, Real.softmax_eq_sigmoid_of_univ_eq_pair (i := a) (j := a.other)
    (by cases a <;> decide) (by cases a <;> decide)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub]

theorem policy_pos (a : Action) : 0 < S.policy U q a := Real.softmax_pos _ a

/-- A player certain that the opponent will steal cooperates at most half the time, since the gap of
(3.1) is then the disadvantageous-inequity cost of cooperating. -/
theorem policy_cooperate_le_half_of_belief_eq_zero (hb : q.belief = 0) (hd : 0 ≤ q.base .dia) :
    S.policy S.expectedBaseUtility q .cooperate ≤ 1 / 2 := by
  rw [policy_eq_sigmoid, Action.other_cooperate, one_div, ← Real.sigmoid_zero,
    Real.sigmoid_le_iff, expectedBaseUtility_cooperate_sub_defect, hb]
  nlinarith [mul_nonneg S.lam_pos.le (mul_nonneg hd S.ν_pot_nonneg)]

/-- A player certain that the opponent will split prefers to cooperate exactly when the
advantageous-inequity cost of stealing outweighs the money it gains. This is the Fehr–Schmidt
account of cooperation. -/
theorem half_le_policy_cooperate_iff (hb : q.belief = 1) :
    1 / 2 ≤ S.policy S.expectedBaseUtility q .cooperate ↔
      q.base .money * (S.ν (S.pot - q.reference) - S.ν (S.pot / 2 - q.reference)) ≤
        q.base .aia * S.ν S.pot := by
  rw [policy_eq_sigmoid, Action.other_cooperate, one_div, ← Real.sigmoid_zero,
    Real.sigmoid_le_iff, expectedBaseUtility_cooperate_sub_defect, hb,
    mul_nonneg_iff_of_pos_left S.lam_pos]
  constructor <;> intro h <;> linarith

/-! ### Inverse planning -/

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
  (p : Ω → Player)

/-- The forward model as a kernel from the prior's support to actions. -/
def plan : Kernel Ω Action :=
  Kernel.softmax fun ω a ↦ ((S.lam * U (p ω) a : ℝ) : EReal)

theorem plan_real (ω : Ω) (a : Action) : (S.plan U p ω).real {a} = S.policy U (p ω) a :=
  Kernel.softmax_coe_real_singleton _ ω a

theorem plan_apply_singleton_ne_zero (ω : Ω) (a : Action) : S.plan U p ω {a} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

instance : IsMarkovKernel (S.plan U p) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨.cooperate, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem comp_plan_ne_zero (a : Action) : (S.plan U p ∘ₘ μ) {a} ≠ 0 := by
  rw [Measure.comp_apply_singleton]
  intro h
  have hμ : ∀ ω, μ {ω} = 0 := fun ω ↦
    (mul_eq_zero.1 (Finset.sum_eq_zero_iff.1 h ω (Finset.mem_univ ω))).resolve_right
      (S.plan_apply_singleton_ne_zero U p ω a)
  have := measure_univ (μ := μ)
  rw [← Finset.coe_univ, ← sum_measure_singleton, Finset.sum_eq_zero fun ω _ ↦ hμ ω] at this
  exact zero_ne_one this

variable [Nonempty Ω]

/-- The observer's inverse inference (3.4), the posterior kernel of the plan. -/
def posterior : Kernel Action Ω := (S.plan U p)†μ

/-- The posterior expectation of a statistic of the player after observing an action. -/
def expectation (f : Player → ℝ) (a : Action) : ℝ :=
  ∫ ω, f (p ω) ∂(S.posterior U p μ a)

end Setting

/-- The prior expectation of a statistic of the player. -/
def priorExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Player)
    (f : Player → ℝ) : ℝ :=
  ∫ ω, f (p ω) ∂μ

namespace Setting

variable (S : Setting) (U : Player → Action → ℝ) {Ω : Type*} [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω] [Fintype Ω] [Nonempty Ω] (p : Ω → Player) (μ : Measure Ω)
  [IsProbabilityMeasure μ] {f : Player → ℝ}

/-- Observing cooperation raises the expectation of any statistic that monovaries with the utility
gap in favour of cooperating, since Bayes' rule reweights the prior by the policy, which is
increasing in the gap. -/
theorem priorExpectation_le_expectation_cooperate
    (hf : Monovary (f ∘ p) fun ω ↦ U (p ω) .cooperate - U (p ω) .defect) :
    priorExpectation μ p f ≤ S.expectation U p μ f .cooperate := by
  refine integral_le_integral_posterior _ μ (S.comp_plan_ne_zero U p μ _) ?_
  intro i j hij
  simp only [plan_real, policy_eq_sigmoid, Action.other_cooperate] at hij
  exact hf ((mul_lt_mul_iff_of_pos_left S.lam_pos).1 (Real.sigmoid_lt_iff.1 hij))

/-- Observing defection lowers it. -/
theorem expectation_defect_le_priorExpectation
    (hf : Monovary (f ∘ p) fun ω ↦ U (p ω) .cooperate - U (p ω) .defect) :
    S.expectation U p μ f .defect ≤ priorExpectation μ p f := by
  refine integral_posterior_le_integral _ μ (S.comp_plan_ne_zero U p μ _) ?_
  intro i j hij
  simp only [plan_real, policy_eq_sigmoid, Action.other_defect] at hij
  have h := (mul_lt_mul_iff_of_pos_left S.lam_pos).1 (Real.sigmoid_lt_iff.1 hij)
  exact hf (by linarith)

theorem expectation_defect_le_expectation_cooperate
    (hf : Monovary (f ∘ p) fun ω ↦ U (p ω) .cooperate - U (p ω) .defect) :
    S.expectation U p μ f .defect ≤ S.expectation U p μ f .cooperate :=
  (S.expectation_defect_le_priorExpectation U p μ hf).trans
    (S.priorExpectation_le_expectation_cooperate U p μ hf)

/-- A prior that varies only in the weight of one domain. -/
def VariesOnly (d : Domain) : Prop :=
  ∀ ω ω', (∀ d', d' ≠ d → (p ω).base d' = (p ω').base d') ∧ (p ω).belief = (p ω').belief ∧
    (p ω).reference = (p ω').reference

/-- A cooperator is inferred to be more averse to advantageous inequity (Figure 2). -/
theorem expectation_aia_defect_le_cooperate (h : VariesOnly p .aia) (hb : ∀ ω, 0 ≤ (p ω).belief) :
    S.expectation S.expectedBaseUtility p μ (·.base .aia) .defect ≤
      S.expectation S.expectedBaseUtility p μ (·.base .aia) .cooperate := by
  refine S.expectation_defect_le_expectation_cooperate _ p μ fun i j hij ↦ ?_
  obtain ⟨hd, hb', hr⟩ := h i j
  have hm := hd .money (by decide)
  have hd' := hd .dia (by decide)
  simp only [expectedBaseUtility_cooperate_sub_defect, hm, hd', hb', hr] at hij
  show (p i).base .aia ≤ (p j).base .aia
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left hlt.le (mul_nonneg (hb j) S.ν_pot_nonneg)]

/-- A cooperator is inferred to be less motivated by money (Figure 2). -/
theorem expectation_money_cooperate_le_defect (h : VariesOnly p .money)
    (hb : ∀ ω, 0 ≤ (p ω).belief) :
    S.expectation S.expectedBaseUtility p μ (·.base .money) .cooperate ≤
      S.expectation S.expectedBaseUtility p μ (·.base .money) .defect := by
  have := S.expectation_defect_le_expectation_cooperate S.expectedBaseUtility p μ
    (f := fun q ↦ -q.base .money) fun i j hij ↦ ?_
  · simpa only [expectation, integral_neg, neg_le_neg_iff] using this
  obtain ⟨hd, hb', hr⟩ := h i j
  have ha := hd .aia (by decide)
  have hd' := hd .dia (by decide)
  simp only [expectedBaseUtility_cooperate_sub_defect, ha, hd', hb', hr] at hij
  have hν : S.ν (S.pot / 2 - (p j).reference) ≤ S.ν (S.pot - (p j).reference) :=
    S.ν_strictMono.monotone (by linarith [S.pot_pos])
  show -(p i).base .money ≤ -(p j).base .money
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left (neg_lt_neg_iff.1 hlt).le
    (mul_nonneg (hb j) (sub_nonneg.2 hν))]

/-- A cooperator is inferred to be less averse to disadvantageous inequity (Figure 2). -/
theorem expectation_dia_cooperate_le_defect (h : VariesOnly p .dia)
    (hb : ∀ ω, (p ω).belief ≤ 1) :
    S.expectation S.expectedBaseUtility p μ (·.base .dia) .cooperate ≤
      S.expectation S.expectedBaseUtility p μ (·.base .dia) .defect := by
  have := S.expectation_defect_le_expectation_cooperate S.expectedBaseUtility p μ
    (f := fun q ↦ -q.base .dia) fun i j hij ↦ ?_
  · simpa only [expectation, integral_neg, neg_le_neg_iff] using this
  obtain ⟨hd, hb', hr⟩ := h i j
  have hm := hd .money (by decide)
  have ha := hd .aia (by decide)
  simp only [expectedBaseUtility_cooperate_sub_defect, hm, ha, hb', hr] at hij
  show -(p i).base .dia ≤ -(p j).base .dia
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left (neg_lt_neg_iff.1 hlt).le
    (mul_nonneg (sub_nonneg.2 (hb j)) S.ν_pot_nonneg)]

/-! ### The public game -/

/-- The expected reputation in a domain is the base weight an observer of the anonymous game would
infer from the action. -/
def reputation (d : Domain) (a₁ : Action) : ℝ :=
  S.expectation S.expectedBaseUtility p μ (·.base d) a₁

/-- The expected utility (3.2) of an action in the public game, the base utility plus the reputation
utilities, each the value of the inferred base weight scaled by the pot. -/
def expectedPublicUtility (q : Player) (a₁ : Action) : ℝ :=
  S.expectedBaseUtility q a₁ +
    ∑ d, d.repuSign * q.repu d * S.ν (S.reputation p μ d a₁ * S.pot)

/-- A player whose reputation concern is to be seen as averse to advantageous inequity
cooperates at least as often in public as in private, since cooperating is inferred to
reflect more of that aversion. -/
theorem policy_cooperate_le_policy_public (q : Player) (hm : q.repu .money = 0)
    (hd : q.repu .dia = 0) (ha : 0 ≤ q.repu .aia)
    (hrep : S.reputation p μ .aia .defect ≤ S.reputation p μ .aia .cooperate) :
    S.policy S.expectedBaseUtility q .cooperate ≤
      S.policy (S.expectedPublicUtility p μ) q .cooperate := by
  rw [policy_eq_sigmoid, policy_eq_sigmoid, Real.sigmoid_le_iff,
    mul_le_mul_iff_of_pos_left S.lam_pos, Action.other_cooperate]
  simp only [expectedPublicUtility, sum_domain, Domain.repuSign, Domain.sign, hm, hd]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg ha (sub_nonneg.2 this)]

/-- A player whose reputation concern is to be seen as averse to disadvantageous inequity
cooperates at most as often in public, since stealing is inferred to reflect more of it. -/
theorem policy_public_le_policy_cooperate (q : Player) (hm : q.repu .money = 0)
    (ha : q.repu .aia = 0) (hd : 0 ≤ q.repu .dia)
    (hrep : S.reputation p μ .dia .cooperate ≤ S.reputation p μ .dia .defect) :
    S.policy (S.expectedPublicUtility p μ) q .cooperate ≤
      S.policy S.expectedBaseUtility q .cooperate := by
  rw [policy_eq_sigmoid, policy_eq_sigmoid, Real.sigmoid_le_iff,
    mul_le_mul_iff_of_pos_left S.lam_pos, Action.other_cooperate]
  simp only [expectedPublicUtility, sum_domain, Domain.repuSign, Domain.sign, hm, ha]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg hd (sub_nonneg.2 this)]

/-- The inverse inference (3.4) for the public game, over the six weights and the belief. -/
def publicPosterior : Kernel Action Ω :=
  S.posterior (S.expectedPublicUtility p μ) p μ

/-! ### Computed appraisals (Section 4) -/

variable (q : Player)

/-- The expected utility of an action in a domain during planning. -/
def expectedDomainUtility (a₁ : Action) (d : Domain) : ℝ :=
  ∑ a₂, q.beliefOn a₂ * S.domainUtility q a₁ a₂ d

theorem expectedBaseUtility_eq_sum (a₁ : Action) :
    S.expectedBaseUtility q a₁ = ∑ d, S.expectedDomainUtility q a₁ d := by
  simp only [expectedBaseUtility, baseUtility, expectedDomainUtility, Finset.mul_sum]
  exact Finset.sum_comm

/-- The prediction error is the achieved utility of the outcome less the utility expected during
planning. -/
def predictionError (a₁ a₂ : Action) (d : Domain) : ℝ :=
  S.domainUtility q a₁ a₂ d - S.expectedDomainUtility q a₁ d

/-- The opponent counterfactual `CFa₂` is the utility the opponent's other choice would have
brought, weighted by the belief that the opponent would make it. -/
def opponentCounterfactual (a₁ a₂ : Action) (d : Domain) : ℝ :=
  q.beliefOn a₂.other * (S.domainUtility q a₁ a₂.other d - S.domainUtility q a₁ a₂ d)

/-- The agent counterfactual `CFa₁` is the utility the player's other choice would have brought,
weighted by the probability of that choice under the policy of the player who knows the opponent's
action (footnote 3). -/
def agentCounterfactual (U : Player → Action → ℝ) (a₁ a₂ : Action) (d : Domain) :
    ℝ :=
  S.policy U (q.knowing a₂) a₁.other *
    (S.domainUtility q a₁.other a₂ d - S.domainUtility q a₁ a₂ d)

/-- The absolute prediction error of the opponent's action, `|PE_{π_{a₂}}|`. -/
def beliefError (a₂ : Action) : ℝ := |1 - q.beliefOn a₂|

/-- A cooperator whose opponent stole is in a more disadvantageous position than expected, the first
loading of envy (Figure 5b). -/
theorem predictionError_dia_cooperate_defect_nonpos (hd : 0 ≤ q.base .dia)
    (hb : 0 ≤ q.belief) : S.predictionError q .cooperate .defect .dia ≤ 0 := by
  have hpot := S.pot_pos.le
  simp only [predictionError, expectedDomainUtility, sum_action, domainUtility, Domain.sign,
    Player.beliefOn, feature_dia_cooperate_cooperate, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg hb (mul_nonneg hd S.ν_pot_nonneg)]

/-- Had the opponent split, the cooperator would have been in a less disadvantageous position, the
second loading of envy (Figure 5b). -/
theorem opponentCounterfactual_dia_cooperate_defect_nonneg (hd : 0 ≤ q.base .dia)
    (hb : 0 ≤ q.belief) : 0 ≤ S.opponentCounterfactual q .cooperate .defect .dia := by
  have hpot := S.pot_pos.le
  simp only [opponentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    Player.beliefOn, feature_dia_cooperate_cooperate, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg hb (mul_nonneg hd S.ν_pot_nonneg)]

/-- Stealing from a splitter costs advantageous-inequity utility, a structural condition of guilt.
-/
theorem domainUtility_aia_defect_cooperate_nonpos (ha : 0 ≤ q.base .aia) :
    S.domainUtility q .defect .cooperate .aia ≤ 0 := by
  simp only [domainUtility, Domain.sign, feature_aia_defect_cooperate S.pot_pos.le]
  nlinarith [S.ν_pot_nonneg]

/-- Splitting would have spared that cost, the other structural condition of guilt. -/
theorem agentCounterfactual_aia_defect_cooperate_nonneg (U : Player → Action → ℝ)
    (ha : 0 ≤ q.base .aia) : 0 ≤ S.agentCounterfactual q U .defect .cooperate .aia := by
  have hpot := S.pot_pos.le
  simp only [agentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    feature_aia_cooperate hpot, feature_aia_defect_cooperate hpot, S.ν_zero]
  nlinarith [mul_nonneg (S.policy_pos U (q.knowing .cooperate) .cooperate).le
    (mul_nonneg ha S.ν_pot_nonneg)]

/-- Had the opponent stolen from a splitter, the money would have been worse, the structural
condition of gratitude. -/
theorem opponentCounterfactual_money_cooperate_cooperate_nonpos (hm : 0 ≤ q.base .money)
    (hb : q.belief ≤ 1) : S.opponentCounterfactual q .cooperate .cooperate .money ≤ 0 := by
  simp only [opponentCounterfactual, Action.other_cooperate, domainUtility, Domain.sign,
    Player.beliefOn, feature_money, payoff, one_mul]
  have := S.ν_strictMono.monotone (show 0 - q.reference ≤ S.pot / 2 - q.reference by
    linarith [S.pot_pos])
  nlinarith [mul_nonneg (sub_nonneg.2 hb) (mul_nonneg hm (sub_nonneg.2 this))]

/-- When both steal, a defector who had split would have been left with nothing against a full pot.
The base agent counterfactual is then relief rather than regret in the disadvantageous domain, so
regret after mutual stealing must come from reputation. -/
theorem agentCounterfactual_dia_defect_defect_nonpos (U : Player → Action → ℝ)
    (hd : 0 ≤ q.base .dia) : S.agentCounterfactual q U .defect .defect .dia ≤ 0 := by
  have hpot := S.pot_pos.le
  simp only [agentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    feature_dia_defect hpot, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg (S.policy_pos U (q.knowing .defect) .cooperate).le
    (mul_nonneg hd S.ν_pot_nonneg)]

/-- The reputation utility of an action in a domain, the summands of (3.2). -/
def reputationUtility (a₁ : Action) (d : Domain) : ℝ :=
  d.repuSign * q.repu d * S.ν (S.reputation p μ d a₁ * S.pot)

/-- The agent counterfactual over reputation. -/
def reputationAgentCounterfactual (U : Player → Action → ℝ) (a₁ a₂ : Action)
    (d : Domain) : ℝ :=
  S.policy U (q.knowing a₂) a₁.other *
    (S.reputationUtility p μ q a₁.other d - S.reputationUtility p μ q a₁ d)

/-- Whatever the opponent did, a defector who cares to be seen as averse to advantageous inequity
would have been seen as more so had they split, which grounds regret and guilt over reputation. -/
theorem reputationAgentCounterfactual_aia_defect_nonneg (U : Player → Action → ℝ)
    (ha : 0 ≤ q.repu .aia)
    (hrep : S.reputation p μ .aia .defect ≤ S.reputation p μ .aia .cooperate) (a₂ : Action) :
    0 ≤ S.reputationAgentCounterfactual p μ q U .defect a₂ .aia := by
  simp only [reputationAgentCounterfactual, Action.other_defect, reputationUtility,
    Domain.repuSign, Domain.sign]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg (S.policy_pos U (q.knowing a₂) .cooperate).le
    (mul_nonneg ha (sub_nonneg.2 this))]

/-! ### Lesions (Section 5) -/

/-- The social lesion keeps only the money appraisals; a reader of monetary achieved utility
then ranks stealing from a splitter above splitting with one, whereas observers predict
similar joy for both. -/
theorem domainUtility_money_cooperate_lt_defect (hm : 0 < q.base .money) :
    S.domainUtility q .cooperate .cooperate .money <
      S.domainUtility q .defect .cooperate .money := by
  simp only [domainUtility, Domain.sign, feature_money, payoff, one_mul]
  exact mul_lt_mul_of_pos_left (S.ν_strictMono (by linarith [S.pot_pos])) hm

end Setting

/-- The inverse planning lesion replaces the posterior of (3.4) by the prior, so that the inferred
preferences and beliefs no longer depend on the action. -/
def lesionedPosterior {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    Kernel Action Ω :=
  Kernel.const Action μ

theorem lesionedPosterior_expectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Ω → Player) (f : Player → ℝ) (a : Action) :
    ∫ ω, f (p ω) ∂(lesionedPosterior μ a) = priorExpectation μ p f := by
  simp [lesionedPosterior, priorExpectation]

end

end HoulihanEtAl2023
