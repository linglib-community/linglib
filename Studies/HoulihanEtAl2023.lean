module

public import Linglib.Core.Probability.Kernel.Softmax
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Topology.UnitInterval
public import Linglib.Pragmatics.Agent.InversePlanning

/-!
# Houlihan et al. (2023): Emotion prediction as computation over a generative theory of mind

A *player* of Split or Steal has a weight in the unit interval for each of three features of an
outcome, the money won against a reference point, the advantageous inequity and the
disadvantageous inequity, a second weight for the reputation each feature earns, a belief that
the opponent cooperates, and the reference point. The base utility of an outcome is the signed
sum of the weighted values `ν` of its features (`Setting.baseUtility`).

A player is an agent whose state is the opponent's action (`Setting.agent`): the value of an
action is its expected base utility under the player's belief (`Setting.value_agent`), and the
player takes the action with the probability the agent's policy gives it at rationality `lam`
(`Setting.policy`). In the public game the utility of an action adds, for each feature, the
reputation weight times the value of the base weight an observer of the anonymous game would
infer from the action (`Setting.publicAgent`, `Setting.value_publicAgent`).

An observer with a prior over a population of players infers a player's weights and belief from
its action by the posterior of the forward model (`Setting.posterior`). Seeing cooperation raises
the expectation of every statistic that monovaries with the value advantage of cooperating
(`Setting.priorExpectation_le_expectation_cooperate`). In a population that varies in one weight
alone, that advantage increases in the advantageous-inequity weight and decreases in the money
and disadvantageous-inequity weights, which gives the direction of each inference
(`Setting.expectation_aia_defect_le_cooperate`, `Setting.expectation_money_cooperate_le_defect`,
`Setting.expectation_dia_cooperate_le_defect`). Cooperating therefore earns the higher
reputation for aversion to advantageous inequity in such a population, so a player who cares only
for that reputation cooperates at least as often in public
(`Setting.policy_cooperate_le_policy_public_of_variesOnly`); such populations exist
(`Setting.variesOnly_update`).

The appraisals of an outcome are computed from the player's weights and belief: the utility
achieved in a feature (`Setting.domainUtility`), its prediction error against the utility
expected during planning (`Setting.predictionError`), the opponent counterfactual, weighted by
the belief that the opponent would have chosen otherwise (`Setting.opponentCounterfactual`), and
the agent counterfactual, weighted by the probability that the player would have chosen
otherwise knowing the opponent's action (`Setting.agentCounterfactual`). A cooperator whose
opponent stole has a nonpositive prediction error and a nonnegative opponent counterfactual in
disadvantageous inequity (`Setting.predictionError_dia_cooperate_defect_nonpos`,
`Setting.opponentCounterfactual_dia_cooperate_defect_nonneg`), and a player who stole from a
cooperator has a nonnegative agent counterfactual in advantageous inequity
(`Setting.agentCounterfactual_aia_defect_cooperate_nonneg`).

## Implementation notes

* The prior over preferences and beliefs is carried by a finite type of simulated players,
  as in the paper's sampled implementation; the value function `ν` is any strictly monotone
  function vanishing at zero, in place of the sign-adjusted logarithm.
* The weights and the belief are points of the unit interval and the reference point is
  nonnegative, the ranges the paper gives them.
* The per-weight directions of inference are stated for priors that vary in that weight alone,
  which is what makes the weight monovary with the value advantage; a correlated prior can
  reverse them, and the paper reports only its empirical prior.
* The appraisals follow the paper's description of them in prose.
* The reputation of an action is the base weight inferred from it in the anonymous game; the
  paper says only that it is what a rational observer would infer.
* The learned readout of emotions and the fitted concordances are not formalized.

## TODO

* Check the appraisals against the formal definitions of the supplementary methods.

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
  /-- The weight of each feature of an outcome in the player's base utility. -/
  base : Domain → unitInterval
  /-- The weight of the reputation each feature earns. -/
  repu : Domain → unitInterval
  /-- The probability the player gives to the opponent's cooperating. -/
  belief : unitInterval
  /-- The money the player expected to win before learning the pot. -/
  reference : NNReal

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
  /-- The value function. -/
  ν : ℝ → ℝ
  ν_zero : ν 0 = 0
  ν_strictMono : StrictMono ν
  /-- The rationality of the softmax. -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- The money in the jackpot. -/
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

/-! ### Players as agents -/

/-- A player of the anonymous game as an agent: its state is the opponent's action, its belief the
player's belief about it, and its utility the base utility of the outcome. -/
def agent (q : Player) : Agent Unit Action Action :=
  ⟨Kernel.const Unit (bernoulliMeasure .cooperate .defect q.belief),
    fun a₂ a₁ ↦ ((S.baseUtility q a₁ a₂ : ℝ) : EReal)⟩

instance (q : Player) : (S.agent q).IsUnconstrained := by
  unfold agent; infer_instance

-- (3.1)
theorem value_agent (q : Player) (a₁ : Action) :
    (S.agent q).value () a₁ = S.expectedBaseUtility q a₁ := by
  rw [agent, Agent.value_coe, Kernel.const_apply, integral_bernoulliMeasure]
  simp [expectedBaseUtility, sum_action, Player.beliefOn]

/-- The probability (3.3) that a player takes an action, the share the policy of the agent `ag`
makes of the player gives the action at rationality `lam`. -/
def policy (ag : Player → Agent Unit Action Action) (q : Player) (a : Action) : ℝ :=
  ((ag q).policy S.lam ()).real {a}

variable (ag : Player → Agent Unit Action Action) [∀ q, (ag q).IsUnconstrained] (q : Player)

theorem policy_eq_sigmoid (a : Action) :
    S.policy ag q a =
      Real.sigmoid (S.lam * ((ag q).value () a - (ag q).value () a.other)) :=
  Agent.policy_real_of_pair (by cases a <;> decide) fun c ↦ by cases a <;> cases c <;> simp

theorem policy_pos (a : Action) : 0 < S.policy ag q a := Agent.policy_real_singleton_pos

theorem policy_cooperate_le_half_of_belief_eq_zero (hb : q.belief = 0) :
    S.policy S.agent q .cooperate ≤ 1 / 2 := by
  rw [policy_eq_sigmoid, Action.other_cooperate, one_div, ← Real.sigmoid_zero,
    Real.sigmoid_le_iff, value_agent, value_agent, expectedBaseUtility_cooperate_sub_defect, hb,
    Set.Icc.coe_zero]
  nlinarith [mul_nonneg S.lam_pos.le
    (mul_nonneg (unitInterval.nonneg (q.base .dia)) S.ν_pot_nonneg)]

theorem half_le_policy_cooperate_iff (hb : q.belief = 1) :
    1 / 2 ≤ S.policy S.agent q .cooperate ↔
      q.base .money * (S.ν (S.pot - q.reference) - S.ν (S.pot / 2 - q.reference)) ≤
        q.base .aia * S.ν S.pot := by
  rw [policy_eq_sigmoid, Action.other_cooperate, one_div, ← Real.sigmoid_zero,
    Real.sigmoid_le_iff, value_agent, value_agent, expectedBaseUtility_cooperate_sub_defect, hb,
    Set.Icc.coe_one,
    mul_nonneg_iff_of_pos_left S.lam_pos]
  constructor <;> intro h <;> linarith

/-! ### Inverse planning -/

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
  (ag : Player → Agent Unit Action Action) [∀ q, (ag q).IsUnconstrained] (p : Ω → Player)

/-- The forward model: the policy (3.3) of each simulated player, as the agent `ag` makes of
it. -/
def plan : Kernel Ω Action := Agent.plan (fun ω ↦ ag (p ω)) S.lam ()

instance : IsMarkovKernel (S.plan ag p) :=
  inferInstanceAs (IsMarkovKernel (Agent.plan _ _ _))

-- (3.3)
theorem plan_real (ω : Ω) (a : Action) : (S.plan ag p ω).real {a} = S.policy ag (p ω) a := rfl

variable (μ : Measure Ω) [IsProbabilityMeasure μ] [Nonempty Ω]

/-- The observer's inverse inference (3.4), the posterior kernel of the plan. -/
def posterior : Kernel Action Ω := (S.plan ag p)†μ

/-- The posterior expectation of a statistic of the player after observing an action. -/
def expectation (f : Player → ℝ) (a : Action) : ℝ :=
  ∫ ω, f (p ω) ∂(S.posterior ag p μ a)

end Setting

/-- The prior expectation of a statistic of the player. -/
def priorExpectation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → Player)
    (f : Player → ℝ) : ℝ :=
  ∫ ω, f (p ω) ∂μ

namespace Setting

variable (S : Setting) (ag : Player → Agent Unit Action Action) [∀ q, (ag q).IsUnconstrained]
  {Ω : Type*} [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω] [Fintype Ω] [Nonempty Ω] (p : Ω → Player) (μ : Measure Ω)
  [IsProbabilityMeasure μ] {f : Player → ℝ}

/-- Seeing a player cooperate raises the observer's expectation of every statistic of the players
that monovaries with the value advantage of cooperating. -/
theorem priorExpectation_le_expectation_cooperate
    (hf : Monovary (f ∘ p) fun ω ↦
      (ag (p ω)).value () .cooperate - (ag (p ω)).value () .defect) :
    priorExpectation μ p f ≤ S.expectation ag p μ f .cooperate :=
  Agent.integral_le_integral_posterior_plan (fun ω ↦ ag (p ω)) () μ S.lam_pos (by decide)
    (fun c ↦ by cases c <;> simp) (hf.monovaryOn _)

theorem expectation_defect_le_priorExpectation
    (hf : Monovary (f ∘ p) fun ω ↦
      (ag (p ω)).value () .cooperate - (ag (p ω)).value () .defect) :
    S.expectation ag p μ f .defect ≤ priorExpectation μ p f :=
  Agent.integral_posterior_plan_le_integral (fun ω ↦ ag (p ω)) () μ (x := Action.defect)
    (x' := Action.cooperate) S.lam_pos (by decide) (fun c ↦ by cases c <;> simp)
    fun _ _ _ _ hij ↦ hf (by linarith)

theorem expectation_defect_le_expectation_cooperate
    (hf : Monovary (f ∘ p) fun ω ↦
      (ag (p ω)).value () .cooperate - (ag (p ω)).value () .defect) :
    S.expectation ag p μ f .defect ≤ S.expectation ag p μ f .cooperate :=
  (S.expectation_defect_le_priorExpectation ag p μ hf).trans
    (S.priorExpectation_le_expectation_cooperate ag p μ hf)

/-- A prior that varies only in the weight of one domain. -/
def VariesOnly (d : Domain) : Prop :=
  ∀ ω ω', (∀ d', d' ≠ d → (p ω).base d' = (p ω').base d') ∧ (p ω).belief = (p ω').belief ∧
    (p ω).reference = (p ω').reference

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω] [Nonempty Ω] in
-- populations that vary in one weight alone exist: vary that weight of any player
theorem variesOnly_update (q : Player) (d : Domain) (w : Ω → unitInterval) :
    VariesOnly (fun ω ↦ { q with base := Function.update q.base d (w ω) }) d :=
  fun _ _ ↦ ⟨fun _ hd ↦ by simp [Function.update_of_ne hd], rfl, rfl⟩

/-- In a population that varies only in the weight of advantageous inequity, the weight inferred
from cooperation is at least the weight inferred from defection. -/
theorem expectation_aia_defect_le_cooperate (h : VariesOnly p .aia) :
    S.expectation S.agent p μ (fun q ↦ (q.base .aia : ℝ)) .defect ≤
      S.expectation S.agent p μ (fun q ↦ (q.base .aia : ℝ)) .cooperate := by
  refine S.expectation_defect_le_expectation_cooperate _ p μ fun i j hij ↦ ?_
  obtain ⟨hd, hb', hr⟩ := h i j
  have hm := hd .money (by decide)
  have hd' := hd .dia (by decide)
  simp only [value_agent, expectedBaseUtility_cooperate_sub_defect, hm, hd', hb', hr] at hij
  change ((p i).base .aia : ℝ) ≤ (p j).base .aia
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left hlt.le
    (mul_nonneg (unitInterval.nonneg (p j).belief) S.ν_pot_nonneg)]

theorem expectation_money_cooperate_le_defect (h : VariesOnly p .money) :
    S.expectation S.agent p μ (fun q ↦ (q.base .money : ℝ)) .cooperate ≤
      S.expectation S.agent p μ (fun q ↦ (q.base .money : ℝ)) .defect := by
  have := S.expectation_defect_le_expectation_cooperate S.agent p μ
    (f := fun q ↦ -(q.base .money : ℝ)) fun i j hij ↦ ?_
  · simpa only [expectation, integral_neg, neg_le_neg_iff] using this
  obtain ⟨hd, hb', hr⟩ := h i j
  have ha := hd .aia (by decide)
  have hd' := hd .dia (by decide)
  simp only [value_agent, expectedBaseUtility_cooperate_sub_defect, ha, hd', hb', hr] at hij
  have hν : S.ν (S.pot / 2 - (p j).reference) ≤ S.ν (S.pot - (p j).reference) :=
    S.ν_strictMono.monotone (by linarith [S.pot_pos])
  change -((p i).base .money : ℝ) ≤ -(p j).base .money
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left (neg_lt_neg_iff.1 hlt).le
    (mul_nonneg (unitInterval.nonneg (p j).belief) (sub_nonneg.2 hν))]

theorem expectation_dia_cooperate_le_defect (h : VariesOnly p .dia) :
    S.expectation S.agent p μ (fun q ↦ (q.base .dia : ℝ)) .cooperate ≤
      S.expectation S.agent p μ (fun q ↦ (q.base .dia : ℝ)) .defect := by
  have := S.expectation_defect_le_expectation_cooperate S.agent p μ
    (f := fun q ↦ -(q.base .dia : ℝ)) fun i j hij ↦ ?_
  · simpa only [expectation, integral_neg, neg_le_neg_iff] using this
  obtain ⟨hd, hb', hr⟩ := h i j
  have hm := hd .money (by decide)
  have ha := hd .aia (by decide)
  simp only [value_agent, expectedBaseUtility_cooperate_sub_defect, hm, ha, hb', hr] at hij
  change -((p i).base .dia : ℝ) ≤ -(p j).base .dia
  refine le_of_not_gt fun hlt ↦ ?_
  nlinarith [mul_le_mul_of_nonneg_left (neg_lt_neg_iff.1 hlt).le
    (mul_nonneg (unitInterval.one_sub_nonneg (p j).belief) S.ν_pot_nonneg)]

/-! ### The public game -/

/-- The expected reputation in a domain is the base weight an observer of the anonymous game would
infer from the action. -/
def reputation (d : Domain) (a₁ : Action) : ℝ :=
  S.expectation S.agent p μ (fun q ↦ (q.base d : ℝ)) a₁

/-- The reputation utility of an action in a domain: the reputation weight times the value of the
inferred base weight scaled by the pot, with the sign opposite to the base utility's. -/
def reputationUtility (q : Player) (a₁ : Action) (d : Domain) : ℝ :=
  d.repuSign * q.repu d * S.ν (S.reputation p μ d a₁ * S.pot)

/-- The expected utility (3.2) of an action in the public game, the base utility plus the reputation
utilities. -/
def expectedPublicUtility (q : Player) (a₁ : Action) : ℝ :=
  S.expectedBaseUtility q a₁ + ∑ d, S.reputationUtility p μ q a₁ d

/-- A player of the public game as an agent: the utility of an outcome adds the reputation
utilities of the action to its base utility. -/
def publicAgent (q : Player) : Agent Unit Action Action :=
  ⟨Kernel.const Unit (bernoulliMeasure .cooperate .defect q.belief), fun a₂ a₁ ↦
    ((S.baseUtility q a₁ a₂ + ∑ d, S.reputationUtility p μ q a₁ d : ℝ) : EReal)⟩

instance (q : Player) : (S.publicAgent p μ q).IsUnconstrained := by
  unfold publicAgent; infer_instance

-- (3.2)
theorem value_publicAgent (q : Player) (a₁ : Action) :
    (S.publicAgent p μ q).value () a₁ = S.expectedPublicUtility p μ q a₁ := by
  rw [publicAgent, Agent.value_coe, Kernel.const_apply, integral_bernoulliMeasure]
  simp only [expectedPublicUtility, expectedBaseUtility, sum_action, Player.beliefOn,
    smul_eq_mul]
  ring

-- (3.2), given that cooperating earns the higher reputation
theorem policy_cooperate_le_policy_public (q : Player) (hm : q.repu .money = 0)
    (hd : q.repu .dia = 0)
    (hrep : S.reputation p μ .aia .defect ≤ S.reputation p μ .aia .cooperate) :
    S.policy S.agent q .cooperate ≤
      S.policy (S.publicAgent p μ) q .cooperate := by
  rw [policy_eq_sigmoid, policy_eq_sigmoid, Real.sigmoid_le_iff,
    mul_le_mul_iff_of_pos_left S.lam_pos, Action.other_cooperate]
  simp only [value_agent, value_publicAgent, expectedPublicUtility, reputationUtility, sum_domain,
    Domain.repuSign,
    Domain.sign, hm, hd, Set.Icc.coe_zero]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg (unitInterval.nonneg (q.repu .aia)) (sub_nonneg.2 this)]

/-- In a population that varies only in the weight of advantageous inequity, a player whose only
reputation concern is to be thought averse to it cooperates at least as often in public as in the
anonymous game: cooperating is what earns that reputation. -/
theorem policy_cooperate_le_policy_public_of_variesOnly (h : VariesOnly p .aia) (q : Player)
    (hm : q.repu .money = 0) (hd : q.repu .dia = 0) :
    S.policy S.agent q .cooperate ≤ S.policy (S.publicAgent p μ) q .cooperate :=
  S.policy_cooperate_le_policy_public p μ q hm hd (S.expectation_aia_defect_le_cooperate p μ h)

theorem policy_public_le_policy_cooperate (q : Player) (hm : q.repu .money = 0)
    (ha : q.repu .aia = 0)
    (hrep : S.reputation p μ .dia .cooperate ≤ S.reputation p μ .dia .defect) :
    S.policy (S.publicAgent p μ) q .cooperate ≤
      S.policy S.agent q .cooperate := by
  rw [policy_eq_sigmoid, policy_eq_sigmoid, Real.sigmoid_le_iff,
    mul_le_mul_iff_of_pos_left S.lam_pos, Action.other_cooperate]
  simp only [value_agent, value_publicAgent, expectedPublicUtility, reputationUtility, sum_domain,
    Domain.repuSign,
    Domain.sign, hm, ha, Set.Icc.coe_zero]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg (unitInterval.nonneg (q.repu .dia)) (sub_nonneg.2 this)]

/-- The inverse inference (3.4) for the public game, over the six weights and the belief. -/
def publicPosterior : Kernel Action Ω :=
  S.posterior (S.publicAgent p μ) p μ

/-! ### Computed appraisals (Section 4) -/

variable (q : Player)

/-- The expected utility of an action in a domain during planning. -/
def expectedDomainUtility (a₁ : Action) (d : Domain) : ℝ :=
  ∑ a₂, q.beliefOn a₂ * S.domainUtility q a₁ a₂ d

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
def agentCounterfactual (ag : Player → Agent Unit Action Action) (a₁ a₂ : Action) (d : Domain) :
    ℝ :=
  S.policy ag (q.knowing a₂) a₁.other *
    (S.domainUtility q a₁.other a₂ d - S.domainUtility q a₁ a₂ d)

/-- A cooperator whose opponent stole achieves no more disadvantageous-inequity utility than it
expected (Figure 5b). -/
theorem predictionError_dia_cooperate_defect_nonpos :
    S.predictionError q .cooperate .defect .dia ≤ 0 := by
  have hpot := S.pot_pos.le
  simp only [predictionError, expectedDomainUtility, sum_action, domainUtility, Domain.sign,
    Player.beliefOn, feature_dia_cooperate_cooperate, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg (unitInterval.nonneg q.belief)
    (mul_nonneg (unitInterval.nonneg (q.base .dia)) S.ν_pot_nonneg)]

-- Figure 5b
theorem opponentCounterfactual_dia_cooperate_defect_nonneg :
    0 ≤ S.opponentCounterfactual q .cooperate .defect .dia := by
  have hpot := S.pot_pos.le
  simp only [opponentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    Player.beliefOn, feature_dia_cooperate_cooperate, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg (unitInterval.nonneg q.belief)
    (mul_nonneg (unitInterval.nonneg (q.base .dia)) S.ν_pot_nonneg)]

theorem domainUtility_aia_defect_cooperate_nonpos :
    S.domainUtility q .defect .cooperate .aia ≤ 0 := by
  simp only [domainUtility, Domain.sign, feature_aia_defect_cooperate S.pot_pos.le]
  nlinarith [S.ν_pot_nonneg, (unitInterval.nonneg (q.base .aia))]

/-- A player who stole from a cooperator would have gained in advantageous-inequity utility by
cooperating. -/
theorem agentCounterfactual_aia_defect_cooperate_nonneg
    (ag : Player → Agent Unit Action Action) [∀ q, (ag q).IsUnconstrained] :
    0 ≤ S.agentCounterfactual q ag .defect .cooperate .aia := by
  have hpot := S.pot_pos.le
  simp only [agentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    feature_aia_cooperate hpot, feature_aia_defect_cooperate hpot, S.ν_zero]
  nlinarith [mul_nonneg (S.policy_pos ag (q.knowing .cooperate) .cooperate).le
    (mul_nonneg (unitInterval.nonneg (q.base .aia)) S.ν_pot_nonneg)]

theorem opponentCounterfactual_money_cooperate_cooperate_nonpos :
    S.opponentCounterfactual q .cooperate .cooperate .money ≤ 0 := by
  simp only [opponentCounterfactual, Action.other_cooperate, domainUtility, Domain.sign,
    Player.beliefOn, feature_money, payoff, one_mul]
  have := S.ν_strictMono.monotone (show 0 - q.reference ≤ S.pot / 2 - q.reference by
    linarith [S.pot_pos])
  nlinarith [mul_nonneg (unitInterval.one_sub_nonneg q.belief)
    (mul_nonneg (unitInterval.nonneg (q.base .money)) (sub_nonneg.2 this))]

theorem agentCounterfactual_dia_defect_defect_nonpos
    (ag : Player → Agent Unit Action Action) [∀ q, (ag q).IsUnconstrained] :
    S.agentCounterfactual q ag .defect .defect .dia ≤ 0 := by
  have hpot := S.pot_pos.le
  simp only [agentCounterfactual, Action.other_defect, domainUtility, Domain.sign,
    feature_dia_defect hpot, feature_dia_cooperate_defect hpot, S.ν_zero]
  nlinarith [mul_nonneg (S.policy_pos ag (q.knowing .defect) .cooperate).le
    (mul_nonneg (unitInterval.nonneg (q.base .dia)) S.ν_pot_nonneg)]

/-- The agent counterfactual over reputation. -/
def reputationAgentCounterfactual (ag : Player → Agent Unit Action Action) (a₁ a₂ : Action)
    (d : Domain) : ℝ :=
  S.policy ag (q.knowing a₂) a₁.other *
    (S.reputationUtility p μ q a₁.other d - S.reputationUtility p μ q a₁ d)

theorem reputationAgentCounterfactual_aia_defect_nonneg (ag : Player → Agent Unit Action Action)
    [∀ q, (ag q).IsUnconstrained]
    (hrep : S.reputation p μ .aia .defect ≤ S.reputation p μ .aia .cooperate) (a₂ : Action) :
    0 ≤ S.reputationAgentCounterfactual p μ q ag .defect a₂ .aia := by
  simp only [reputationAgentCounterfactual, Action.other_defect, reputationUtility,
    Domain.repuSign, Domain.sign]
  have := S.ν_strictMono.monotone (mul_le_mul_of_nonneg_right hrep S.pot_pos.le)
  nlinarith [mul_nonneg (S.policy_pos ag (q.knowing a₂) .cooperate).le
    (mul_nonneg (unitInterval.nonneg (q.repu .aia)) (sub_nonneg.2 this))]

/-! ### Lesions (Section 5) -/

theorem domainUtility_money_cooperate_lt_defect (hm : 0 < q.base .money) :
    S.domainUtility q .cooperate .cooperate .money <
      S.domainUtility q .defect .cooperate .money := by
  simp only [domainUtility, Domain.sign, feature_money, payoff, one_mul]
  exact mul_lt_mul_of_pos_left (S.ν_strictMono (by linarith [S.pot_pos]))
    (unitInterval.coe_pos.2 hm)

end Setting

end

end HoulihanEtAl2023
