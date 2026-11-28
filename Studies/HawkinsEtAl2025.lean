module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Data.Examples.HawkinsEtAl2025
public import Linglib.Semantics.Questions.Inquisitive.Polar
public import Linglib.Pragmatics.Agent.InversePlanning
public import Linglib.Pragmatics.Probabilistic.Literal

/-!
# Hawkins, Tsvilodub, Bergey, Goodman and Franke (2025): Relevant answers to polar questions

In the PRIOR-PQ model of [hawkins-etal-2025] a questioner has a decision problem, a utility
`U : W → A → ℝ` over worlds and actions with a belief `π` about the world. Its policy
soft-maximizes the expected utility `∫ w, U w a ∂π` of an action, and its value `value U αℵ π` is
the expected utility of following the policy.

A response `r` is safe for the polar question `q` when every belief state that knows `r` resolves
`q`. The base respondent `m.R0 q` answers `q` at a world uniformly among the true and safe
responses. The questioner `m.questioner p d` is an agent that chooses a question, worth to it the
expected value of its decision problem after the base respondent's answer, less the cost of the
answer, and `m.questionerPlan p` gives its policy at each decision problem. The pragmatic
respondent `m.respondent p πD πW` infers the decision problem from the question by Bayes' rule and
soft-maximizes a weighted sum of informativity, the negative Kullback-Leibler divergence of the
questioner's updated belief from its own belief `πW`, and action relevance, the value of the
questioner's updated decision problem, less the cost of the response.

A response is safe iff it resolves the polar question (`safe_iff_mem_polar`). The value of a
question to the questioner is its value of information under `value`, plus the value of the prior,
less the expected cost (`Model.value_questioner_eq_valueOfInformation`). When informativity has
positive weight, the respondent never gives a response false at a world it considers possible
(`Model.respondent_truthful`).

In the credit-card model `cards ι` the worlds are the sets of accepted cards, the questioner goes
to the restaurant or stays, and an action is worth 5 when it matches whether a card of interest is
accepted and 0 otherwise. Of two beliefs about such a bet, the one further from even odds has the
greater value (`value_lt_value_iff`), so a response that leaves open whether going pays leaves a
decision problem of lower value than one that settles it (`value_lt_of_notMem_polar`), and *yes*
to "Do you accept credit cards?" leaves a questioner who holds some but not all of the cards worse
off than the exhaustive list does (`value_generalYes_lt_value_exhaustive`).

## Implementation notes

* A decision problem is an `Agent` that observes nothing (`problem`), and its policy is
  `Agent.policy`. The value is monotone in the rationality (`value_mono`) and at most the best
  expected utility `decisionValue`, the value of a decision problem in [van-rooy-2003b]
  (`value_le_decisionValue`), to which it tends as the rationality grows
  (`tendsto_value_atTop`). It is not convex in the belief: `decisionValue` gives information
  nonnegative value (`valueOfInformation_decisionValue_nonneg`), and under `value` learning the
  world can have negative value (`valueOfInformation_value_gamble_neg`).
* The questioner's utility for a question at a world integrates over the base respondent's answer
  there, so its value under the prior is the expectation over the answers `m.R0 q ∘ₘ m.prior d`
  (`Model.value_questioner`), and `m.questionerPlan p` is the `Agent.plan` of the questioners.
* The questioner hearing a response and the respondent hearing a question are `RSA.listener`s of
  the base respondent and of the questioner, so a response no world produces leaves the zero
  measure; the questioner and the pragmatic respondent are `Kernel.softmax` kernels.
* `Safe q r` says that not knowing the answer to `q` entails not knowing `r`, the reading on which
  mentioning Visa is safe for "Do you take Visa or Mastercard?". It applies to a mention apart
  from the polar answer it accompanies ("No, but we take American Express").
* Informativity is `klDiv πW π'` with the respondent's belief `πW` in the first argument and the
  questioner's updated belief `π'` in the second, so a response false at a world the respondent
  considers possible has infinite divergence. The expected divergence is a lower integral and the
  score is `EReal`-valued.
* Both terms of the respondent's score read the questioner's belief after the update by the
  truth-only base respondent `m.R0'`, which is defined at unsafe responses.
* The credit-card model is stated over any finite type `ι` of cards. The dialogues about Visa,
  Mastercard and American Express instantiate it at the cards of the data file.

## TODO

* The comparison of *no* about a card with *yes* to the general question, which
  `value_lt_value_iff_abs` reduces to a comparison of the two posterior probabilities that going
  pays.
* The predicted rates of exhaustive answers, highest after a polar question about an unavailable
  card, then after the general question, then after a polar question about an available card,
  which depend on the fitted parameters.
* The iced tea and blanket case studies, with the elicited utilities.
* The definition of safety in the paper's supplementary material has not been compared with
  `Safe`.

## References

* [hawkins-etal-2025]
* [van-rooy-2003b]
-/

@[expose] public section

namespace HawkinsEtAl2025

open MeasureTheory ProbabilityTheory InformationTheory Finset Inquisitive Inquisitive.Proposition
open scoped ENNReal NNReal

variable {W Q R A D : Type*}

/-! ### Safe answers (§2a) -/

/-- A response `r` is safe for the polar question `q` when not knowing the answer to `q` entails
not knowing `r`, that is, when every belief state that knows `r` resolves `q`. -/
def Safe (q r : Set W) : Prop := ∀ s ⊆ r, s ∈ polar q

/-- A response is safe exactly when it resolves the polar question, since resolution is
downward closed. -/
theorem safe_iff_mem_polar {q r : Set W} : Safe q r ↔ r ∈ polar q :=
  ⟨fun h ↦ h r subset_rfl, fun h _ hs ↦ (polar q).isLowerSet hs h⟩

instance [Fintype W] (q r : Set W) [DecidablePred (· ∈ q)] [DecidablePred (· ∈ r)] :
    Decidable (Safe q r) :=
  decidable_of_iff ((∀ w, w ∈ r → w ∈ q) ∨ ∀ w, w ∈ r → w ∉ q)
    (safe_iff_mem_polar.trans mem_polar).symm

/-! ### The model -/

/-- A PRIOR-PQ model gives the propositions that questions and responses denote, the
questioner's decision problems, and the cost of responses. -/
structure Model (W Q R A D : Type*) [MeasurableSpace W] where
  /-- The proposition a polar question asks about. -/
  question : Q → Set W
  /-- The proposition a response asserts. -/
  response : R → Set W
  /-- The utility function of a decision problem. -/
  utility : D → W → A → ℝ
  /-- The questioner's prior over worlds under a decision problem. -/
  prior : D → Measure W
  /-- The production cost of a response. -/
  cost : R → ℝ

/-- The parameters of PRIOR-PQ are the rationalities of the policy, the questioner and the
respondent, the weight of cost, and the weight `β` of action relevance against informativity. -/
structure Params where
  /-- The rationality `αℵ` of the policy. -/
  αℵ : ℝ
  /-- The rationality `αQ` of the questioner. -/
  αQ : ℝ
  /-- The rationality `αR` of the respondent. -/
  αR : ℝ
  /-- The weight `w_c` of response cost. -/
  wc : ℝ
  /-- The weight `β` of action relevance. -/
  β : ℝ

variable [MeasurableSpace W] [MeasurableSpace R] (m : Model W Q R A D)

/-- `m.trueSafe w q` is the set of responses true at `w` and safe for `q`. -/
def Model.trueSafe (w : W) (q : Q) : Set R :=
  {r | w ∈ m.response r ∧ Safe (m.question q) (m.response r)}

instance [Fintype W] [∀ q, DecidablePred (· ∈ m.question q)]
    [∀ r, DecidablePred (· ∈ m.response r)] (w : W) (q : Q) : DecidablePred (· ∈ m.trueSafe w q) :=
  fun r ↦ inferInstanceAs (Decidable (w ∈ m.response r ∧ Safe (m.question q) (m.response r)))

/-! ### The base respondent (§2a) -/

section BaseRespondent

section

variable [Countable W] [MeasurableSingletonClass W]

/-- The base respondent (2.1) answers `q` at `w` uniformly among the true and safe responses. -/
noncomputable def Model.R0 (q : Q) : Kernel W R :=
  Kernel.ofFunOfCountable fun w ↦ uniformOn (m.trueSafe w q)

/-- The truth-only base respondent `R0'` (§2c) answers uniformly among the true responses. -/
noncomputable def Model.R0' : Kernel W R :=
  Kernel.ofFunOfCountable fun w ↦ uniformOn {r | w ∈ m.response r}

@[simp] theorem Model.R0_apply (q : Q) (w : W) : m.R0 q w = uniformOn (m.trueSafe w q) := rfl

@[simp] theorem Model.R0'_apply (w : W) : m.R0' w = uniformOn {r | w ∈ m.response r} := rfl

instance (q : Q) : IsFiniteKernel (m.R0 q) :=
  ⟨⟨1, ENNReal.one_lt_top, fun w ↦ show uniformOn (m.trueSafe w q) Set.univ ≤ 1 from
    prob_le_one⟩⟩

instance : IsFiniteKernel m.R0' :=
  ⟨⟨1, ENNReal.one_lt_top, fun w ↦ show uniformOn {r | w ∈ m.response r} Set.univ ≤ 1 from
    prob_le_one⟩⟩

variable [Finite R] [MeasurableSingletonClass R]

theorem Model.R0_apply_singleton_ne_zero_iff {q : Q} {w : W} {r : R} :
    m.R0 q w {r} ≠ 0 ↔ r ∈ m.trueSafe w q := by
  rw [R0_apply, Ne, uniformOn_eq_zero_iff (Set.toFinite _), Set.inter_singleton_eq_empty,
    not_not]

theorem Model.R0'_apply_singleton_ne_zero_iff {w : W} {r : R} :
    m.R0' w {r} ≠ 0 ↔ w ∈ m.response r := by
  rw [R0'_apply, Ne, uniformOn_eq_zero_iff (Set.toFinite _), Set.inter_singleton_eq_empty,
    not_not]
  exact Iff.rfl

theorem Model.R0_real_singleton (q : Q) (w : W) (r : R) [Decidable (r ∈ m.trueSafe w q)] :
    (m.R0 q w).real {r} = if r ∈ m.trueSafe w q then ((m.trueSafe w q).ncard : ℝ)⁻¹ else 0 := by
  rw [R0_apply, uniformOn_real_apply]
  split_ifs with h
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h), Set.ncard_singleton, Nat.cast_one,
      one_div]
  · rw [Set.inter_singleton_eq_empty.2 h, Set.ncard_empty, Nat.cast_zero, zero_div]

theorem Model.isMarkovKernel_R0 {q : Q} (h : ∀ w, (m.trueSafe w q).Nonempty) :
    IsMarkovKernel (m.R0 q) :=
  ⟨fun w ↦ isProbabilityMeasure_uniformOn (Set.toFinite _) (h w)⟩

end

variable [Fintype W] [MeasurableSingletonClass W] [Finite R] [MeasurableSingletonClass R] {d : D}
  [IsFiniteMeasure (m.prior d)]

theorem Model.listener_R0'_apply_singleton_ne_zero_iff (hπ : ∀ w, m.prior d {w} ≠ 0) {r : R}
    {w : W} : RSA.listener (m.prior d) m.R0' r {w} ≠ 0 ↔ w ∈ m.response r := by
  rw [RSA.listener_apply_singleton_ne_zero_iff, m.R0'_apply_singleton_ne_zero_iff]
  exact and_iff_right (hπ w)

theorem Model.listener_R0'_apply_compl_response (r : R) :
    RSA.listener (m.prior d) m.R0' r (m.response r)ᶜ = 0 :=
  mem_ae_iff.1 (ae_iff_of_countable.2 fun _ hw ↦
    m.R0'_apply_singleton_ne_zero_iff.1 (RSA.listener_apply_singleton_ne_zero_iff.1 hw).2)

-- §2b
theorem Model.listener_R0_real_lt_iff {q : Q} {r : R} {w₁ w₂ : W}
    (hp : m.prior d {w₁} = m.prior d {w₂}) (hpos : m.prior d {w₁} ≠ 0)
    (h₁ : r ∈ m.trueSafe w₁ q) (h₂ : r ∈ m.trueSafe w₂ q) :
    (RSA.listener (m.prior d) (m.R0 q) r).real {w₁} <
        (RSA.listener (m.prior d) (m.R0 q) r).real {w₂} ↔
      (m.trueSafe w₂ q).ncard < (m.trueSafe w₁ q).ncard := by
  classical
  have hc {w} (hw : r ∈ m.trueSafe w q) : (0 : ℝ) < (m.trueSafe w q).ncard :=
    Nat.cast_pos.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨r, hw⟩)
  have hμ : (m.prior d).real {w₂} = (m.prior d).real {w₁} := by
    rw [measureReal_def, measureReal_def, hp]
  have hμpos : 0 < (m.prior d).real {w₁} := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  rw [RSA.listener_real_singleton_lt_iff, hμ, mul_lt_mul_iff_right₀ hμpos, m.R0_real_singleton,
    m.R0_real_singleton, ite_eq_left h₁, ite_eq_left h₂, inv_lt_inv₀ (hc h₁) (hc h₂), Nat.cast_lt]

end BaseRespondent

/-! ### The questioner (§2b) -/

section Questioner

variable [Fintype A] [MeasurableSpace A]

/-- The decision problem with utility `U` and belief `π` is an agent that observes nothing. -/
def problem (U : W → A → ℝ) (π : Measure W) : Agent Unit W A :=
  ⟨Kernel.const Unit π, fun w a ↦ (U w a : EReal)⟩

instance (U : W → A → ℝ) (π : Measure W) : (problem U π).IsUnconstrained := by
  unfold problem; infer_instance

/-- The value `V(D)` of a decision problem is the expected utility of following its policy (2.2),
the policy of the agent at rationality `αℵ`. -/
noncomputable def value (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) : ℝ :=
  ∫ a, (problem U π).value () a ∂(problem U π).policy αℵ ()

section

variable [MeasurableSingletonClass A] {U : W → A → ℝ} {αℵ : ℝ} {π : Measure W} {a b : A}

theorem value_eq_sum (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) :
    value U αℵ π =
      ∑ a, Real.softmax (fun a ↦ αℵ * ∫ w, U w a ∂π) a * ∫ w, U w a ∂π := by
  simp only [value, integral_fintype .of_finite, smul_eq_mul, Agent.policy_real_singleton,
    problem, Agent.value_coe, Kernel.const_apply]

theorem value_le_decisionValue [Nonempty A] (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) :
    value U αℵ π ≤ decisionValue U π := by
  rw [value_eq_sum]
  refine (Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (integral_le_decisionValue π a)
    (Real.softmax_nonneg _ a)).trans_eq ?_
  rw [← Finset.sum_mul, Real.sum_softmax, one_mul]

theorem value_of_pair (hab : a ≠ b) (hall : ∀ c, c = a ∨ c = b) :
    value U αℵ π =
      Real.sigmoid (αℵ * (∫ w, U w a ∂π - ∫ w, U w b ∂π)) * ∫ w, U w a ∂π +
        (1 - Real.sigmoid (αℵ * (∫ w, U w a ∂π - ∫ w, U w b ∂π))) * ∫ w, U w b ∂π := by
  classical
  have huniv : (Finset.univ : Finset A) = {a, b} := by ext c; simpa using hall c
  rw [value, integral_fintype .of_finite, huniv, Finset.sum_pair hab,
    Agent.policy_real_of_pair hab hall,
    Agent.policy_real_of_pair hab.symm fun c ↦ (hall c).symm, ← Real.sigmoid_neg]
  simp only [problem, Agent.value_coe, Kernel.const_apply, smul_eq_mul]
  ring_nf

theorem value_mono [Nonempty A] (U : W → A → ℝ) (π : Measure W) :
    Monotone fun αℵ ↦ value U αℵ π := fun α β h ↦ by
  show value U α π ≤ value U β π
  rw [value_eq_sum, value_eq_sum]
  exact Real.monotone_sum_softmax_smul_mul (fun a ↦ ∫ w, U w a ∂π) h

-- [van-rooy-2003b]
theorem tendsto_value_atTop [Nonempty A] (U : W → A → ℝ) (π : Measure W) :
    Filter.Tendsto (fun αℵ ↦ value U αℵ π) .atTop (nhds (decisionValue U π)) := by
  simp only [value_eq_sum]
  exact Real.tendsto_sum_softmax_smul_mul_atTop fun a ↦ ∫ w, U w a ∂π

private theorem mul_sigmoid_sub_half_lt_iff {k x y : ℝ} (hk : 0 < k) :
    x * (Real.sigmoid (k * x) - 1 / 2) < y * (Real.sigmoid (k * y) - 1 / 2) ↔ |x| < |y| := by
  have even (t : ℝ) :
      t * (Real.sigmoid (k * t) - 1 / 2) = |t| * (Real.sigmoid (k * |t|) - 1 / 2) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sigmoid_neg]; ring
  have mono : StrictMonoOn (fun t : ℝ ↦ t * (Real.sigmoid (k * t) - 1 / 2)) (Set.Ici 0) := by
    intro a ha b hb hab
    have h0 : 0 ≤ Real.sigmoid (k * a) - 1 / 2 := by
      rw [sub_nonneg, one_div, ← Real.sigmoid_zero]
      exact Real.sigmoid_le_iff.2 (mul_nonneg hk.le ha)
    have hlt : Real.sigmoid (k * a) < Real.sigmoid (k * b) :=
      Real.sigmoid_lt (mul_lt_mul_of_pos_left hab hk)
    show a * _ < b * _
    nlinarith [mul_pos (sub_pos.2 hab) (lt_of_le_of_lt h0 (sub_lt_sub_right hlt _)),
      mul_nonneg ha (sub_nonneg.2 hlt.le)]
  rw [even x, even y]
  exact mono.lt_iff_lt (abs_nonneg x) (abs_nonneg y)

theorem value_of_integral_eq {c p : ℝ} (hab : a ≠ b) (hall : ∀ c, c = a ∨ c = b)
    (ha : ∫ w, U w a ∂π = c * p) (hb : ∫ w, U w b ∂π = c * (1 - p)) :
    value U αℵ π =
      c / 2 + c * ((2 * p - 1) * (Real.sigmoid (αℵ * c * (2 * p - 1)) - 1 / 2)) := by
  rw [value_of_pair hab hall, ha, hb,
    show αℵ * (c * p - c * (1 - p)) = αℵ * c * (2 * p - 1) by ring]
  ring

/-- Of two beliefs about a bet that pays `c` on one action with probability `p` and on the other
with probability `1 - p`, the one further from even odds has the greater value. -/
theorem value_lt_value_iff {π' : Measure W} {c p p' : ℝ} (hα : 0 < αℵ) (hc : 0 < c)
    (hab : a ≠ b) (hall : ∀ c, c = a ∨ c = b) (ha : ∫ w, U w a ∂π = c * p)
    (hb : ∫ w, U w b ∂π = c * (1 - p)) (ha' : ∫ w, U w a ∂π' = c * p')
    (hb' : ∫ w, U w b ∂π' = c * (1 - p')) :
    value U αℵ π < value U αℵ π' ↔ |2 * p - 1| < |2 * p' - 1| := by
  rw [value_of_integral_eq hab hall ha hb, value_of_integral_eq hab hall ha' hb',
    add_lt_add_iff_left, mul_lt_mul_iff_right₀ hc, mul_sigmoid_sub_half_lt_iff (mul_pos hα hc)]

end

private theorem sigmoid_log_two_mul (n : ℕ) :
    Real.sigmoid (Real.log 2 * n) = 2 ^ n / (2 ^ n + 1) := by
  have h : Real.exp (-(Real.log 2 * n)) = (2 ^ n)⁻¹ := by
    rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log two_pos]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [Real.sigmoid_def, h]
  field_simp

/-- A safe action worth 1 and a risky action worth -2 at one world and -4 at the other. -/
def gamble (w a : Fin 2) : ℝ := if a = 0 then 1 else if w = 0 then -2 else -4

theorem valueOfInformation_value_gamble_neg :
    valueOfInformation (value gamble (Real.log 2)) Kernel.id
      ((2⁻¹ : ℝ≥0) • (Measure.dirac 0 + Measure.dirac 1)) < 0 := by
  have hμ (f : Fin 2 → ℝ) :
      ∫ w, f w ∂((2⁻¹ : ℝ≥0) • (Measure.dirac 0 + Measure.dirac 1)) = (f 0 + f 1) / 2 := by
    rw [integral_smul_nnreal_measure, integral_add_measure .of_finite .of_finite,
      integral_dirac, integral_dirac, NNReal.smul_def]
    simp
    ring
  have hv (π : Measure (Fin 2)) := value_of_pair (U := gamble) (αℵ := Real.log 2) (π := π)
    (a := 0) (b := 1) (by decide) (by decide)
  have s3 := sigmoid_log_two_mul 3
  have s4 := sigmoid_log_two_mul 4
  have s5 := sigmoid_log_two_mul 5
  rw [valueOfInformation_id, hμ, hv, hv, hv]
  simp only [integral_dirac, hμ, gamble]
  norm_num at s3 s4 s5 ⊢
  rw [s3, s4, s5]
  norm_num

variable [Fintype W] [MeasurableSingletonClass W] [Finite R] [MeasurableSingletonClass R]
  (p : Params)

/-- The questioner with the decision problem `d` is an agent that chooses a question (2.3). At
the world `w`, asking `q` is worth the expected value of `d` updated (2.4) by the base
respondent's answer at `w`, less the weighted cost of the answer. -/
noncomputable def Model.questioner (d : D) : Agent Unit W Q where
  belief := Kernel.const Unit (m.prior d)
  utility w q := ((∫ r, (value (m.utility d) p.αℵ (RSA.listener (m.prior d) (m.R0 q) r) -
    p.wc * m.cost r) ∂(m.R0 q w) : ℝ) : EReal)

instance (d : D) : (m.questioner p d).IsUnconstrained := by
  unfold Model.questioner; infer_instance

theorem Model.value_questioner (d : D) [IsFiniteMeasure (m.prior d)] (q : Q) :
    (m.questioner p d).value () q =
      ∫ r, (value (m.utility d) p.αℵ (RSA.listener (m.prior d) (m.R0 q) r) - p.wc * m.cost r)
        ∂(m.R0 q ∘ₘ m.prior d) := by
  rw [Measure.integral_comp .of_finite]
  rfl

/-- The value of a question to the questioner is its value of information under the policy
value, plus the value of the prior, less the expected cost. -/
theorem Model.value_questioner_eq_valueOfInformation [StandardBorelSpace W] [Nonempty W] (d : D)
    [IsFiniteMeasure (m.prior d)] (q : Q) :
    (m.questioner p d).value () q =
      valueOfInformation (value (m.utility d) p.αℵ) (m.R0 q) (m.prior d) +
        value (m.utility d) p.αℵ (m.prior d) - p.wc * ∫ r, m.cost r ∂(m.R0 q ∘ₘ m.prior d) := by
  have h : ∀ᵐ r ∂(m.R0 q ∘ₘ m.prior d),
      RSA.listener (m.prior d) (m.R0 q) r = ((m.R0 q)†(m.prior d)) r :=
    ae_iff_of_countable.2 fun r hr ↦ RSA.listener_apply_eq_posterior _ _ hr
  rw [m.value_questioner, integral_sub .of_finite .of_finite, integral_const_mul,
    valueOfInformation, integral_congr_ae (h.mono fun r hr ↦ congrArg _ hr)]
  ring

variable [MeasurableSpace Q] [Fintype Q] [MeasurableSpace D] [Fintype D]
  [MeasurableSingletonClass D]

/-- The questions asked under each decision problem: the policy of its questioner at rationality
`αQ`. -/
noncomputable def Model.questionerPlan : Kernel D Q := Agent.plan (m.questioner p) p.αQ ()

instance : IsFiniteKernel (m.questionerPlan p) :=
  inferInstanceAs (IsFiniteKernel (Agent.plan _ _ _))

instance [Nonempty Q] : IsMarkovKernel (m.questionerPlan p) :=
  inferInstanceAs (IsMarkovKernel (Agent.plan _ _ _))

theorem Model.questionerPlan_apply_singleton_ne_zero [MeasurableSingletonClass Q] (d : D)
    (q : Q) : m.questionerPlan p d {q} ≠ 0 :=
  (m.questioner p d).policy_apply_singleton_ne_zero p.αQ () q

end Questioner

/-! ### The pragmatic respondent (§2c) -/

section Respondent

variable [Fintype A] [MeasurableSpace A] [Fintype W] [MeasurableSingletonClass W] [Fintype R]
  [MeasurableSingletonClass R] (p : Params) [MeasurableSpace Q] [Fintype Q]
  [MeasurableSingletonClass Q] [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
  (πD : Measure D)

/-- The respondent's belief about the decision problem after hearing `q` is that of a listener
to the questioner at the prior `πD`, `π(D ∣ q) ∝ Q(q ∣ D) π(D)`. -/
noncomputable def Model.goalPosterior : Kernel Q D := RSA.listener πD (m.questionerPlan p)

instance : IsFiniteKernel (m.goalPosterior p πD) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ _))

theorem Model.goalPosterior_real_lt_iff [IsFiniteMeasure πD] (q : Q) {d₁ d₂ : D}
    (hp : πD {d₁} = πD {d₂}) (hpos : πD {d₁} ≠ 0) :
    (m.goalPosterior p πD q).real {d₁} < (m.goalPosterior p πD q).real {d₂} ↔
      (m.questionerPlan p d₁).real {q} < (m.questionerPlan p d₂).real {q} := by
  have hμ : πD.real {d₂} = πD.real {d₁} := by rw [measureReal_def, measureReal_def, hp]
  have hμpos : 0 < πD.real {d₁} := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  rw [Model.goalPosterior, RSA.listener_real_singleton_lt_iff, hμ, mul_lt_mul_iff_right₀ hμpos]

/-- The pragmatic respondent's score for answering `q` with `r` (2.5) is the expectation over the
inferred decision problem of informativity, weighted by `1 - β`, and action relevance, weighted
by `β`, less the weighted cost. Both terms read the questioner's belief after the truth-only
update, and informativity is its negative divergence from the respondent's belief `πW`. The
expected divergence is a lower integral, so a response at infinite divergence scores `⊥`. -/
noncomputable def Model.respondentScore (πW : Measure W) (q : Q) (r : R) : EReal :=
  ((1 - p.β : ℝ) : EReal) *
      -((∫⁻ d, klDiv πW (RSA.listener (m.prior d) m.R0' r) ∂(m.goalPosterior p πD q) : ℝ≥0∞) :
        EReal) +
    ((p.β * ∫ d, value (m.utility d) p.αℵ (RSA.listener (m.prior d) m.R0' r)
        ∂(m.goalPosterior p πD q) - p.wc * m.cost r : ℝ) : EReal)

theorem Model.respondentScore_of_beta_eq_one (hβ : p.β = 1) (πW : Measure W) (q : Q) (r : R) :
    m.respondentScore p πD πW q r =
      ((∫ d, value (m.utility d) p.αℵ (RSA.listener (m.prior d) m.R0' r)
          ∂(m.goalPosterior p πD q) - p.wc * m.cost r : ℝ) : EReal) := by
  simp [Model.respondentScore, hβ]

/-- The pragmatic respondent (2.5) soft-maximizes its score with rationality `αR`. -/
noncomputable def Model.respondent (πW : Measure W) : Kernel Q R :=
  Kernel.softmax fun q r ↦ (p.αR : EReal) * m.respondentScore p πD πW q r

-- §2c
theorem Model.respondent_apply_singleton_ne_zero_of_beta_eq_one (hβ : p.β = 1)
    (πW : Measure W) (q : Q) (r : R) : m.respondent p πD πW q {r} ≠ 0 := by
  have h (r : R) : ∃ x : ℝ, (p.αR : EReal) * m.respondentScore p πD πW q r = x :=
    ⟨_, by rw [m.respondentScore_of_beta_eq_one p πD hβ, ← EReal.coe_mul]⟩
  exact Kernel.softmax_apply_singleton_ne_zero
    (by obtain ⟨x, hx⟩ := h r; exact hx ▸ EReal.coe_ne_bot x)
    fun r' ↦ by obtain ⟨x, hx⟩ := h r'; exact hx ▸ EReal.coe_ne_top x

/-- When `β < 1`, the respondent never gives a response false at a world it considers possible. -/
theorem Model.respondent_truthful [IsFiniteMeasure πD] (hβ : p.β < 1) (hα : 0 < p.αR)
    {πW : Measure W} {q : Q} {r : R} {d : D} (hd : πD {d} ≠ 0) {w : W} (hw : πW {w} ≠ 0)
    (hf : w ∉ m.response r) : m.respondent p πD πW q {r} = 0 := by
  have hkl : klDiv πW (RSA.listener (m.prior d) m.R0' r) = ∞ :=
    klDiv_of_not_ac fun hac ↦ hw (hac (RSA.listener_apply_singleton_eq_zero
      (not_not.1 (mt m.R0'_apply_singleton_ne_zero_iff.1 hf))))
  have hgp : m.goalPosterior p πD q {d} ≠ 0 :=
    RSA.listener_apply_singleton_ne_zero hd (m.questionerPlan_apply_singleton_ne_zero p d q)
  have hint : ∫⁻ d', klDiv πW (RSA.listener (m.prior d') m.R0' r) ∂(m.goalPosterior p πD q) =
      ∞ := by
    rw [lintegral_countable']
    exact tsum_eq_top_of_eq_top ⟨d, by rw [hkl, ENNReal.top_mul hgp]⟩
  refine Kernel.softmax_apply_singleton_eq_zero ?_
  simp only [Model.respondentScore, hint, EReal.coe_ennreal_top, EReal.neg_top,
    EReal.coe_mul_bot_of_pos (sub_pos.2 hβ), EReal.bot_add, EReal.coe_mul_bot_of_pos hα]

end Respondent

/-! ### Case study 1: credit cards (§3a) -/

/-- The questioner either stays or goes. -/
inductive Act where
  | stay
  | go
  deriving DecidableEq, Fintype

instance : MeasurableSpace Act := ⊤

/-- A response is a polar answer to whether any card of `S` is accepted, the mention of some
accepted cards, or the exhaustive list of the accepted cards. -/
inductive Resp (ι : Type*) where
  | polar (S : Finset ι) (b : Bool)
  | mention (T : Finset ι)
  | exhaustive (T : Finset ι)
  deriving DecidableEq, Fintype

instance {ι : Type*} : MeasurableSpace (Resp ι) := ⊤

/-- The decision problem `U1` turns on whether any of the questioner's cards `C` is accepted,
and `U2` on whether any card is accepted. -/
inductive Goal (ι : Type*) where
  | ownCards (C : Finset ι)
  | anyCard
  deriving DecidableEq, Fintype

instance {ι : Type*} : MeasurableSpace (Goal ι) := ⊤

variable {ι : Type*} [DecidableEq ι]

/-- `d.target` is the set of worlds at which going pays under the goal `d`. -/
def Goal.target : Goal ι → Set (Finset ι)
  | .ownCards C => {w | (C ∩ w).Nonempty}
  | .anyCard => {w | w.Nonempty}

/-- The utility of §3a is 5 for going when a relevant card is accepted or staying when none is,
and 0 otherwise. -/
noncomputable def cardUtility (d : Goal ι) (w : Finset ι) : Act → ℝ
  | .go => d.target.indicator (fun _ ↦ 5) w
  | .stay => d.targetᶜ.indicator (fun _ ↦ 5) w

/-- `r.denote` is the set of worlds at which the response `r` is true. -/
def Resp.denote : Resp ι → Set (Finset ι)
  | .polar S b => {w | (S ∩ w).Nonempty ↔ b = true}
  | .mention T => {w | T ⊆ w}
  | .exhaustive T => {T}

instance : ∀ r : Resp ι, DecidablePred (· ∈ r.denote)
  | .polar S b, w => inferInstanceAs (Decidable ((S ∩ w).Nonempty ↔ b = true))
  | .mention T, w => inferInstanceAs (Decidable (T ⊆ w))
  | .exhaustive T, w => inferInstanceAs (Decidable (w = T))

variable (ι) in
/-- In the credit-card model over the cards `ι`, a question asks whether any card of a set is
accepted, worlds are the sets of accepted cards, priors are uniform over worlds, and a response
costs the cards it mentions. -/
noncomputable def cards : Model (Finset ι) (Finset ι) (Resp ι) Act (Goal ι) where
  question S := {w | (S ∩ w).Nonempty}
  response := Resp.denote
  utility := cardUtility
  prior _ := uniformOn Set.univ
  cost
    | .polar _ _ => 0
    | .mention T => T.card
    | .exhaustive T => T.card

instance (S : Finset ι) : DecidablePred (· ∈ (cards ι).question S) :=
  fun w ↦ inferInstanceAs (Decidable (S ∩ w).Nonempty)

instance (r : Resp ι) : DecidablePred (· ∈ (cards ι).response r) :=
  inferInstanceAs (DecidablePred (· ∈ r.denote))

@[simp] theorem mem_response_polar_true {S w : Finset ι} :
    w ∈ (cards ι).response (.polar S true) ↔ (S ∩ w).Nonempty :=
  iff_true_right rfl

@[simp] theorem mem_response_polar_false {S w : Finset ι} :
    w ∈ (cards ι).response (.polar S false) ↔ ¬(S ∩ w).Nonempty :=
  iff_false_right Bool.false_ne_true

theorem safe_polar (S : Finset ι) (b : Bool) :
    Safe ((cards ι).question S) ((cards ι).response (.polar S b)) := by
  rw [safe_iff_mem_polar, mem_polar]
  cases b
  · exact .inr fun _ hw ↦ mem_response_polar_false.1 hw
  · exact .inl fun _ hw ↦ mem_response_polar_true.1 hw

theorem safe_exhaustive (S T : Finset ι) :
    Safe ((cards ι).question S) ((cards ι).response (.exhaustive T)) := by
  rw [safe_iff_mem_polar, mem_polar]
  by_cases h : T ∈ (cards ι).question S
  · exact .inl (Set.singleton_subset_iff.2 h)
  · exact .inr (Set.singleton_subset_iff.2 h)

theorem mention_safe_iff (S T : Finset ι) (hS : S.Nonempty) :
    Safe ((cards ι).question S) ((cards ι).response (.mention T)) ↔ (T ∩ S).Nonempty := by
  rw [safe_iff_mem_polar, mem_polar]
  constructor
  · rintro (h | h)
    · exact Finset.inter_comm S T ▸ h (show T ∈ {w | T ⊆ w} from Finset.Subset.refl T)
    · obtain ⟨s, hs⟩ := hS
      exact absurd ⟨s, Finset.mem_inter.2 ⟨hs, Finset.mem_union_right _ hs⟩⟩
        (h (show T ∪ S ∈ {w | T ⊆ w} from Finset.subset_union_left))
  · rintro ⟨t, ht⟩
    exact .inl fun w hw ↦ ⟨t, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 ht).2,
      hw (Finset.mem_inter.1 ht).1⟩⟩

-- (1), (2)
theorem mention_rows :
    ∀ e ∈ Examples.all, ∀ c ∈ Examples.mentioned e,
      (Safe ((cards Examples.Card).question {.visa, .mastercard})
          ((cards Examples.Card).response (.mention {c})) ↔ e.judgment = .questionable) := by
  decide

theorem trueSafe_nonempty (w q : Finset ι) : ((cards ι).trueSafe w q).Nonempty :=
  ⟨.polar q (decide (q ∩ w).Nonempty),
    show (q ∩ w).Nonempty ↔ decide (q ∩ w).Nonempty = true by simp, safe_polar q _⟩

section Value

variable [Fintype ι] {d : Goal ι} {r : Resp ι} {αℵ : ℝ}

instance (q : Finset ι) : IsMarkovKernel ((cards ι).R0 q) :=
  (cards ι).isMarkovKernel_R0 fun w ↦ trueSafe_nonempty w q

instance (d : Goal ι) : IsProbabilityMeasure ((cards ι).prior d) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

private theorem cards_prior_ne_zero (d : Goal ι) (w : Finset ι) : (cards ι).prior d {w} ≠ 0 :=
  uniformOn_univ_singleton_ne_zero w

private theorem integral_cardUtility_go (π : Measure (Finset ι)) :
    ∫ w, (cards ι).utility d w .go ∂π = 5 * π.real d.target :=
  (integral_indicator_const 5 (Set.toFinite _).measurableSet).trans (mul_comm _ _)

private theorem integral_cardUtility_stay (π : Measure (Finset ι)) [IsProbabilityMeasure π] :
    ∫ w, (cards ι).utility d w .stay ∂π = 5 * (1 - π.real d.target) := by
  rw [← probReal_compl_eq_one_sub (Set.toFinite _).measurableSet]
  exact (integral_indicator_const 5 (Set.toFinite _).measurableSet).trans (mul_comm _ _)

private theorem act_eq (c : Act) : c = .go ∨ c = .stay := by cases c <;> simp

private theorem value_cards (π : Measure (Finset ι)) [IsProbabilityMeasure π] :
    value ((cards ι).utility d) αℵ π = 5 / 2 + 5 * ((2 * π.real d.target - 1) *
      (Real.sigmoid (αℵ * 5 * (2 * π.real d.target - 1)) - 1 / 2)) :=
  value_of_integral_eq (by decide) act_eq (integral_cardUtility_go π)
    (integral_cardUtility_stay π)

private theorem isProbabilityMeasure_listener_cards (hr : ((cards ι).response r).Nonempty) :
    IsProbabilityMeasure (RSA.listener ((cards ι).prior d) (cards ι).R0' r) :=
  let ⟨w₀, hw₀⟩ := hr
  RSA.isProbabilityMeasure_listener_of_ne_zero ((cards ι).prior d) (cards ι).R0'
    (cards_prior_ne_zero d w₀) ((cards ι).R0'_apply_singleton_ne_zero_iff.2 hw₀)

-- §3a
theorem value_lt_value_iff_abs (hα : 0 < αℵ) {r' : Resp ι}
    (hr : ((cards ι).response r).Nonempty) (hr' : ((cards ι).response r').Nonempty) :
    value ((cards ι).utility d) αℵ (RSA.listener ((cards ι).prior d) (cards ι).R0' r) <
        value ((cards ι).utility d) αℵ (RSA.listener ((cards ι).prior d) (cards ι).R0' r') ↔
      |2 * (RSA.listener ((cards ι).prior d) (cards ι).R0' r).real d.target - 1| <
        |2 * (RSA.listener ((cards ι).prior d) (cards ι).R0' r').real d.target - 1| := by
  have := isProbabilityMeasure_listener_cards (d := d) hr
  have := isProbabilityMeasure_listener_cards (d := d) hr'
  exact value_lt_value_iff hα (by norm_num) (by decide) act_eq (integral_cardUtility_go _)
    (integral_cardUtility_stay _) (integral_cardUtility_go _) (integral_cardUtility_stay _)

theorem value_of_mem_polar (hr : ((cards ι).response r).Nonempty)
    (h : (cards ι).response r ∈ polar d.target) (αℵ : ℝ) :
    value ((cards ι).utility d) αℵ (RSA.listener ((cards ι).prior d) (cards ι).R0' r) =
      5 * Real.sigmoid (αℵ * 5) := by
  have := isProbabilityMeasure_listener_cards (d := d) hr
  have hnull := (cards ι).listener_R0'_apply_compl_response (d := d) r
  have hmeas : MeasurableSet d.target := (Set.toFinite _).measurableSet
  rcases mem_polar.1 h with h | h
  · rw [value_cards, measureReal_def, (prob_compl_eq_zero_iff hmeas).1
      (measure_mono_null (Set.compl_subset_compl.2 h) hnull), ENNReal.toReal_one,
      show αℵ * 5 * (2 * 1 - 1) = αℵ * 5 by ring]
    ring
  · rw [value_cards, measureReal_def, measure_mono_null (Set.subset_compl_comm.1 h) hnull,
      ENNReal.toReal_zero, show αℵ * 5 * (2 * 0 - 1) = -(αℵ * 5) by ring, Real.sigmoid_neg]
    ring

-- §3a
theorem value_lt_of_notMem_polar (hα : 0 < αℵ) (h : (cards ι).response r ∉ polar d.target) :
    value ((cards ι).utility d) αℵ (RSA.listener ((cards ι).prior d) (cards ι).R0' r) <
      5 * Real.sigmoid (αℵ * 5) := by
  rw [mem_polar, not_or, Set.not_subset, Set.not_subset] at h
  obtain ⟨⟨w₂, hw₂, hw₂G⟩, w₁, hw₁, hw₁G⟩ := h
  have hπ := cards_prior_ne_zero d
  have := isProbabilityMeasure_listener_cards (d := d) ⟨w₁, hw₁⟩
  have hmeas : MeasurableSet d.target := (Set.toFinite _).measurableSet
  have hpos {s : Set (Finset ι)} {w : Finset ι} (hw : w ∈ (cards ι).response r) (hs : w ∈ s) :
      0 < (RSA.listener ((cards ι).prior d) (cards ι).R0' r).real s :=
    ENNReal.toReal_pos (fun h0 ↦ ((cards ι).listener_R0'_apply_singleton_ne_zero_iff hπ).2 hw
      (measure_mono_null (Set.singleton_subset_iff.2 hs) h0)) (measure_ne_top _ _)
  have hp := hpos hw₁ (Set.notMem_compl_iff.1 hw₁G)
  have hp' := hpos (s := d.targetᶜ) hw₂ hw₂G
  rw [probReal_compl_eq_one_sub hmeas] at hp'
  have key := (mul_sigmoid_sub_half_lt_iff (y := 1) (mul_pos hα (by norm_num : (0 : ℝ) < 5))).2
    (show |2 * (RSA.listener ((cards ι).prior d) (cards ι).R0' r).real d.target - 1| < |1| by
      rw [abs_one, abs_lt]; constructor <;> linarith)
  rw [value_cards]
  simp only [mul_one, one_mul] at key
  linarith

theorem value_exhaustive (d : Goal ι) (w : Finset ι) (αℵ : ℝ) :
    value ((cards ι).utility d) αℵ
        (RSA.listener ((cards ι).prior d) (cards ι).R0' (.exhaustive w)) =
      5 * Real.sigmoid (αℵ * 5) := by
  refine value_of_mem_polar (r := .exhaustive w) ⟨w, Set.mem_singleton w⟩ (mem_polar.2 ?_) αℵ
  by_cases h : w ∈ d.target
  · exact .inl (Set.singleton_subset_iff.2 h)
  · exact .inr (Set.singleton_subset_iff.2 h)

-- (3)
theorem value_yes_eq_value_exhaustive {a : ι} {C : Finset ι} (ha : a ∈ C) (w : Finset ι)
    (αℵ : ℝ) :
    value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.polar {a} true)) =
      value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.exhaustive w)) := by
  rw [value_exhaustive]
  refine value_of_mem_polar ⟨{a}, mem_response_polar_true.2 (by simp)⟩
    (mem_polar.2 (.inl fun w' hw' ↦ ?_)) αℵ
  obtain ⟨x, hx⟩ := mem_response_polar_true.1 hw'
  rw [Finset.mem_inter, Finset.mem_singleton] at hx
  exact ⟨a, Finset.mem_inter.2 ⟨ha, hx.1 ▸ hx.2⟩⟩

/-- In (5), *yes* to the general question leaves a questioner who holds some but not all of the
cards a decision problem of lower value than the exhaustive list does. -/
theorem value_generalYes_lt_value_exhaustive (hα : 0 < αℵ) {C : Finset ι} (hC : C.Nonempty)
    (hC' : Cᶜ.Nonempty) (w : Finset ι) :
    value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.polar univ true)) <
      value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.exhaustive w)) := by
  rw [value_exhaustive]
  refine value_lt_of_notMem_polar hα fun h ↦ ?_
  rcases mem_polar.1 h with h | h
  · have : (C ∩ Cᶜ).Nonempty := h (mem_response_polar_true.2 (by simpa using hC'))
    simp at this
  · exact h (mem_response_polar_true.2 (by simpa using hC))
      (show (C ∩ C).Nonempty by simpa using hC)

-- (4)
theorem value_no_lt_value_exhaustive (hα : 0 < αℵ) {a : ι} {C : Finset ι} (ha : a ∈ C)
    (hC : C ≠ {a}) (w : Finset ι) :
    value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.polar {a} false)) <
      value ((cards ι).utility (.ownCards C)) αℵ
        (RSA.listener ((cards ι).prior (.ownCards C)) (cards ι).R0' (.exhaustive w)) := by
  obtain ⟨x, hx, hxa⟩ : ∃ x ∈ C, x ≠ a := by
    by_contra! h
    exact hC (Finset.eq_singleton_iff_unique_mem.2 ⟨ha, h⟩)
  rw [value_exhaustive]
  refine value_lt_of_notMem_polar hα fun h ↦ ?_
  rcases mem_polar.1 h with h | h
  · have : (C ∩ ∅).Nonempty := h (mem_response_polar_false.2 (by simp))
    simp at this
  · exact h (mem_response_polar_false.2 (by simp))
      (show (C ∩ C.erase a).Nonempty from
        ⟨x, Finset.mem_inter.2 ⟨hx, Finset.mem_erase.2 ⟨hxa, hx⟩⟩⟩)

theorem respondent_cards_dirac_apply_singleton (p : Params) (hβ : p.β < 1) (hα : 0 < p.αR)
    (πD : Measure (Goal ι)) [IsFiniteMeasure πD] (hd : πD {d} ≠ 0) {w q : Finset ι}
    (hf : w ∉ (cards ι).response r) : (cards ι).respondent p πD (.dirac w) q {r} = 0 :=
  (cards ι).respondent_truthful p πD hβ hα hd (by simp) hf

end Value

end HawkinsEtAl2025
