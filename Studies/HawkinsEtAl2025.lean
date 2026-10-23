module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Linglib.Data.Examples.HawkinsEtAl2025
public import Linglib.Pragmatics.RSA.Basic
public import Linglib.Semantics.Questions.Hamblin

/-!
# Hawkins, Tsvilodub, Bergey, Goodman and Franke (2025): Relevant answers to polar questions

The PRIOR-PQ model of [hawkins-etal-2025] explains the answers to polar questions by the
questioner's decision problem. A base respondent gives a random true and safe response, one that
resolves the question for anyone who knows it. The questioner asks the question whose answers
most raise the value of its decision problem, and a pragmatic respondent infers the decision
problem from the question and trades informativity against relevance to it.

## Main statements

* `safe_iff_mem_polar`: a response is safe exactly when it resolves the polar question.
* `questionScore_eq_valueOfInformation`: the questioner scores a question by its value of
  information.
* `listener_R0_real_lt_iff`: by the size principle, an answer favours the worlds with fewer true
  and safe alternatives.
* `goalPosterior_real_lt_iff`: the respondent favours the decision problems under which the
  question was likelier.
* `respondent_truthful`, `respondent_apply_singleton_ne_zero_of_beta_eq_one`: informativity
  keeps the respondent truthful, and relevance alone does not.
* `mention_safe_iff`: in the credit-card case study, naming a card is safe exactly when it was
  asked about.
* `yes_value_eq_exhaustive`, `generalYes_posterior_ne_zero`: after "yes" to a question about a
  card the questioner holds the exhaustive list adds no value, while after "yes" to the general
  question the questioner stays uncertain.

## Implementation notes

* The questioner hearing a response and the respondent hearing a question are `RSA.listener`s of
  the base respondent and of the questioner, so a response no world produces leaves the zero
  measure; the questioner and the pragmatic respondent are `Kernel.softmax` kernels.
* The paper defines safety as "not knowing the answer to `q` entails not knowing whether `r`",
  under which its safe example "Yes, we take Visa" to "Do you take Visa or Mastercard?" would be
  unsafe. `Safe` takes the reading "not knowing `r`" that the examples force, and applies to a
  mention apart from the polar answer it accompanies ("No, but we take American Express").
* The displayed respondent utility puts the questioner's updated belief first in the divergence.
  The file follows the prose, which puts the respondent's belief first, since only that order
  enforces truthfulness; in the displayed order a respondent who knows the world, as in the case
  study, finds every response short of a world-identifying one infinitely uninformative.
* The paper replaces `R0` by the truth-only `R0'` in the questioner's update as the respondent
  models it, since under `R0` the update is undefined at unsafe responses. The display primes
  only the informativity term; the file uses `R0'` for relevance too.
* The softmax value of a decision problem is not convex in the belief, so a question can have
  negative value of information.

## TODO

* The predicted rates of exhaustive answers, highest after a polar question about an unavailable
  card, then after the general question, then after a polar question about an available card,
  which depend on the fitted parameters.
* The value comparison behind the general question, that after "yes" the decision problem of a
  questioner holding American Express has lower value than after the exhaustive list.
* The iced tea and blanket case studies, with the elicited utilities.

## References

* [hawkins-etal-2025]
-/

@[expose] public section

namespace HawkinsEtAl2025

open MeasureTheory ProbabilityTheory InformationTheory Finset Question
open scoped ENNReal

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

/-- By the size principle (§2b), between two worlds of equal prior at which a response is true
and safe, the questioner comes to favour the world with fewer true and safe alternatives. -/
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

variable [Fintype A]

/-- The policy (2.2) of a decision problem under beliefs `π` is a softmax over expected utility
with rationality `αℵ`. -/
noncomputable def policy (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) : A → ℝ :=
  Real.softmax (αℵ • fun a ↦ ∫ w, U w a ∂π)

/-- The value `V(D)` of a decision problem is the expected utility of following its policy. -/
noncomputable def value (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) : ℝ :=
  ∑ a, policy U αℵ π a * ∫ w, U w a ∂π

theorem value_eq_of_ae {π π' : Measure W} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    {U : W → A → ℝ} {c : A → ℝ} (αℵ : ℝ) (hU : ∀ᵐ w ∂π, U w = c) (hU' : ∀ᵐ w ∂π', U w = c) :
    value U αℵ π = value U αℵ π' := by
  have h {ν : Measure W} [IsProbabilityMeasure ν] (hν : ∀ᵐ w ∂ν, U w = c) (a : A) :
      ∫ w, U w a ∂ν = c a := by
    rw [integral_congr_ae (hν.mono fun w hw ↦ congrFun hw a)]
    simp
  simp only [value, policy, h hU, h hU']

variable [Fintype W] [MeasurableSingletonClass W] [Finite R] [MeasurableSingletonClass R]
  (p : Params)

/-- The expected value to the questioner of asking `q` under the decision problem `d` (2.3) is
the value of `d` updated (2.4) by the base respondent's answer, less the weighted cost. -/
noncomputable def Model.questionScore (d : D) (q : Q) : ℝ :=
  ∫ r, (value (m.utility d) p.αℵ (RSA.listener (m.prior d) (m.R0 q) r) - p.wc * m.cost r)
    ∂(m.R0 q ∘ₘ m.prior d)

/-- The question score is the value of information of the question under the policy value, plus
the value of the prior, less the expected cost. -/
theorem Model.questionScore_eq_valueOfInformation [StandardBorelSpace W] [Nonempty W] (d : D)
    [IsFiniteMeasure (m.prior d)] (q : Q) :
    m.questionScore p d q =
      valueOfInformation (value (m.utility d) p.αℵ) (m.R0 q) (m.prior d) +
        value (m.utility d) p.αℵ (m.prior d) - p.wc * ∫ r, m.cost r ∂(m.R0 q ∘ₘ m.prior d) := by
  have h : ∀ᵐ r ∂(m.R0 q ∘ₘ m.prior d),
      RSA.listener (m.prior d) (m.R0 q) r = ((m.R0 q)†(m.prior d)) r :=
    ae_iff_of_countable.2 fun r hr ↦ RSA.listener_apply_eq_posterior _ _ hr
  rw [Model.questionScore, integral_sub .of_finite .of_finite, integral_const_mul,
    valueOfInformation, integral_congr_ae (h.mono fun r hr ↦ congrArg _ hr)]
  ring

variable [MeasurableSpace Q] [Fintype Q] [MeasurableSingletonClass Q] [MeasurableSpace D]
  [Countable D] [MeasurableSingletonClass D]

/-- The questioner (2.3) soft-maximizes the question score with rationality `αQ`. -/
noncomputable def Model.questioner : Kernel D Q :=
  Kernel.softmax fun d q ↦ ((p.αQ * m.questionScore p d q : ℝ) : EReal)

instance : IsFiniteKernel (m.questioner p) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty Q] : IsMarkovKernel (m.questioner p) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary Q, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

theorem Model.questioner_apply_singleton_ne_zero (d : D) (q : Q) : m.questioner p d {q} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero (EReal.coe_ne_bot _) fun _ ↦ EReal.coe_ne_top _

end Questioner

/-! ### The pragmatic respondent (§2c) -/

section Respondent

variable [Fintype A] [Fintype W] [MeasurableSingletonClass W] [Fintype R]
  [MeasurableSingletonClass R] (p : Params) [MeasurableSpace Q] [Fintype Q]
  [MeasurableSingletonClass Q] [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
  (πD : Measure D)

/-- The respondent's belief about the decision problem after hearing `q` is that of a listener
to the questioner at the prior `πD`, `π(D ∣ q) ∝ Q(q ∣ D) π(D)`. -/
noncomputable def Model.goalPosterior : Kernel Q D := RSA.listener πD (m.questioner p)

instance : IsFiniteKernel (m.goalPosterior p πD) :=
  inferInstanceAs (IsFiniteKernel (RSA.listener _ _))

/-- Between decision problems of equal prior, the respondent comes to favour the one under which
the question was the likelier, so a question signals the goal. -/
theorem Model.goalPosterior_real_lt_iff [IsFiniteMeasure πD] (q : Q) {d₁ d₂ : D}
    (hp : πD {d₁} = πD {d₂}) (hpos : πD {d₁} ≠ 0) :
    (m.goalPosterior p πD q).real {d₁} < (m.goalPosterior p πD q).real {d₂} ↔
      (m.questioner p d₁).real {q} < (m.questioner p d₂).real {q} := by
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

/-- Action relevance alone does not enforce truthfulness (§2c), since at `β = 1` the respondent
gives every response, false ones included, positive probability. -/
theorem Model.respondent_apply_singleton_ne_zero_of_beta_eq_one (hβ : p.β = 1)
    (πW : Measure W) (q : Q) (r : R) : m.respondent p πD πW q {r} ≠ 0 := by
  have h (r : R) : ∃ x : ℝ, (p.αR : EReal) * m.respondentScore p πD πW q r = x :=
    ⟨_, by rw [m.respondentScore_of_beta_eq_one p πD hβ, ← EReal.coe_mul]⟩
  exact Kernel.softmax_apply_singleton_ne_zero
    (by obtain ⟨x, hx⟩ := h r; exact hx ▸ EReal.coe_ne_bot x)
    fun r' ↦ by obtain ⟨x, hx⟩ := h r'; exact hx ▸ EReal.coe_ne_top x

/-- Informativity enforces truthfulness (§2c). When `β < 1`, a respondent who considers some
decision problem possible never gives a response that is false at a world it considers
possible. -/
theorem Model.respondent_truthful [IsFiniteMeasure πD] (hβ : p.β < 1) (hα : 0 < p.αR)
    {πW : Measure W} {q : Q} {r : R} {d : D} (hd : πD {d} ≠ 0) {w : W} (hw : πW {w} ≠ 0)
    (hf : w ∉ m.response r) : m.respondent p πD πW q {r} = 0 := by
  have hkl : klDiv πW (RSA.listener (m.prior d) m.R0' r) = ∞ :=
    klDiv_of_not_ac fun hac ↦ hw (hac (RSA.listener_apply_singleton_eq_zero
      (not_not.1 (mt m.R0'_apply_singleton_ne_zero_iff.1 hf))))
  have hgp : m.goalPosterior p πD q {d} ≠ 0 :=
    RSA.listener_apply_singleton_ne_zero hd (m.questioner_apply_singleton_ne_zero p d q)
  have hint : ∫⁻ d', klDiv πW (RSA.listener (m.prior d') m.R0' r) ∂(m.goalPosterior p πD q) =
      ∞ := by
    rw [lintegral_countable']
    exact ENNReal.tsum_eq_top_of_eq_top ⟨d, by rw [hkl, ENNReal.top_mul hgp]⟩
  refine Kernel.softmax_apply_singleton_eq_zero ?_
  simp only [Model.respondentScore, hint, EReal.coe_ennreal_top, EReal.neg_top,
    EReal.coe_mul_bot_of_pos (sub_pos.2 hβ), EReal.bot_add, EReal.coe_mul_bot_of_pos hα]

end Respondent

/-! ### Case study 1: credit cards (§3a) -/

/-- A card is one of the three credit cards of §3a. -/
inductive Card where
  | amex
  | mastercard
  | carteBlanche
  deriving DecidableEq, Fintype, Repr

/-- The questioner either stays or goes. -/
inductive Act where
  | stay
  | go
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- A response is a polar answer to whether any card of `S` is accepted, the mention of some
accepted cards, or the exhaustive list of the accepted cards. -/
inductive Resp where
  | polar (S : Finset Card) (b : Bool)
  | mention (T : Finset Card)
  | exhaustive (T : Finset Card)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Resp := ⊤

instance : MeasurableSpace (Finset Card) := ⊤

instance : DiscreteMeasurableSpace (Finset Card) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

/-- The decision problem `U1` turns on whether any of the questioner's cards `C` is accepted,
and `U2` on whether any card is accepted. -/
inductive Goal where
  | ownCards (C : Finset Card)
  | anyCard
  deriving DecidableEq, Fintype

/-- The utility of §3a is 5 for going when a relevant card is accepted or staying when none is,
and 0 otherwise. -/
def cardUtility : Goal → Finset Card → Act → ℝ
  | .ownCards C, w, .go => if (C ∩ w).Nonempty then 5 else 0
  | .ownCards C, w, .stay => if (C ∩ w).Nonempty then 0 else 5
  | .anyCard, w, .go => if w.Nonempty then 5 else 0
  | .anyCard, w, .stay => if w.Nonempty then 0 else 5

/-- `r.denote` is the set of worlds at which the response `r` is true. -/
def Resp.denote : Resp → Set (Finset Card)
  | .polar S b => {w | (S ∩ w).Nonempty ↔ b = true}
  | .mention T => {w | T ⊆ w}
  | .exhaustive T => {T}

instance : ∀ r, DecidablePred (· ∈ Resp.denote r)
  | .polar S b, w => inferInstanceAs (Decidable ((S ∩ w).Nonempty ↔ b = true))
  | .mention T, w => inferInstanceAs (Decidable (T ⊆ w))
  | .exhaustive T, w => inferInstanceAs (Decidable (w = T))

/-- In the credit-card model, a question asks whether any card of a set is accepted, worlds are
the sets of accepted cards, priors are uniform over the eight worlds, and a response costs the
cards it mentions. -/
noncomputable def cards : Model (Finset Card) (Finset Card) Resp Act Goal where
  question S := {w | (S ∩ w).Nonempty}
  response := Resp.denote
  utility := cardUtility
  prior _ := uniformOn Set.univ
  cost
    | .polar _ _ => 0
    | .mention T => T.card
    | .exhaustive T => T.card

instance (S : Finset Card) : DecidablePred (· ∈ cards.question S) :=
  fun w ↦ inferInstanceAs (Decidable (S ∩ w).Nonempty)

instance (r : Resp) : DecidablePred (· ∈ cards.response r) :=
  inferInstanceAs (DecidablePred (· ∈ Resp.denote r))

instance (d : Goal) : IsProbabilityMeasure (cards.prior d) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

theorem polar_exhaustive_safe :
    (∀ S b, Safe (cards.question S) (cards.response (.polar S b))) ∧
      ∀ S T, Safe (cards.question S) (cards.response (.exhaustive T)) := by
  decide

/-- Mentioning accepted cards is safe for a question exactly when one of them was asked about.
Naming one of the two cards asked about is safe, as in (1) (`Examples.ex1`), and naming a third
card is not, as in (2) (`Examples.ex2`). -/
theorem mention_safe_iff (S T : Finset Card) (hS : S.Nonempty) :
    Safe (cards.question S) (cards.response (.mention T)) ↔ (T ∩ S).Nonempty := by
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

theorem trueSafe_nonempty (w q : Finset Card) : (cards.trueSafe w q).Nonempty :=
  ⟨.polar q (decide (q ∩ w).Nonempty),
    show (q ∩ w).Nonempty ↔ decide (q ∩ w).Nonempty = true by simp,
    polar_exhaustive_safe.1 q _⟩

instance (q : Finset Card) : IsMarkovKernel (cards.R0 q) :=
  cards.isMarkovKernel_R0 fun w ↦ trueSafe_nonempty w q

private theorem cards_prior_ne_zero (d : Goal) (w : Finset Card) : cards.prior d {w} ≠ 0 :=
  uniformOn_univ_singleton_ne_zero w

/-- In (3) (`Examples.ex3`), for a questioner holding the card asked about, the value of the
decision problem after the answer "yes" already equals its value after the exhaustive list,
since every world compatible with either answer accepts a card the questioner holds; only the
cost separates the two answers. -/
theorem yes_value_eq_exhaustive (C w : Finset Card) (hC : .amex ∈ C) (hw : .amex ∈ w)
    (αℵ : ℝ) :
    value (cards.utility (.ownCards C)) αℵ
        (RSA.listener (cards.prior (.ownCards C)) cards.R0' (.polar {.amex} true)) =
      value (cards.utility (.ownCards C)) αℵ
        (RSA.listener (cards.prior (.ownCards C)) cards.R0' (.exhaustive w)) := by
  have hπ := cards_prior_ne_zero (.ownCards C)
  have hyes : w ∈ cards.response (.polar {.amex} true) := by
    show ({Card.amex} ∩ w).Nonempty ↔ true = true
    simp [Finset.singleton_inter_of_mem hw]
  have := RSA.isProbabilityMeasure_listener_of_ne_zero (cards.prior (.ownCards C)) cards.R0'
    (hπ w) (cards.R0'_apply_singleton_ne_zero_iff.2 hyes)
  have := RSA.isProbabilityMeasure_listener_of_ne_zero (cards.prior (.ownCards C)) cards.R0'
    (hπ w) ((cards.R0'_apply_singleton_ne_zero_iff (r := .exhaustive w)).2 rfl)
  have hgo (w' : Finset Card) (hw' : Card.amex ∈ w') :
      cards.utility (.ownCards C) w' = fun a ↦ match a with | .go => 5 | .stay => 0 :=
    funext fun a ↦ by
      have hCw : (C ∩ w').Nonempty := ⟨.amex, Finset.mem_inter.2 ⟨hC, hw'⟩⟩
      cases a <;> simp [cards, cardUtility, hCw]
  refine value_eq_of_ae αℵ (ae_iff_of_countable.2 fun w' hw' ↦ hgo w' ?_)
    (ae_iff_of_countable.2 fun w' hw' ↦ hgo w' ?_)
  · obtain ⟨x, hx⟩ : ({Card.amex} ∩ w').Nonempty :=
      ((cards.listener_R0'_apply_singleton_ne_zero_iff hπ).1 hw').2 rfl
    rw [Finset.mem_inter, Finset.mem_singleton] at hx
    exact hx.1 ▸ hx.2
  · exact (Set.mem_singleton_iff.1 ((cards.listener_R0'_apply_singleton_ne_zero_iff hπ).1 hw')) ▸ hw

/-- In (5) (`Examples.ex5`), after "yes" to the general question, a world accepting only
MasterCard keeps positive posterior, so a questioner holding American Express remains
uncertain; after "yes" to the question about American Express it does not. -/
theorem generalYes_posterior_ne_zero :
    RSA.listener (cards.prior (.ownCards {.amex})) cards.R0' (.polar univ true)
        {{.mastercard}} ≠ 0 ∧
      RSA.listener (cards.prior (.ownCards {.amex})) cards.R0' (.polar {.amex} true)
        {{.mastercard}} = 0 := by
  have hπ := cards_prior_ne_zero (.ownCards {.amex})
  have h₁ : {.mastercard} ∈ cards.response (.polar univ true) := by decide
  have h₂ : {.mastercard} ∉ cards.response (.polar {.amex} true) := by decide
  exact ⟨(cards.listener_R0'_apply_singleton_ne_zero_iff hπ).2 h₁,
    not_not.1 fun h ↦ h₂ ((cards.listener_R0'_apply_singleton_ne_zero_iff hπ).1 h)⟩

end HawkinsEtAl2025
