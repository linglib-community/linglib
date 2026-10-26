module

public import Linglib.Core.Probability.ConditionalProbability
public import Linglib.Core.Probability.Independence.Basic
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Decision-Theoretic Semantics

This file sets up the core of Merin's Decision-Theoretic Semantics (DTS) [merin-1999-relevance]:
meaning explicated through the *signed relevance* of a proposition E to one side H of a
dichotomic issue {H, ¬H}, the log Bayes factor log (P(E∣H) / P(E∣¬H)).

Each side of the issue conditions the prior on itself (`Context.conditional`), and the Bayes
factor of E is the ratio of the two conditional probabilities of E. The paper's applications to
*or*, *but*, *even*, and *also* are in `Studies/Merin1999a.lean`.

## Main definitions

- `Context`: a dichotomic issue (`topic : Set W`, with its measurability witness) plus a prior
  (Partial Definition 6); `Context.Nondegenerate` marks a live issue
- `bayesFactor`: the ratio P(E∣H) / P(E∣¬H)
- `relevance`: its logarithm, Merin's relevance of E to H (Definition 4)
- `posRelevant`, `negRelevant`, `irrelevant`: the relevance signs (Definition 5), and
  `relevanceSign`, the sign of P(E∣H) − P(E∣¬H), which swapping the issue negates
- `hContrary`: A and B have opposite relevance signs
- `CondIndepIssue`: independence of A and B conditionally on H and on ¬H (Definition 9), the
  content of the Conditional Independence Presumption (Hypothesis 2)

## Main results

- `posRelevant_iff_cond_lt`: E confirms H iff H makes E more probable than ¬H does
- `sign_reversal`: BF_H(E) · BF_¬H(E) = 1 (Corollary 3)
- `relevance_eq_neg_log_sub_neg_log`: relevance is the differential of conditional
  informativeness (Fact 2)
- `CondIndepIssue.bayesFactor_inter`: under issue-conditional independence, BF(A∧B) =
  BF(A) · BF(B) (Fact 5); Theorem 6a's order of conjunction, disjuncts, and disjunction is
  `CondIndepIssue.max_bayesFactor_lt_inter`, `.bayesFactor_union_lt_max`, and
  `.one_lt_bayesFactor_union`

## Implementation notes

The context stores H, with ¬H implicit. Relevance is carried by `bayesFactor` in `ℝ≥0∞`,
where the boundary cases P(E∣¬H) = 0 and P(E∣H) = 0 take their true values `∞` and `0`
(Merin's r = ±∞); `relevance` is the real logarithm, which sends both to `0`, so sign and
order facts are stated on `bayesFactor`.

## References

* [merin-1999-relevance]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS

/-! ### Contexts -/

/-- A DTS context (Partial Definition 6) consists of the proposition H at issue, with ¬H
implicit, and a prior over worlds. -/
structure Context (W : Type*) [MeasurableSpace W] where
  /-- The hypothesis H. -/
  topic : Set W
  /-- Measurability of the topic, so that conditioning on H and ¬H is well-behaved. -/
  topicMeasurable : MeasurableSet topic
  /-- Prior measure over worlds. Conditioning normalizes, so an unnormalized prior (e.g.
  `Measure.count`) induces the same relevance facts as its normalization. -/
  prior : Measure W

variable {W : Type*} [MeasurableSpace W]

/-- Swapping the issue replaces H with ¬H. -/
def swapIssue (ctx : Context W) : Context W :=
  { topic := ctx.topicᶜ,
    topicMeasurable := ctx.topicMeasurable.compl,
    prior := ctx.prior }

/-- The prior conditioned on H (at `true`) or on ¬H (at `false`). -/
noncomputable def Context.conditional (ctx : Context W) : Bool → Measure W
  | true => ctx.prior[|ctx.topic]
  | false => ctx.prior[|ctx.topicᶜ]

@[simp] theorem Context.conditional_true (ctx : Context W) :
    ctx.conditional true = ctx.prior[|ctx.topic] := rfl

@[simp] theorem Context.conditional_false (ctx : Context W) :
    ctx.conditional false = ctx.prior[|ctx.topicᶜ] := rfl

/-- An issue is live when both sides carry mass. Merin's dichotomic issue {H, ¬H}
presupposes a genuine question, so the degenerate cases are excluded at the
level of the object rather than per theorem. -/
class Context.Nondegenerate (ctx : Context W) : Prop where
  topic_ne_zero : ctx.prior ctx.topic ≠ 0
  compl_ne_zero : ctx.prior ctx.topicᶜ ≠ 0

instance (ctx : Context W) [h : ctx.Nondegenerate] : (swapIssue ctx).Nondegenerate :=
  ⟨h.compl_ne_zero, by simpa [swapIssue, compl_compl] using h.topic_ne_zero⟩

theorem Context.isProbabilityMeasure_conditional (ctx : Context W)
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] (θ : Bool) :
    IsProbabilityMeasure (ctx.conditional θ) := by
  cases θ
  · exact cond_isProbabilityMeasure Context.Nondegenerate.compl_ne_zero
  · exact cond_isProbabilityMeasure Context.Nondegenerate.topic_ne_zero

instance (ctx : Context W) (θ : Bool) :
    IsZeroOrProbabilityMeasure (ctx.conditional θ) := by
  cases θ <;> · rw [Context.conditional]; infer_instance

/-! ### Bayes factor and relevance -/

/-- The Bayes factor P(E∣H) / P(E∣¬H), in `ℝ≥0∞`. Total division gives the boundary cases
their true values: P(E∣¬H) = 0 with P(E∣H) > 0 is `∞` (infinitely strong evidence for H), and
0/0 = 0. -/
noncomputable def bayesFactor (ctx : Context W) (e : Set W) : ℝ≥0∞ :=
  ctx.conditional true e / ctx.conditional false e

theorem bayesFactor_def (ctx : Context W) (e : Set W) :
    bayesFactor ctx e = ctx.prior[|ctx.topic] e / ctx.prior[|ctx.topicᶜ] e := rfl

theorem toReal_bayesFactor (ctx : Context W) (e : Set W) :
    (bayesFactor ctx e).toReal = (ctx.prior[|ctx.topic]).real e / (ctx.prior[|ctx.topicᶜ]).real e :=
  ENNReal.toReal_div _ _

/-- Merin's relevance of E to H (Definition 4) is the log Bayes factor, real-valued through
`ENNReal.toReal`. The boundary cases `0` and `∞` both land at `Real.log 0 = 0`,
so sign and order facts are read off `bayesFactor` itself
(`posRelevant_iff_one_lt_toReal`, `relevance_lt_relevance`). -/
noncomputable def relevance (ctx : Context W) (e : Set W) : ℝ :=
  Real.log (bayesFactor ctx e).toReal

theorem bayesFactor_ne_zero {ctx : Context W} {e : Set W} (h : ctx.prior[|ctx.topic] e ≠ 0) :
    bayesFactor ctx e ≠ 0 := by
  rw [bayesFactor_def]
  exact ENNReal.div_ne_zero.mpr ⟨h, measure_ne_top _ _⟩

theorem bayesFactor_ne_top {ctx : Context W} {e : Set W} (h : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    bayesFactor ctx e ≠ ⊤ := by
  rw [bayesFactor_def]
  exact (ENNReal.div_lt_top (measure_ne_top _ _) h).ne

theorem relevance_lt_relevance {ctx : Context W} {e₁ e₂ : Set W} (h₁ : bayesFactor ctx e₁ ≠ 0)
    (h₂ : bayesFactor ctx e₂ ≠ ⊤) (h : bayesFactor ctx e₁ < bayesFactor ctx e₂) :
    relevance ctx e₁ < relevance ctx e₂ :=
  Real.log_lt_log (ENNReal.toReal_pos h₁ (ne_top_of_lt h))
    ((ENNReal.toReal_lt_toReal (ne_top_of_lt h) h₂).mpr h)

/-- E is positively relevant to H, and so confirms it, when BF > 1 (Definition 5). -/
def posRelevant (ctx : Context W) (e : Set W) : Prop :=
  1 < bayesFactor ctx e

theorem posRelevant_iff_one_lt_toReal {ctx : Context W} {e : Set W}
    (ht : bayesFactor ctx e ≠ ⊤) : posRelevant ctx e ↔ 1 < (bayesFactor ctx e).toReal := by
  rw [posRelevant, ← ENNReal.toReal_lt_toReal ENNReal.one_ne_top ht, ENNReal.toReal_one]

/-- E is negatively relevant to H, and so disconfirms it, when BF < 1 (Definition 5). -/
def negRelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e < 1

theorem negRelevant_iff_toReal_lt_one {ctx : Context W} {e : Set W}
    (ht : bayesFactor ctx e ≠ ⊤) : negRelevant ctx e ↔ (bayesFactor ctx e).toReal < 1 := by
  rw [negRelevant, ← ENNReal.toReal_lt_toReal ht ENNReal.one_ne_top, ENNReal.toReal_one]

/-- E is irrelevant to H, neither confirming nor disconfirming it, when BF = 1 (Definition 5). -/
def irrelevant (ctx : Context W) (e : Set W) : Prop :=
  bayesFactor ctx e = 1

/-- A and B are H-contrary: they have opposite nonzero relevance signs, one supporting H and
the other ¬H. -/
def hContrary (ctx : Context W) (a b : Set W) : Prop :=
  (posRelevant ctx a ∧ negRelevant ctx b) ∨ (negRelevant ctx a ∧ posRelevant ctx b)

theorem bayesFactor_swapIssue (ctx : Context W) (e : Set W) :
    bayesFactor (swapIssue ctx) e =
      ctx.prior[|ctx.topicᶜ] e / ctx.prior[|ctx.topic] e := by
  simp [bayesFactor, swapIssue, compl_compl]

/-- E confirms H exactly when H makes E more probable than ¬H does. -/
theorem posRelevant_iff_cond_lt {ctx : Context W} {e : Set W} :
    posRelevant ctx e ↔ ctx.prior[|ctx.topicᶜ] e < ctx.prior[|ctx.topic] e := by
  rw [posRelevant, bayesFactor_def]
  rcases eq_or_ne (ctx.prior[|ctx.topicᶜ] e) 0 with h | h
  · rcases eq_or_ne (ctx.prior[|ctx.topic] e) 0 with h' | h'
    · simp [h, h']
    · simp [h, h', ENNReal.div_zero h', pos_iff_ne_zero]
  · rw [ENNReal.lt_div_iff_mul_lt (.inl h) (.inl (measure_ne_top _ _)), one_mul]

theorem negRelevant_iff_cond_lt {ctx : Context W} {e : Set W}
    (h : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    negRelevant ctx e ↔ ctx.prior[|ctx.topic] e < ctx.prior[|ctx.topicᶜ] e := by
  rw [negRelevant, bayesFactor_def, ENNReal.div_lt_iff (.inl h) (.inl (measure_ne_top _ _)),
    one_mul]

/-- The relevance sign of E for H, the sign of P(E∣H) − P(E∣¬H): `1` when E is positively
relevant to H and `-1` when it is negatively relevant (Definition 5). -/
noncomputable def relevanceSign (ctx : Context W) (e : Set W) : SignType :=
  SignType.sign ((ctx.prior[|ctx.topic]).real e - (ctx.prior[|ctx.topicᶜ]).real e)

theorem relevanceSign_swapIssue (ctx : Context W) (e : Set W) :
    relevanceSign (swapIssue ctx) e = -relevanceSign ctx e := by
  rw [relevanceSign, relevanceSign, ← Left.sign_neg, neg_sub]
  simp [swapIssue]

theorem relevanceSign_eq_one_iff {ctx : Context W} {e : Set W} :
    relevanceSign ctx e = 1 ↔ posRelevant ctx e := by
  rw [relevanceSign, sign_eq_one_iff, sub_pos, posRelevant_iff_cond_lt, measureReal_def,
    measureReal_def, ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

/-! ### Monotonicity

Shedding ¬H-worlds from an utterance can only strengthen it as an argument for
H: the H-side conditional is unchanged and the ¬H-side conditional can only
fall. -/

theorem bayesFactor_le_of_subset (ctx : Context W) {u₁ u₂ : Set W}
    (hsub : u₂ ⊆ u₁) (hent : ctx.topic ∩ u₁ ⊆ u₂) :
    bayesFactor ctx u₁ ≤ bayesFactor ctx u₂ := by
  have h : ctx.topic ∩ u₁ = ctx.topic ∩ u₂ := Set.inter_congr_left (fun _ hw ↦ hsub hw.2) hent
  rw [bayesFactor_def, bayesFactor_def, cond_apply ctx.topicMeasurable,
    cond_apply ctx.topicMeasurable, h]
  exact ENNReal.div_le_div_left (measure_mono hsub) _

theorem bayesFactor_lt_of_subset (ctx : Context W) [IsFiniteMeasure ctx.prior]
    {u₁ u₂ : Set W} (hu₂ : MeasurableSet u₂) (hsub : u₂ ⊆ u₁) (hent : ctx.topic ∩ u₁ ⊆ u₂)
    (hpos : ctx.prior (ctx.topic ∩ u₂) ≠ 0) (hgap : ctx.prior (u₁ \ u₂) ≠ 0) :
    bayesFactor ctx u₁ < bayesFactor ctx u₂ := by
  have h : ctx.topic ∩ u₁ = ctx.topic ∩ u₂ := Set.inter_congr_left (fun _ hw ↦ hsub hw.2) hent
  have hgap' : u₁ \ u₂ ⊆ ctx.topicᶜ := fun w hw h ↦ hw.2 (hent ⟨h, hw.1⟩)
  have hd : ctx.prior[|ctx.topicᶜ] u₂ < ctx.prior[|ctx.topicᶜ] u₁ := by
    rw [cond_apply ctx.topicMeasurable.compl, cond_apply ctx.topicMeasurable.compl,
      ← measure_inter_add_sdiff (ctx.topicᶜ ∩ u₁) hu₂, Set.inter_sdiff_assoc,
      Set.inter_eq_right.mpr hgap', Set.inter_assoc, Set.inter_eq_right.mpr hsub]
    exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr (measure_ne_top ctx.prior _))
      (ENNReal.inv_ne_top.mpr fun h0 ↦ hgap (measure_mono_null hgap' h0))
      (ENNReal.lt_add_right (measure_ne_top ctx.prior _) hgap)
  rw [bayesFactor_def, bayesFactor_def, cond_apply ctx.topicMeasurable,
    cond_apply ctx.topicMeasurable, h]
  exact ENNReal.div_lt_div_left
    (mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top ctx.prior _)) hpos)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr fun h ↦ hpos
      (measure_mono_null Set.inter_subset_left h)) (measure_ne_top ctx.prior _)) hd

/-! ### Counting priors

Over a finite type with the counting prior, the Bayes factor is a ratio of
proportions and relevance its logarithm. The real-valued forms need no side
conditions: the junk values agree (`0 / 0 = 0` in `ℝ`, `Real.log 0 = 0`). -/

section Count

variable [Fintype W] [MeasurableSingletonClass W] (topic e : Set W)

theorem toReal_bayesFactor_count :
    (bayesFactor ⟨topic, .of_discrete, .count⟩ e).toReal =
      ((topic ∩ e).ncard / topic.ncard) / ((topicᶜ ∩ e).ncard / topicᶜ.ncard) := by
  rw [toReal_bayesFactor]
  exact congrArg₂ (· / ·) (uniformOn_real_apply topic e) (uniformOn_real_apply topicᶜ e)

theorem relevance_count :
    relevance ⟨topic, .of_discrete, .count⟩ e =
      Real.log (((topic ∩ e).ncard / topic.ncard) / ((topicᶜ ∩ e).ncard / topicᶜ.ncard)) :=
  congrArg Real.log (toReal_bayesFactor_count topic e)

theorem relevanceSign_count :
    relevanceSign ⟨topic, .of_discrete, .count⟩ e =
      SignType.sign ((topic ∩ e).ncard / topic.ncard - (topicᶜ ∩ e).ncard / topicᶜ.ncard : ℝ) :=
  congrArg SignType.sign
    (congrArg₂ (· - ·) (uniformOn_real_apply topic e) (uniformOn_real_apply topicᶜ e))

variable {topic} in
/-- On a live issue the relevance sign compares cross-products of counts. -/
theorem relevanceSign_count_eq (h : topic.Nonempty) (hc : topicᶜ.Nonempty) :
    relevanceSign ⟨topic, .of_discrete, .count⟩ e =
      SignType.sign ((topic ∩ e).ncard * topicᶜ.ncard - (topicᶜ ∩ e).ncard * topic.ncard : ℤ) := by
  have h₁ : (0 : ℝ) < topic.ncard := by exact_mod_cast (Set.ncard_pos topic.toFinite).2 h
  have h₂ : (0 : ℝ) < topicᶜ.ncard := by exact_mod_cast (Set.ncard_pos topicᶜ.toFinite).2 hc
  rw [relevanceSign_count, div_sub_div _ _ h₁.ne' h₂.ne', div_eq_mul_inv, sign_mul,
    sign_pos (inv_pos.2 (mul_pos h₁ h₂)), mul_one, ← sign_intCast (α := ℝ)]
  push_cast
  ring_nf

variable {topic e}

theorem bayesFactor_count_ne_zero (h : (topic ∩ e).Nonempty) :
    bayesFactor ⟨topic, .of_discrete, .count⟩ e ≠ 0 :=
  bayesFactor_ne_zero ((uniformOn_eq_zero_iff (Set.toFinite _)).not.mpr h.ne_empty)

theorem bayesFactor_count_ne_top (h : (topicᶜ ∩ e).Nonempty) :
    bayesFactor ⟨topic, .of_discrete, .count⟩ e ≠ ⊤ :=
  bayesFactor_ne_top ((uniformOn_eq_zero_iff (Set.toFinite _)).not.mpr h.ne_empty)

end Count

/-! ### Cross-product characterizations

The relevance signs as comparisons of cross-products of real masses. -/

section Cross

variable (ctx : Context W) [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {e : Set W}

private theorem measureReal_topic_pos : 0 < ctx.prior.real ctx.topic :=
  ENNReal.toReal_pos Context.Nondegenerate.topic_ne_zero (measure_ne_top _ _)

private theorem measureReal_compl_pos : 0 < ctx.prior.real ctx.topicᶜ :=
  ENNReal.toReal_pos Context.Nondegenerate.compl_ne_zero (measure_ne_top _ _)

theorem posRelevant_iff_real_cross :
    posRelevant ctx e ↔
      ctx.prior.real (ctx.topicᶜ ∩ e) * ctx.prior.real ctx.topic <
        ctx.prior.real (ctx.topic ∩ e) * ctx.prior.real ctx.topicᶜ := by
  rw [posRelevant_iff_cond_lt, ← ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    (measure_ne_top _ _), ← measureReal_def, ← measureReal_def,
    cond_real_apply _ ctx.topicMeasurable.compl, cond_real_apply _ ctx.topicMeasurable,
    div_lt_div_iff₀ (measureReal_compl_pos ctx) (measureReal_topic_pos ctx)]

theorem negRelevant_iff_real_cross (he : ctx.prior e ≠ 0) :
    negRelevant ctx e ↔
      ctx.prior.real (ctx.topic ∩ e) * ctx.prior.real ctx.topicᶜ <
        ctx.prior.real (ctx.topicᶜ ∩ e) * ctx.prior.real ctx.topic := by
  have hHm := ctx.topicMeasurable
  rcases eq_or_ne (ctx.prior[|ctx.topicᶜ] e) 0 with h | h
  · have h0 : ctx.prior (ctx.topicᶜ ∩ e) = 0 :=
      by_contra fun hne ↦ (cond_pos_of_inter_ne_zero hHm.compl hne).ne' h
    have hH : ctx.prior (ctx.topic ∩ e) ≠ 0 := fun hH ↦ he <| measure_mono_null
      (fun x hx ↦ (em (x ∈ ctx.topic)).imp (⟨·, hx⟩) (⟨·, hx⟩)) (measure_union_null hH h0)
    refine iff_of_false ?_ (not_lt.2 ?_)
    · rw [negRelevant, bayesFactor_def, h,
        ENNReal.div_zero (cond_pos_of_inter_ne_zero hHm hH).ne', not_lt]
      exact le_top
    · rw [measureReal_def ctx.prior (ctx.topicᶜ ∩ e), h0, ENNReal.toReal_zero, zero_mul]
      positivity
  · rw [negRelevant_iff_cond_lt h, ← ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (measure_ne_top _ _), ← measureReal_def, ← measureReal_def, cond_real_apply _ hHm.compl,
      cond_real_apply _ hHm,
      div_lt_div_iff₀ (measureReal_topic_pos ctx) (measureReal_compl_pos ctx)]

end Cross

/-! ### Issue-conditional independence -/

/-- A and B are independent conditionally on H and on ¬H (Definition 9) when mathlib's `IndepSet`
holds at both conditionals. Merin's Conditional Independence Presumption (Hypothesis 2) is that
interpretation assumes this of coordinated sisters unless something suggests otherwise. -/
def CondIndepIssue (ctx : Context W) (a b : Set W) : Prop :=
  ∀ θ, IndepSet a b (ctx.conditional θ)

theorem condIndepIssue_iff (ctx : Context W) {a b : Set W}
    (ham : MeasurableSet a) (hbm : MeasurableSet b) :
    CondIndepIssue ctx a b ↔
      (ctx.prior[|ctx.topic] (a ∩ b) =
        ctx.prior[|ctx.topic] a * ctx.prior[|ctx.topic] b ∧
      ctx.prior[|ctx.topicᶜ] (a ∩ b) =
        ctx.prior[|ctx.topicᶜ] a * ctx.prior[|ctx.topicᶜ] b) := by
  refine ⟨fun h ↦ ⟨(h true).measure_inter_eq_mul, (h false).measure_inter_eq_mul⟩,
    fun h θ ↦ ?_⟩
  cases θ
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.2
  · exact (indepSet_iff_measure_inter_eq_mul ham hbm _).mpr h.1

section Count

variable [Fintype W] [MeasurableSingletonClass W] {topic a b : Set W}

private theorem indepSet_uniformOn_iff (s : Set W) :
    IndepSet a b (uniformOn s) ↔
      (s ∩ (a ∩ b)).ncard * s.ncard = (s ∩ a).ncard * (s ∩ b).ncard := by
  rw [indepSet_iff_measure_inter_eq_mul .of_discrete .of_discrete (uniformOn s),
    ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    uniformOn_real_apply, uniformOn_real_apply, uniformOn_real_apply]
  rcases Nat.eq_zero_or_pos s.ncard with h0 | h0
  · have hz : ∀ t, (s ∩ t).ncard = 0 := fun t ↦
      Nat.eq_zero_of_le_zero (h0 ▸ Set.ncard_le_ncard Set.inter_subset_left s.toFinite)
    simp [h0, hz]
  · rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    norm_cast
    rw [← mul_assoc]
    exact ⟨fun h ↦ Nat.eq_of_mul_eq_mul_right h0 h, fun h ↦ by rw [h]⟩

theorem condIndepIssue_count_iff :
    CondIndepIssue ⟨topic, .of_discrete, .count⟩ a b ↔
      (topic ∩ (a ∩ b)).ncard * topic.ncard = (topic ∩ a).ncard * (topic ∩ b).ncard ∧
      (topicᶜ ∩ (a ∩ b)).ncard * topicᶜ.ncard = (topicᶜ ∩ a).ncard * (topicᶜ ∩ b).ncard := by
  rw [CondIndepIssue, Bool.forall_bool, and_comm]
  exact and_congr (indepSet_uniformOn_iff _) (indepSet_uniformOn_iff _)

end Count

/-! ### Sign reversal -/

/-- E is positively relevant to H iff negatively relevant to ¬H (Corollary 3). -/
theorem sign_reversal_qual (ctx : Context W) (e : Set W) (hEH : ctx.prior[|ctx.topic] e ≠ 0) :
    posRelevant ctx e ↔ negRelevant (swapIssue ctx) e := by
  rw [posRelevant_iff_cond_lt, negRelevant_iff_cond_lt (by simpa [swapIssue] using hEH)]
  simp [swapIssue]

/-- The Bayes factors of E for H and for ¬H multiply to one (Corollary 3). -/
theorem sign_reversal (ctx : Context W) (e : Set W) (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    bayesFactor ctx e * bayesFactor (swapIssue ctx) e = 1 := by
  rw [bayesFactor_swapIssue, bayesFactor_def, div_eq_mul_inv, div_eq_mul_inv, mul_mul_mul_comm,
    mul_comm (ctx.prior[|ctx.topic] e), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hENotH (measure_ne_top _ _),
    ENNReal.mul_inv_cancel hEH (measure_ne_top _ _), one_mul]

/-- The log Bayes factor of E for H is the conditional surprisal of E given ¬H minus that given H
(Fact 2). -/
theorem relevance_eq_neg_log_sub_neg_log (ctx : Context W) (e : Set W)
    (hEH : ctx.prior[|ctx.topic] e ≠ 0)
    (hENotH : ctx.prior[|ctx.topicᶜ] e ≠ 0) :
    relevance ctx e =
      (-Real.log (ctx.prior[|ctx.topicᶜ] e).toReal) -
      (-Real.log (ctx.prior[|ctx.topic] e).toReal) := by
  rw [relevance, bayesFactor_def, ENNReal.toReal_div,
    Real.log_div (ENNReal.toReal_ne_zero.2 ⟨hEH, measure_ne_top _ _⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hENotH, measure_ne_top _ _⟩)]
  ring

/-! ### Consequences of issue-conditional independence

Theorem 6a holds for any two probability measures under which A and B are independent; the
conditionals on the two sides of the issue are such a pair. -/

/-- Under issue-conditional independence the Bayes factor is multiplicative over conjunction,
BF(A∧B) = BF(A) · BF(B) (Fact 5). -/
theorem CondIndepIssue.bayesFactor_inter {ctx : Context W} {a b : Set W}
    (h : CondIndepIssue ctx a b) (hNotH' : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∩ b) = bayesFactor ctx a * bayesFactor ctx b := by
  have hb : ctx.conditional false b ≠ 0 := hNotH'
  simp only [bayesFactor]
  rw [(h true).measure_inter_eq_mul, (h false).measure_inter_eq_mul,
    ENNReal.mul_div_mul_comm (.inr (measure_ne_top _ _)) (.inr hb)]

/-- Under issue-conditional independence with A and B both positively relevant, their
conjunction dominates both conjuncts, the conjunction case of Theorem 6a. -/
theorem CondIndepIssue.max_bayesFactor_lt_inter {ctx : Context W} {a b : Set W}
    (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    max (bayesFactor ctx a) (bayesFactor ctx b) < bayesFactor ctx (a ∩ b) := by
  rw [h.bayesFactor_inter hNb, max_lt_iff]
  constructor
  · simpa using ENNReal.mul_lt_mul_right (zero_lt_one.trans hPosA).ne' (bayesFactor_ne_top hNa)
      hPosB
  · simpa using ENNReal.mul_lt_mul_left (zero_lt_one.trans hPosB).ne' (bayesFactor_ne_top hNb)
      hPosA

private lemma max_div_gt_or_div (pAH pBH pAnH pBnH : ℝ)
    (h1 : 0 < pAnH) (h2 : 0 < pBnH)
    (h3 : pAnH < pAH) (h4 : pBnH < pBH)
    (h5 : pAnH < 1) (h6 : pBnH < 1)
    (_h7 : pAH ≤ 1) (h8 : pBH ≤ 1) :
    max (pAH / pAnH) (pBH / pBnH) >
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) ∧
    (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) > 1 := by
  have hden_pos : pAnH + pBnH - pAnH * pBnH > 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, max_def]; split
    · rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      nlinarith [mul_pos (mul_pos h2 (show (0:ℝ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · rename_i hlt; push Not at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      nlinarith [mul_pos (mul_pos h1 (show (0:ℝ) < pAH by linarith))
        (show pBH - pBnH > 0 from by linarith)]
  · rw [gt_iff_lt, one_lt_div hden_pos]
    nlinarith

/-- The union bounds of Theorem 6a hold for two probability measures making A and B independent,
each with ratio above one. -/
private theorem div_union_bounds {μ ν : Measure W} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {a b : Set W} (hbm : MeasurableSet b)
    (h₁ : IndepSet a b μ) (h₂ : IndepSet a b ν) (ha : 1 < μ a / ν a) (hb : 1 < μ b / ν b)
    (hνa : ν a ≠ 0) (hνb : ν b ≠ 0) :
    μ (a ∪ b) / ν (a ∪ b) < max (μ a / ν a) (μ b / ν b) ∧ 1 < μ (a ∪ b) / ν (a ∪ b) := by
  have hlt {s : Set W} (hs : 1 < μ s / ν s) (h0 : ν s ≠ 0) : ν.real s < μ.real s :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 <| by
      simpa using (ENNReal.lt_div_iff_mul_lt (.inl h0) (.inl (measure_ne_top _ _))).1 hs
  have hunion {ρ : Measure W} [IsProbabilityMeasure ρ] (h : IndepSet a b ρ) :
      ρ.real (a ∪ b) = ρ.real a + ρ.real b - ρ.real a * ρ.real b := by
    rw [eq_sub_iff_add_eq, ← measureReal_union_add_inter hbm, h.measureReal_inter_eq_mul]
  have hfin {s : Set W} (h0 : ν s ≠ 0) : μ s / ν s ≠ ⊤ := ENNReal.div_ne_top (measure_ne_top _ _) h0
  have hνu : ν (a ∪ b) ≠ 0 := fun h0 ↦ hνa (measure_mono_null Set.subset_union_left h0)
  have hA := hlt ha hνa
  have hB := hlt hb hνb
  have harith := max_div_gt_or_div _ _ _ _ (ENNReal.toReal_pos hνa (measure_ne_top _ _))
    (ENNReal.toReal_pos hνb (measure_ne_top _ _)) hA hB (hA.trans_le measureReal_le_one)
    (hB.trans_le measureReal_le_one) measureReal_le_one measureReal_le_one
  constructor
  · rw [← ENNReal.toReal_lt_toReal (hfin hνu) (max_ne_top (hfin hνa) (hfin hνb)),
      ENNReal.toReal_max (hfin hνa) (hfin hνb), ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, hunion h₁, hunion h₂]
    exact harith.1
  · rw [← ENNReal.toReal_lt_toReal ENNReal.one_ne_top (hfin hνu), ENNReal.toReal_one,
      ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, hunion h₁, hunion h₂]
    exact harith.2

/-- Under issue-conditional independence with A and B positively relevant, the Bayes factor of their
disjunction is below the larger of theirs (Theorem 6a). -/
theorem CondIndepIssue.bayesFactor_union_lt_max {ctx : Context W}
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (hbm : MeasurableSet b) (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    bayesFactor ctx (a ∪ b) < max (bayesFactor ctx a) (bayesFactor ctx b) := by
  have := ctx.isProbabilityMeasure_conditional true
  have := ctx.isProbabilityMeasure_conditional false
  exact (div_union_bounds hbm (h true) (h false) hPosA hPosB hNa hNb).1

/-- Under issue-conditional independence with A and B both positively relevant, their
disjunction is still positively relevant, the lower bound for disjunction in Theorem 6a. -/
theorem CondIndepIssue.one_lt_bayesFactor_union {ctx : Context W}
    [IsFiniteMeasure ctx.prior] [ctx.Nondegenerate] {a b : Set W}
    (hbm : MeasurableSet b) (h : CondIndepIssue ctx a b)
    (hPosA : posRelevant ctx a) (hPosB : posRelevant ctx b)
    (hNa : ctx.prior[|ctx.topicᶜ] a ≠ 0) (hNb : ctx.prior[|ctx.topicᶜ] b ≠ 0) :
    1 < bayesFactor ctx (a ∪ b) := by
  have := ctx.isProbabilityMeasure_conditional true
  have := ctx.isProbabilityMeasure_conditional false
  exact (div_union_bounds hbm (h true) (h false) hPosA hPosB hNa hNb).2

/-! ### The Bayesian bridge -/

theorem posRelevant_iff_lt_cond (ctx : Context W) [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] (e : Set W) :
    posRelevant ctx e ↔ ctx.prior e < ctx.prior[|ctx.topic] e := by
  have hHm := ctx.topicMeasurable
  rw [posRelevant_iff_cond_lt, ← cond_add_cond_compl_eq hHm ctx.prior]
  conv_rhs => rhs; rw [← mul_one (ctx.prior[|ctx.topic] e),
    ← prob_add_prob_compl (μ := ctx.prior) hHm, mul_add]
  rw [ENNReal.add_lt_add_iff_left (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ENNReal.mul_lt_mul_iff_left Context.Nondegenerate.compl_ne_zero (measure_ne_top _ _)]

end DTS
