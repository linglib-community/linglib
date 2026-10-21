module

public import Linglib.Discourse.Response
public import Linglib.Syntax.PolarInterrogative.Basic

/-!
# Answers to polar interrogatives

In Holmberg's syntax of yes–no questions the polarity head of a polar interrogative is merged
unvalued, and a short answer merges a focused valued polarity feature, spelled out by an answer
particle, with the clause inherited from the question, normally elided. A
`PolarInterrogative.AnswerFeature` is that feature: a valued [+Pol] or [−Pol], or the
affirmative [+Pol, REV] of a polarity-reversing particle such as Swedish *jo*, which eliminates
the negation in the answer. Given the negation of the clause the answer inherits,
`AnswerFeature.answer` computes the polarity of the alternative the answer confirms, relative to
the question's positive alternative, or `none` for an ill-formed answer. A negation out of the
polarity head's reach, such as a low, VP-internal one, leaves the particle to value the head,
and the value composes with the negation; a middle negation values the head itself, so that a
negative particle agrees with it and a plain affirmative clashes with it.

The answers a feature gives to the questions whose negations a language allows form a set of
`Discourse.Response`s (`AnswerFeature.responses`), the image of the response the feature gives
each negation (`AnswerFeature.response`), whose polarity features are those of Farkas
and Bruce, to whom Holmberg credits REV. The mechanism derives the two systems for answering
negative questions from the syntax of negation. Out of the head's reach a valued feature fixes
the relative polarity of the answer, the truth-based system
(`AnswerFeature.responses_value_of_forall_not_valuesHead`), so that the affirmative feature
confirms the negative alternative just when the negation is low
(`AnswerFeature.confirmsNegativeQuestion_responses_positive_iff`). A negation valuing the head
leaves only the negative feature, which fixes the absolute polarity, the polarity-based system
(`AnswerFeature.responses_value_negative_of_valuesHead`,
`AnswerFeature.responses_value_positive_of_valuesHead`). The only answer a reversing feature
gives is the [reverse, +] answer to a negative question (`AnswerFeature.responses_reversing`).

## Implementation notes

* What decides the system is whether the negation can value the polarity head
  (`PolarInterrogative.ClauseNegation.ValuesHead`); the height of the negation matters only
  through that, as Holmberg argues for Thai, whose negation cannot value the head from inside
  the complement of the question particle.
* REV needs a negation in the answer to eliminate, so a reversing particle is ill formed after a
  neutral or a positive-bias question. Colloquial Swedish, where *jo* can confirm the positive
  alternative of any yes–no question (Holmberg's footnote to the section on positive and
  negative bias), is not modelled.
* The two versions of the negative particle in polarity-based languages, an interpretable one
  valuing the head and an uninterpretable one agreeing with a negation that values it, are one
  `AnswerFeature.value .negative`, whose agreement is built into `AnswerFeature.answer`.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
-/

@[expose] public section

namespace PolarInterrogative

/-- The feature an answer particle spells out, a valued polarity feature or the affirmative
polarity-reversing feature of *jo*, `[jo, +Pol, REV]`. -/
inductive AnswerFeature where
  /-- A valued polarity feature, [+Pol] or [−Pol]. -/
  | value (p : Polarity)
  /-- [+Pol, REV], positive polarity eliminating a negation in the answer. -/
  | reversing
  deriving DecidableEq, Repr

namespace AnswerFeature

open ClauseNegation

/-- The polarity of the alternative an answer confirms, relative to the positive alternative,
or `none` when the answer is ill formed. A reversing feature eliminates the negation inside the
inherited clause and values the head, and is ill formed without one. Otherwise, if the negation
values the head, a negative feature agrees with it and an affirmative one clashes with it; if
not, the feature values the head, composing with a negation inside the clause. -/
def answer : AnswerFeature → ClauseNegation → Option Polarity
  | reversing, n => if n.InClause then some .positive else none
  | value p, n =>
    if n.ValuesHead then (if p = .negative then some .negative else none)
    else some (p * n.primaryPolarity)

variable {n : ClauseNegation}

/-- A reversing feature eliminates the negation inside the clause and values the head. -/
theorem answer_reversing_of_inClause (h : n.InClause) : reversing.answer n = some .positive := by
  simp [answer, h]

/-- A reversing feature has no negation to eliminate outside a negative-bias question. -/
theorem answer_reversing_of_not_inClause (h : ¬ n.InClause) : reversing.answer n = none := by
  simp [answer, h]

/-- When the negation values the head, a negative feature agrees with it, confirming the
negative alternative, and an affirmative one clashes with it. -/
theorem answer_value_of_valuesHead {p : Polarity} (h : n.ValuesHead) :
    (value p).answer n = if p = .negative then some .negative else none := by
  simp [answer, h]

/-- Without a negation valuing the head, a valued feature values it and composes with the
polarity of the primary alternative. -/
theorem answer_value_of_not_valuesHead {p : Polarity} (h : ¬ n.ValuesHead) :
    (value p).answer n = some (p * n.primaryPolarity) := by
  simp [answer, h]

/-- A negation inside the clause that does not value the head admits every feature, so a
truth-based configuration has no need of a reversing particle. -/
theorem answer_ne_none_of_inClause (f : AnswerFeature) (hi : n.InClause) (h : ¬ n.ValuesHead) :
    f.answer n ≠ none := by
  cases f
  · simp [answer_value_of_not_valuesHead h]
  · simp [answer_reversing_of_inClause hi]

/-- The response an answer with feature `f` gives to a polar question whose negation is `n`, if
the answer is well formed, recording the polarity of the question's primary alternative and that
of the alternative the answer confirms. -/
def response (f : AnswerFeature) (n : ClauseNegation) : Option Discourse.Response :=
  (f.answer n).map (⟨.polarQuestion, n.primaryPolarity, ·⟩)

theorem response_eq_some_iff {f : AnswerFeature} {x : Discourse.Response} :
    f.response n = some x ↔ x.reactsTo = .polarQuestion ∧ x.antecedent = n.primaryPolarity ∧
      f.answer n = some x.polarity := by
  obtain ⟨m, a, s⟩ := x
  cases h : f.answer n <;> simp [response, h, and_comm, eq_comm]

/-- Without a negation valuing the head, a valued feature answers with the response of relative
polarity `p` to the question's primary alternative. -/
theorem response_value_of_not_valuesHead {p : Polarity} (h : ¬ n.ValuesHead) :
    (value p).response n = some ⟨.polarQuestion, n.primaryPolarity, p * n.primaryPolarity⟩ := by
  simp [response, answer_value_of_not_valuesHead h]

/-- Out of the head's reach, the relative polarity of an answer is the value of its feature. -/
theorem relative_of_response_value {p : Polarity} {x : Discourse.Response}
    (hn : ¬ n.ValuesHead) (h : (value p).response n = some x) : x.relative = p := by
  rw [response_value_of_not_valuesHead hn, Option.some_inj] at h
  rw [← h, Discourse.Response.relative_mk, mul_div_cancel_right]

/-- A reversing feature answers a question with a negation inside the clause by reversing its
negative primary alternative. -/
theorem response_reversing_of_inClause (h : n.InClause) :
    reversing.response n = some ⟨.polarQuestion, .negative, .positive⟩ := by
  simp [response, answer_reversing_of_inClause h, primaryPolarity_of_inClause h]

theorem response_reversing_of_not_inClause (h : ¬ n.InClause) : reversing.response n = none := by
  simp [response, answer_reversing_of_not_inClause h]

/-- The answers a feature gives to polar questions whose negations are among `N`. -/
def responses (f : AnswerFeature) (N : Set ClauseNegation) : Set Discourse.Response :=
  {x | ∃ n ∈ N, f.response n = some x}

variable {f : AnswerFeature} {N : Set ClauseNegation}

theorem mem_responses {x : Discourse.Response} :
    x ∈ f.responses N ↔ ∃ n ∈ N, f.response n = some x :=
  Iff.rfl

theorem responses_singleton_of_response_eq_some {x : Discourse.Response}
    (h : f.response n = some x) : f.responses {n} = {x} := by
  ext y
  simp [responses, h, eq_comm]

theorem responses_singleton_of_response_eq_none (h : f.response n = none) :
    f.responses {n} = ∅ := by
  ext y
  simp [responses, h]

/-- Out of the reach of every negation of `N`, a valued feature fixes the relative polarity of
the answer to the question's primary alternative, as in the truth-based system. -/
theorem responses_value_of_forall_not_valuesHead {p : Polarity} (hN : ∀ n ∈ N, ¬ n.ValuesHead) :
    (value p).responses N = {x | x.reactsTo = .polarQuestion ∧
      x.antecedent ∈ primaryPolarity '' N ∧ x.relative = p} := by
  ext x
  refine ⟨fun ⟨n, hn, h⟩ ↦ ?_, fun ⟨hm, ⟨n, hn, ha⟩, hr⟩ ↦ ⟨n, hn, ?_⟩⟩
  · obtain ⟨hm, ha, -⟩ := response_eq_some_iff.1 h
    exact ⟨hm, ⟨n, hn, ha.symm⟩, relative_of_response_value (hN n hn) h⟩
  · obtain ⟨m, a, s⟩ := x
    obtain rfl : m = .polarQuestion := hm
    obtain rfl : n.primaryPolarity = a := ha
    obtain rfl : s / n.primaryPolarity = p := hr
    rw [response_value_of_not_valuesHead (hN n hn), div_mul_cancel]

/-- A negation valuing the head leaves the negative feature only the confirmation of the negative
alternative, its absolute polarity, as in the polarity-based system. -/
theorem responses_value_negative_of_valuesHead (hn : n.ValuesHead) :
    (value .negative).responses {n} = {⟨.polarQuestion, .negative, .negative⟩} := by
  obtain rfl : n = .height .middle := hn
  exact responses_singleton_of_response_eq_some rfl

/-- A negation valuing the head leaves the affirmative feature no answer. -/
theorem responses_value_positive_of_valuesHead (hn : n.ValuesHead) :
    (value .positive).responses {n} = ∅ := by
  obtain rfl : n = .height .middle := hn
  exact responses_singleton_of_response_eq_none rfl

/-- REV is [reverse, +]. Once some negation of `N` is inside the clause, the only answer of a
reversing feature reverses a negative primary alternative with a positive answer. -/
theorem responses_reversing (hN : ∃ n ∈ N, n.InClause) :
    reversing.responses N = {⟨.polarQuestion, .negative, .positive⟩} := by
  obtain ⟨n₀, hn₀, hi₀⟩ := hN
  ext x
  refine ⟨fun ⟨n, _, h⟩ ↦ ?_, fun h ↦ ⟨n₀, hn₀, h ▸ response_reversing_of_inClause hi₀⟩⟩
  by_cases hi : n.InClause
  · rw [response_reversing_of_inClause hi, Option.some_inj] at h
    exact h.symm
  · rw [response_reversing_of_not_inClause hi] at h
    cases h

/-- The answers of a feature to questions whose negations are among `N` confirm the negative
alternative of a negative question iff some negation of `N` inside the clause yields it. -/
theorem confirmsNegativeQuestion_responses_iff :
    Discourse.Response.ConfirmsNegativeQuestion (f.responses N) ↔
      ∃ n ∈ N, n.InClause ∧ f.answer n = some .negative := by
  simp only [Discourse.Response.ConfirmsNegativeQuestion,
    Discourse.Response.negativeQuestionConfirmation, mem_responses, response_eq_some_iff,
    true_and]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  simp only [primaryPolarity]
  split_ifs with h <;> simp [h]

/-- In the truth-based system the affirmative feature confirms the negative alternative of a
question whose negation has height `h` iff the negation is low, out of the polarity head's
reach. -/
theorem confirmsNegativeQuestion_responses_positive_iff (h : NegationHeight) :
    Discourse.Response.ConfirmsNegativeQuestion ((value .positive).responses {.height h}) ↔
      h = .low := by
  rw [confirmsNegativeQuestion_responses_iff]
  cases h <;> simp [answer, ClauseNegation.InClause, ClauseNegation.ValuesHead,
    primaryPolarity]

/-- In the polarity-based system the negative feature confirms the negative alternative of a
question whose negation has height `h` iff the negation is middle, valuing the polarity head. -/
theorem confirmsNegativeQuestion_responses_negative_iff (h : NegationHeight) :
    Discourse.Response.ConfirmsNegativeQuestion ((value .negative).responses {.height h}) ↔
      h = .middle := by
  rw [confirmsNegativeQuestion_responses_iff]
  cases h <;> simp [answer, ClauseNegation.InClause, ClauseNegation.ValuesHead,
    primaryPolarity]

end AnswerFeature

end PolarInterrogative
