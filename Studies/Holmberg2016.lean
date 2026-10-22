module

public import Linglib.Discourse.Response
public import Linglib.Semantics.Denotation
public import Linglib.Syntax.Negation
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Fragments.English.Particles
public import Linglib.Fragments.Japanese.Particles
public import Linglib.Fragments.Romance.French.Particles
public import Linglib.Fragments.Swedish.Particles
public import Studies.FarkasBruce2010
public import Linglib.Data.Examples.Holmberg2016
public import Mathlib.Data.Fintype.Sum

/-!
# Holmberg (2016): The Syntax of Yes and No

This file formalizes Holmberg's account of answers to yes–no questions. A polar
interrogative contains an unvalued polarity head whose two values yield the Hamblin set it
denotes, the same for a negative interrogative as for its positive counterpart
(`PolarInterrogative.denote_eq_polar_radical`), and an answer is a full sentence: a focused
valued polarity feature, spelled out by a particle or an echoed verb, merged with the clause
inherited from the question and eliding it, so that it chooses one of the two alternatives
(`smul_mem_alt`). The particles of
English, Swedish, French and Japanese spell out the features `english`, `swedish`, `french` and
`japanese`. The two systems for answering negative questions follow from the syntax of negation
(`AnswerFeature.answer`): a middle negation values the polarity head before the particle can,
so a plain affirmative clashes and the negative particle confirms the negative alternative,
while a low negation is out of reach, so *yes* confirms the negative alternative and *no* is a
double negation. English speakers who read *not* low and those who read it middle both take a
bare answer to *Is John not coming?* to mean that he is not coming (`negative_neutralization`);
an adverb preceding *not* forces the low reading, and in Swedish, which has no low negation, an
adverb screens the middle negation from the polarity head to the same effect
(`swedish_adverb`).

Section 4.4 defines the polarity-based system as the one lacking low negation (`PolarityBased`),
which is the typology's: its affirmative particle never confirms the negative alternative of a
negative question (`polarityBased_iff_not_confirmsNegativeQuestion`). Such a language has no
negative neutralization (`PolarityBased.answer_ne_negative`); Swedish, whose negation is never low,
is one (`swedish_polarityBased`), so confirming the positive alternative of a negative question
takes the polarity-reversing *jo* (`swedish_negative_question`), which a truth-based configuration
never needs (`no_reversal_needed_truth_based`). In the polarity features of Farkas and Bruce, the
Japanese particles answer a negative question by its relative polarity and the Swedish ones by its
absolute polarity (`japanese_responses`, `swedish_responses`). Crediting the REV feature to Farkas
and Bruce, the mechanism derives what they say *si* and *doch* mark: the answers a reversing feature
gives are their [reverse, +] answers (`responses_reversing_eq_reversePositive`). Positive-bias
questions carry a high negation outside the inherited clause and are answered like neutral questions
(`high_answers_like_neutral`). Which negations an English polar question form carries depends on the
speaker's variety (`negations`): a question with *not* has the inner reading for all speakers
(`primaryPolarity_of_mem_negations_nonPreposed`), and one with *-n't* only the outer reading in the
restrictive variety (`primaryPolarity_of_mem_negations_restrictive`), where it is answered like a
neutral question (`answer_of_mem_negations_restrictive`), and also the inner one in the tolerant
variety (`exists_mem_negations_tolerant_primaryPolarity`, `exists_mem_negations_tolerant`). The
mechanism predicts the judgment of every example answered by a single particle of the study, whose
question is neutral or whose negation the annotation locates (`judgment_iff_predicted`).

## Implementation notes

* An answer is computed as a polarity relative to the question's positive alternative
  (`AnswerFeature.answer`); the alternative it confirms is that polarity acting on the positive
  alternative. For *Har Johan nångång inte kommit i tid?* the positive alternative is that Johan
  has always been on time.
* Section 4.7 revises the height criterion: what matters is whether the negation can value the
  polarity head (`ClauseNegation.ValuesHead`), which is how Thai questions come out
  truth-based. Thai and the Chinese question types (Section 4.9) are not formalized, nor are
  verb-echo answers and the structure of Finnish and Thai answers (Chapter 3), the two versions
  of *no* of Section 4.4, the higher-order alternative of positive-bias questions (Section 4.8),
  the table of languages with a reversing affirmative particle, and the global survey of
  Section 4.2.
* The reading of a polar interrogative is an `Option Polarity`: `none` for a positive question,
  and for a negative one the polarity of the proposition it double-checks, relative to its radical,
  the primary polarity of the clause's negation (`ClauseNegation.primaryPolarity`). Ladd's outer
  reading is `some .positive` and his inner reading `some .negative`.
* REV needs a negation in the answer to eliminate, so a reversing particle is ill formed after a
  neutral or a positive-bias question. Colloquial Swedish, where *jo* can confirm the positive
  alternative of any yes–no question, is not modelled.
* The very formal English that does not use *-n't* at all, where a question with *not* must,
  as the book says presumably, carry the positive-bias reading as well, is not modelled: `negations`
  is stated for the varieties that use *-n't*.
* The book discusses French *oui* and *si* but not *non*, which `french` gives [−Pol], as the
  negative particle of every language the book discusses.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [ladd-1981]
-/

@[expose] public section

namespace Holmberg2016

open Question Discourse Semantics

/-! ### The polarity head -/

/-- Structural height of a sentential negation relative to the polarity head. The height
classifies constructions, not languages. English *not* is read low by some speakers and middle
by others, and low by all after an adverb; *-n't* in positive-bias questions is high. -/
inductive NegationHeight where
  /-- Negation below the reach of the polarity head, VP-internal (English *not* on its low
  reading). -/
  | low
  /-- Negation in a local c-command relation to the polarity head (Swedish, Finnish, English
  *not* on its middle reading). -/
  | middle
  /-- Negation above the polarity head, in the C-domain (English *-n't* in positive-bias
  questions). -/
  | high
  deriving DecidableEq, Repr, Fintype

/-- The negation of a clause relative to its polarity head, if any. An answer inherits the
negation of the clause it answers. -/
inductive ClauseNegation where
  /-- No negation, as in a neutral question or a positive statement. -/
  | absent
  /-- A negation of the given height, nothing intervening between it and the polarity head. -/
  | height (h : NegationHeight)
  /-- A middle negation screened from the polarity head by an adverb scoping over it, as in
  Swedish *Har Johan nångång inte kommit i tid?*. -/
  | screened
  deriving DecidableEq, Repr, Fintype

namespace ClauseNegation

variable (n : ClauseNegation)

/-- The negation is inside the clause the answer inherits, so that both alternatives of the
question contain it, as a low or middle negation is. -/
def InClause : Prop := n = .height .low ∨ n = .height .middle ∨ n = .screened

instance : Decidable n.InClause := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The polarity of the question's primary alternative relative to its positive alternative,
negative when the negation is inside the inherited clause. -/
def primaryPolarity : Polarity := if n.InClause then .negative else .positive

/-- The negation values the polarity head when it is a middle negation not screened off by an
adverb. -/
def ValuesHead : Prop := n = .height .middle

instance : Decidable n.ValuesHead := inferInstanceAs (Decidable (_ = _))

variable {n}

theorem primaryPolarity_of_inClause (h : n.InClause) : n.primaryPolarity = .negative := by
  simp [primaryPolarity, h]

end ClauseNegation

/-- A polar interrogative, given by its sentence radical, the positive alternative, and its
negation. -/
structure PolarInterrogative (W : Type*) where
  /-- The sentence radical, the positive alternative. -/
  radical : Set W
  /-- The negation of the interrogative. -/
  negation : ClauseNegation

namespace PolarInterrogative

open Semantics

variable {W : Type*} (q : PolarInterrogative W)

/-- The primary alternative is the radical under the polarity its negation gives it, negative
when the negation is inside the clause. -/
def primary : Set W := q.negation.primaryPolarity • q.radical

/-- A polar interrogative denotes the polar question of its primary alternative, the
disjunction of that alternative and its negation. -/
instance : Denotes (PolarInterrogative W) (Question W) := ⟨fun q ↦ Question.polar q.primary⟩

theorem denote_def : ⟦q⟧ = Question.polar q.primary := rfl

/-- A negative interrogative denotes the same question as its positive counterpart, the negation
deciding which alternative is primary, not what the alternatives are. -/
@[simp] theorem denote_eq_polar_radical : ⟦q⟧ = Question.polar q.radical :=
  Question.polar_smul _ _

/-- The alternatives of a polar interrogative with a nontrivial radical are the values of its
polarity variable applied to the radical, its polarity alternatives. -/
theorem alt_denote {q : PolarInterrogative W} (hne : q.radical ≠ ∅)
    (hnu : q.radical ≠ Set.univ) : Question.alt ⟦q⟧ = MulAction.orbit Polarity q.radical := by
  rw [denote_eq_polar_radical]
  exact Question.alt_polar_eq_orbit hne hnu

end PolarInterrogative

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

variable {W : Type*}

/-! ### The question variable -/

/-- An answer does not assert but chooses between the two alternatives of the question
(Section 5.1), and whatever polarity it gives the positive alternative yields one of them. -/
theorem smul_mem_alt {q : PolarInterrogative W} (hne : q.radical ≠ ∅)
    (hnu : q.radical ≠ Set.univ) (s : Polarity) : s • q.radical ∈ alt ⟦q⟧ := by
  rw [PolarInterrogative.alt_denote hne hnu]
  exact MulAction.mem_orbit _ s

/-! ### The particles -/

/-- An English particle spells out the valued feature of its polarity. -/
def english (p : English.PolarityParticle) : AnswerFeature := .value p.polarity

/-- The features of the Swedish particles, *jo* being [+Pol, REV]. -/
def swedish : Swedish.PolarityParticle → AnswerFeature
  | .ja => .value .positive
  | .nej => .value .negative
  | .jo => .reversing

/-- The features of the French particles, *si* being [+Pol, REV]. -/
def french : French.PolarityParticle → AnswerFeature
  | .oui => .value .positive
  | .non => .value .negative
  | .si => .reversing

/-- The features of the Japanese particles. -/
def japanese : Japanese.PolarityParticle → AnswerFeature
  | .un => .value .positive
  | .uun => .value .negative

/-! ### English (Section 4.3) -/

/-- In negative neutralization, speakers who read *not* low take *yes* to confirm that John is
not coming and speakers who read it middle take *no* to, so the two answers mean the same. -/
theorem negative_neutralization :
    (english .yes).answer (.height .low) = some .negative ∧
      (english .no).answer (.height .middle) = some .negative := by
  decide

/-- With the middle reading of *not*, bare *yes* is not a well-formed answer. -/
theorem yes_ill_formed_middle : (english .yes).answer (.height .middle) = none := by decide

/-- With the low reading, *no* is grammatically a double negation confirming the positive
alternative; since bare *no* is parsed as the simpler plain negation, the continuation of *No,
he is* is compulsory. -/
theorem no_double_negation : (english .no).answer (.height .low) = some .positive := by decide

/-! ### The polarity-based system (Section 4.4) -/

/-- A language whose negations take the heights `N` follows the polarity-based system, which
Section 4.4 defines as the system lacking low negation. -/
def PolarityBased (N : Finset NegationHeight) : Prop := .low ∉ N

instance (N : Finset NegationHeight) : Decidable (PolarityBased N) :=
  inferInstanceAs (Decidable (_ ∉ _))

/-- The definition is the typology's, since a language lacks low negation iff its affirmative
particle confirms the negative alternative of none of its negative questions. -/
theorem polarityBased_iff_not_confirmsNegativeQuestion {N : Finset NegationHeight} :
    PolarityBased N ↔ ¬ Response.ConfirmsNegativeQuestion
      ((AnswerFeature.value .positive).responses (ClauseNegation.height '' N)) := by
  rw [AnswerFeature.confirmsNegativeQuestion_responses_iff, PolarityBased]
  constructor
  · rintro hN ⟨_, ⟨h, hh, rfl⟩, -, ha⟩
    cases h
    · exact hN hh
    all_goals exact absurd ha (by decide)
  · exact fun H hl ↦ H ⟨_, ⟨.low, hl, rfl⟩, by decide, by decide⟩

/-- A polarity-based language has no negative neutralization, since no affirmative feature
confirms the negative alternative of a negative question, unless an adverb screens the
negation. -/
theorem PolarityBased.answer_ne_negative {N : Finset NegationHeight} (hN : PolarityBased N)
    {h : NegationHeight} (hh : h ∈ N) :
    (AnswerFeature.value .positive).answer (.height h) ≠ some .negative := by
  cases h
  · exact absurd hh hN
  all_goals decide

/-! ### Swedish (Section 4.5) and the reversing particles -/

/-- The heights of Swedish negation are middle, and high in positive-bias questions
(Section 4.8). Swedish has no low negation, hence no double negation
*Du kan inte inte gå i kyrkan* (Section 4.5). -/
def swedishNegation : Finset NegationHeight := {.middle, .high}

theorem swedish_polarityBased : PolarityBased swedishNegation := by decide

/-- *Ja* never confirms the negative alternative of a Swedish negative question. -/
theorem swedish_ja_ne_negative {h : NegationHeight} (hh : h ∈ swedishNegation) :
    (swedish .ja).answer (.height h) ≠ some .negative :=
  swedish_polarityBased.answer_ne_negative hh

/-- To *Har Johan inte kommit?* the plain affirmative *ja* is ill formed, *nej* confirms that he
has not come, and the reversing *jo* confirms that he has. -/
theorem swedish_negative_question :
    (swedish .ja).answer (.height .middle) = none ∧
      (swedish .nej).answer (.height .middle) = some .negative ∧
      (swedish .jo).answer (.height .middle) = some .positive := by
  decide

/-- With the negation valuing the polarity head, the Swedish particles answer a negative question
by its absolute polarity: *nej* gives only the [−] confirmation of the negative alternative, and
*ja* gives no answer at all. -/
theorem swedish_responses :
    (swedish .nej).responses {.height .middle} = {⟨.polarQuestion, .negative, .negative⟩} ∧
      (swedish .ja).responses {.height .middle} = ∅ :=
  ⟨AnswerFeature.responses_value_negative_of_valuesHead rfl,
    AnswerFeature.responses_value_positive_of_valuesHead rfl⟩

/-- In *Har Johan nångång inte kommit i tid?* the adverb intervening between the negation and
the polarity head lets *ja* confirm the negative alternative, although Swedish has no low
negation. -/
theorem swedish_adverb :
    (swedish .ja).answer .screened = some .negative ∧
      (swedish .nej).answer .screened = some .positive := by
  decide

/-- To *Tu n'es pas fatigué?* the plain affirmative *oui* is ill formed and the reversing *si*
confirms the positive alternative. -/
theorem french_negative_question :
    (french .oui).answer (.height .middle) = none ∧
      (french .si).answer (.height .middle) = some .positive := by
  decide

/-- REV, credited to Farkas and Bruce, is what they say *si* and *doch* mark. To questions whose
negations include one inside the inherited clause, a reversing feature such as that of *si* or
*jo* gives exactly the answers that are [reverse, +]. -/
theorem responses_reversing_eq_reversePositive {N : Set ClauseNegation}
    (hN : ∃ n ∈ N, n.InClause) :
    AnswerFeature.reversing.responses N =
      FarkasBruce2010.reversePositive ∩ {x | x.reactsTo = .polarQuestion} := by
  rw [AnswerFeature.responses_reversing hN]
  ext ⟨m, a, s⟩
  cases m <;> cases a <;> cases s <;> decide

/-- Reversing particles are needed only where a negation values the polarity head, since in a
truth-based configuration every particle yields a well-formed answer, which is why no language
with a reversing affirmative particle clearly employs the truth-based system. -/
theorem no_reversal_needed_truth_based (f : AnswerFeature) : f.answer (.height .low) ≠ none :=
  f.answer_ne_none_of_inClause (by decide) (by decide)

/-! ### Japanese (Section 4.1) -/

/-- On the prediction of Section 4.10 that the Japanese negation in a negative-bias question does
not value the polarity head, being low, *un* confirms that he does not drink coffee and *uun*
that he does. -/
theorem japanese_negative_question :
    (japanese .un).answer (.height .low) = some .negative ∧
      (japanese .uun).answer (.height .low) = some .positive := by
  decide

/-- With the negation low, the Japanese particles answer a negative question by its relative
polarity, *un* giving exactly the [same] answers and *uun* the [reverse] ones. -/
theorem japanese_responses :
    (japanese .un).responses {.height .low} =
        {x | x.reactsTo = .polarQuestion ∧ x.antecedent = .negative ∧ x.relative = .positive} ∧
      (japanese .uun).responses {.height .low} =
        {x | x.reactsTo = .polarQuestion ∧ x.antecedent = .negative ∧ x.relative = .negative} := by
  constructor <;>
  · rw [japanese, AnswerFeature.responses_value_of_forall_not_valuesHead (by decide)]
    simp [ClauseNegation.primaryPolarity, ClauseNegation.InClause]

/-! ### Positive-bias questions (Section 4.8) -/

/-- A positive-bias negative question, with the negation in the C-domain above the polarity
head, is answered like a neutral question. -/
theorem high_answers_like_neutral (f : AnswerFeature) :
    f.answer (.height .high) = f.answer .absent := by
  cases f <;> rfl

/-! ### Negative question forms in English -/

/-- The two varieties of English the book distinguishes by negative questions with *-n't*. In the
restrictive one such a question conveys only an expected positive answer; in the tolerant one it
can also convey an expected negative answer, and then licenses *either*, as Ladd observes. -/
inductive EnglishVariety where
  | restrictive
  | tolerant
  deriving DecidableEq, Repr

/-- The negations an English polar question with its negation in a given position can carry in a
variety, none for the positive question; for non-preposed *not* a low or a middle negation, as
speakers differ; for preposed *-n't* the high negation of the positive-bias reading and, in the
tolerant variety, a negation inside the clause, at a height the book does not fix. -/
def negations : EnglishVariety → Option Negation.Position → Set ClauseNegation
  | _, none => {.absent}
  | _, some .nonPreposed => {.height .low, .height .middle}
  | .restrictive, some .preposed => {.height .high}
  | .tolerant, some .preposed => {.height .low, .height .middle, .height .high}

/-- A question with *not* makes the negative alternative primary for all speakers, having the
inner reading, which conveys an expected negative answer. -/
theorem primaryPolarity_of_mem_negations_nonPreposed {v : EnglishVariety} {n : ClauseNegation}
    (hn : n ∈ negations v (some .nonPreposed)) : n.primaryPolarity = .negative := by
  cases v <;> rcases hn with rfl | rfl <;> rfl

/-- In the restrictive variety a question with *-n't* has only the outer reading. -/
theorem primaryPolarity_of_mem_negations_restrictive {n : ClauseNegation}
    (hn : n ∈ negations .restrictive (some .preposed)) : n.primaryPolarity = .positive := by
  rw [show n = .height .high from hn]
  rfl

/-- In the tolerant variety it also has the inner reading. -/
theorem exists_mem_negations_tolerant_primaryPolarity :
    ∃ n ∈ negations .tolerant (some .preposed), n.primaryPolarity = .negative :=
  ⟨.height .middle, by simp [negations], rfl⟩

/-- In the restrictive variety a question with *-n't* is answered like its positive counterpart,
whatever the particle. -/
theorem answer_of_mem_negations_restrictive {n : ClauseNegation}
    (hn : n ∈ negations .restrictive (some .preposed)) (f : AnswerFeature) :
    f.answer n = f.answer .absent := by
  rw [show n = .height .high from hn]
  exact high_answers_like_neutral f

/-- In the tolerant variety it need not be, since on a reading with the negation inside the
clause a bare *yes* does not answer it as it answers the positive question. -/
theorem exists_mem_negations_tolerant :
    ∃ n ∈ negations .tolerant (some .preposed),
      (english .yes).answer n ≠ (english .yes).answer .absent :=
  ⟨.height .middle, by simp [negations], by decide⟩

/-! ### The examples -/


/-- The features of each language's particles, by Glottocode and spelling. -/
def featureTable : List (String × List (String × AnswerFeature)) :=
  [("stan1293", [English.PolarityParticle.yes, .no].map fun p ↦ (p.form, english p)),
    ("swed1254", [Swedish.PolarityParticle.ja, .nej, .jo].map fun p ↦ (p.form, swedish p)),
    ("stan1290", [French.PolarityParticle.oui, .non, .si].map fun p ↦ (p.form, french p)),
    ("nucl1643", [Japanese.PolarityParticle.un, .uun].map fun p ↦ (p.form, japanese p))]

/-- The negation of a question, by where the annotation locates it. -/
def negationTable : List (String × ClauseNegation) :=
  [("low", .height .low), ("middle", .height .middle), ("middle behind an adverb", .screened),
    ("high", .height .high)]

/-- The alternatives an example confirms, as polarities relative to the positive alternative. -/
def polarityTable : List (String × Polarity) := [("p", .positive), ("not p", .negative)]

/-- An example of a single particle answering a question whose negation the example fixes. -/
structure Row where
  /-- The negation of the question. -/
  negation : ClauseNegation
  /-- The feature of the answer. -/
  feature : AnswerFeature
  /-- The alternative the answer confirms or is intended to confirm, if the example says. -/
  target : Option Polarity
  /-- The judgment of the answer. -/
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The row of an example whose question is neutral or whose negation is located, and whose
answer is a single particle of one of the four languages. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let negation ← if ex.feature? "question" = some "neutral" then some .absent
    else ex.parse? "negation" negationTable
  let table ← List.lookup ex.language featureTable
  let feature ← ex.parse? "answer" table
  let target := ex.parse? "confirms" polarityTable <|> ex.parse? "intended" polarityTable
  pure ⟨negation, feature, target, ex.judgment⟩

/-- The rows of the examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The answer is well formed and confirms the alternative the example targets, if any. -/
def Row.Predicted (r : Row) : Prop :=
  r.feature.answer r.negation ≠ none ∧
    (r.target = none ∨ r.feature.answer r.negation = r.target)

instance : DecidablePred Row.Predicted := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The rows include *Har Johan inte kommit?* answered by *\*Ja* and by *Jo* (Section 4.5). -/
theorem kommit_mem_rows :
    ⟨.height .middle, swedish .ja, none, .ungrammatical⟩ ∈ rows ∧
      ⟨.height .middle, swedish .jo, some .positive, .acceptable⟩ ∈ rows := by
  decide

/-- The mechanism predicts the judgment of every example answered by a single particle of the
study, whose question is neutral or whose negation the annotation locates, the example being
acceptable just when the answer is well formed and confirms the alternative it targets. -/
theorem judgment_iff_predicted : ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.Predicted) := by
  decide

end Holmberg2016
