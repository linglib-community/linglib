module

public import Linglib.Discourse.Response
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Questions.Hamblin
public import Mathlib.Data.Fintype.Sum

/-!
# Polar interrogatives and their answers

This file formalizes Holmberg's syntax of yes–no questions and their answers. A
`PolarInterrogative` is a sentence radical, its positive alternative, with a `ClauseNegation`,
the negation of the clause, if any, with its height relative to the polarity head. Its primary
alternative is the radical under the polarity the negation gives it, and it denotes the polar
question of that alternative; a negative interrogative and its positive counterpart denote the
same question, differing only in which alternative is primary
(`PolarInterrogative.denote_eq_polar_radical`), whose alternatives are the polarity alternatives
of the radical (`PolarInterrogative.alt_denote`).

The polarity head is merged unvalued, and a short answer merges a focused valued polarity
feature, spelled out by an answer particle, with the clause inherited from the question,
normally elided. An `AnswerFeature` is that feature: a valued [+Pol] or [−Pol], or the
affirmative [+Pol, REV] of a polarity-reversing particle such as Swedish *jo*, which eliminates
the negation in the answer. Given the negation of the clause the answer inherits,
`AnswerFeature.answer` computes the polarity of the alternative the answer confirms, relative to
the question's positive alternative, or `none` for an ill-formed answer. A negation out of the
polarity head's reach, such as a low, VP-internal one, leaves the particle to value the head,
and the value composes with the negation; a middle negation values the head itself, so that a
negative particle agrees with it and a plain affirmative clashes with it.

The answers a feature gives to the questions whose negations a language allows form a set of
`Discourse.Response`s (`AnswerFeature.responses`), whose polarity features are those of Farkas
and Bruce, to whom Holmberg credits REV. The mechanism derives the two systems for answering
negative questions from the syntax of negation. Out of the head's reach a valued feature fixes
the relative polarity of the answer, the truth-based system
(`AnswerFeature.responses_value_of_forall_not_valuesHead`), so that the affirmative feature
confirms the negative alternative just when the negation is low
(`AnswerFeature.confirmsNegativeQuestion_responses_positive_iff`). A negation valuing the head
leaves only the negative feature, which fixes the absolute polarity, the polarity-based system
(`AnswerFeature.responses_value_negative_of_valuesHead`,
`AnswerFeature.responses_value_positive_of_valuesHead`). A reversing feature gives exactly the
[reverse, +] answers (`AnswerFeature.responses_reversing`).

## Implementation notes

* What decides the system is whether the negation can value the polarity head
  (`ClauseNegation.ValuesHead`); the height of the negation matters only through that, as
  Holmberg argues for Thai, whose negation cannot value the head from inside the complement of
  the question particle. Heights classify constructions, not languages: English *not* is read
  low by some speakers and middle by others, and *-n't* in positive-bias questions is high.
* REV needs a negation in the answer to eliminate, so a reversing particle is ill formed after a
  neutral or a positive-bias question. Colloquial Swedish, where *jo* can confirm the positive
  alternative of any yes–no question (Holmberg's footnote to the section on positive and
  negative bias), is not modelled.
* The two versions of the negative particle in polarity-based languages, an interpretable one
  valuing the head and an uninterpretable one agreeing with a negation that values it, are one
  `AnswerFeature.value .negative`, whose agreement is built into `AnswerFeature.answer`.
* The reading of a polar interrogative is an `Option Polarity`: `none` for a positive question,
  and for a negative one the polarity of the proposition it double-checks, relative to its
  radical. Ladd's outer reading, double-checking `p`, is `some .positive`, and his inner
  reading, double-checking `¬p`, is `some .negative`. Each analysis computes it from its own
  structure; here it is the primary polarity of the clause's negation
  (`ClauseNegation.primaryPolarity`), negative for a negation inside the clause and positive for a
  high one.
* The position of the negation (`NegationPosition`) follows Romero and Han, and the form of a
  polar interrogative, an `Option NegationPosition`, gives Romero's PosQ, LoNQ and HiNQ.
  Readings and forms are related, not identified: the preposed *-n't* of *Isn't this the road to
  Lund?* has both readings for some speakers of English, so each language or variety relates a
  form to a set of readings.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [ladd-1981]
* [romero-han-2004]
* [romero-2024]
-/
@[expose] public section

/-- The feature an answer particle spells out, a valued polarity feature or the affirmative
polarity-reversing feature of *jo*, `[jo, +Pol, REV]`. -/
inductive AnswerFeature where
  /-- A valued polarity feature, [+Pol] or [−Pol]. -/
  | value (p : Polarity)
  /-- [+Pol, REV], positive polarity eliminating a negation in the answer. -/
  | reversing
  deriving DecidableEq, Repr

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

/-- The position of the negation of a negative polar interrogative relative to the rest of the
clause, preposed with the finite verb, as English *n't* in *Isn't Jane coming?*, or not, as *not*
in *Is Jane not coming?*. What matters is the relative position, not a particular one. -/
inductive NegationPosition where
  /-- Negation preposed with the finite verb. -/
  | preposed
  /-- Negation in its clause-internal position. -/
  | nonPreposed
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

/-- The answers a feature gives to polar questions whose negations are among `N`, each given by
the polarity of the question's primary alternative and that of the alternative the answer
confirms. -/
def responses (f : AnswerFeature) (N : Set ClauseNegation) : Set Discourse.Response :=
  {x | x.reactsTo = .polarQuestion ∧
    ∃ n ∈ N, n.primaryPolarity = x.antecedent ∧ f.answer n = some x.polarity}

/-- Out of the reach of every negation of `N`, a valued feature fixes the relative polarity of
the answer to the question's primary alternative, as in the truth-based system. -/
theorem responses_value_of_forall_not_valuesHead {p : Polarity} {N : Set ClauseNegation}
    (hN : ∀ n ∈ N, ¬ n.ValuesHead) :
    (value p).responses N = {x | x.reactsTo = .polarQuestion ∧
      x.antecedent ∈ primaryPolarity '' N ∧ x.relative = p} := by
  ext ⟨m, a, s⟩
  simp only [responses, Set.mem_ofPred_eq, Set.mem_image, Discourse.Response.relative_mk]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨n, hn, rfl, h⟩
    rw [answer_value_of_not_valuesHead (hN n hn), Option.some_inj] at h
    exact ⟨⟨n, hn, rfl⟩, by rw [← h, mul_div_cancel_right]⟩
  · rintro ⟨⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, rfl, by rw [answer_value_of_not_valuesHead (hN n hn), div_mul_cancel]⟩

/-- A negation valuing the head leaves the negative feature only the confirmation of the negative
alternative, its absolute polarity, as in the polarity-based system. -/
theorem responses_value_negative_of_valuesHead (hn : n.ValuesHead) :
    (value .negative).responses {n} = {⟨.polarQuestion, .negative, .negative⟩} := by
  obtain rfl : n = .height .middle := hn
  ext ⟨m, a, s⟩
  simp only [responses, Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left]
  cases m <;> cases a <;> cases s <;> decide

/-- A negation valuing the head leaves the affirmative feature no answer. -/
theorem responses_value_positive_of_valuesHead (hn : n.ValuesHead) :
    (value .positive).responses {n} = ∅ := by
  obtain rfl : n = .height .middle := hn
  ext ⟨m, a, s⟩
  simp only [responses, Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eq_left,
    Set.mem_empty_iff_false, iff_false]
  cases m <;> cases a <;> cases s <;> decide

/-- REV is [reverse, +]. Once some negation of `N` is inside the clause, a reversing feature
gives exactly the positive answers reversing the primary alternative. -/
theorem responses_reversing {N : Set ClauseNegation} (hN : ∃ n ∈ N, n.InClause) :
    reversing.responses N = {x | x.reactsTo = .polarQuestion ∧ x.relative = .negative ∧
      x.polarity = .positive} := by
  obtain ⟨n₀, hn₀, hi₀⟩ := hN
  ext ⟨m, a, p⟩
  simp only [responses, Set.mem_ofPred_eq, Discourse.Response.relative_mk]
  constructor
  · rintro ⟨rfl, n, -, rfl, h⟩
    by_cases hi : n.InClause
    · rw [answer_reversing_of_inClause hi, Option.some_inj] at h
      subst h
      rw [primaryPolarity_of_inClause hi]
      exact ⟨rfl, rfl, rfl⟩
    · rw [answer_reversing_of_not_inClause hi] at h
      cases h
  · rintro ⟨rfl, ha, rfl⟩
    refine ⟨rfl, n₀, hn₀, ?_, answer_reversing_of_inClause hi₀⟩
    rw [primaryPolarity_of_inClause hi₀]
    cases a
    · exact absurd ha (by decide)
    · rfl

/-- The answers of a feature to questions whose negations are among `N` confirm the negative
alternative of a negative question iff some negation of `N` inside the clause yields it. -/
theorem confirmsNegativeQuestion_responses_iff {f : AnswerFeature} {N : Set ClauseNegation} :
    Discourse.Response.ConfirmsNegativeQuestion (f.responses N) ↔
      ∃ n ∈ N, n.InClause ∧ f.answer n = some .negative := by
  simp only [Discourse.Response.ConfirmsNegativeQuestion, responses, Set.mem_ofPred_eq,
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
