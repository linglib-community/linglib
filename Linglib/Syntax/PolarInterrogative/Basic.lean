module

public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Questions.Hamblin
public import Mathlib.Data.Fintype.Sum

/-!
# Polar interrogatives

A `PolarInterrogative` is a sentence radical, its positive alternative, with the negation of its
clause, if any (`PolarInterrogative.ClauseNegation`), placed relative to the polarity head as in
Holmberg's syntax of yes–no questions. Its primary alternative is the radical under the polarity
the negation gives it, and it denotes the polar question of that alternative. A negative
interrogative and its positive counterpart therefore denote the same question, differing only in
which alternative is primary (`PolarInterrogative.denote_eq_polar_radical`), and the
alternatives are the polarity alternatives of the radical (`PolarInterrogative.alt_denote`).

## Main definitions

* `PolarInterrogative`: a sentence radical with the negation of its clause.
* `PolarInterrogative.NegationHeight`, `PolarInterrogative.ClauseNegation`: the negation of a
  clause relative to its polarity head.
* `PolarInterrogative.NegationPosition`: preposed or non-preposed negation.

## Implementation notes

* Heights classify constructions, not languages: English *not* is read low by some speakers and
  middle by others, and *-n't* in positive-bias questions is high.
* The reading of a polar interrogative is an `Option Polarity`: `none` for a positive question,
  and for a negative one the polarity of the proposition it double-checks, relative to its
  radical. Ladd's outer reading, double-checking `p`, is `some .positive`, and his inner
  reading, double-checking `¬p`, is `some .negative`. Each analysis computes it from its own
  structure; here it is the primary polarity of the clause's negation
  (`PolarInterrogative.ClauseNegation.primaryPolarity`), negative for a negation inside the
  clause and positive for a high one.
* The position of the negation follows Romero and Han, and the form of a polar interrogative,
  an `Option NegationPosition`, gives Romero's PosQ, LoNQ and HiNQ. Readings and forms are
  related, not identified: the preposed *-n't* of *Isn't this the road to Lund?* has both
  readings for some speakers of English, so each language or variety relates a form to a set of
  readings.

## References

* [holmberg-2016]
* [ladd-1981]
* [romero-han-2004]
* [romero-2024]
-/

@[expose] public section

namespace PolarInterrogative

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

end PolarInterrogative

/-- A polar interrogative, given by its sentence radical, the positive alternative, and its
negation. -/
structure PolarInterrogative (W : Type*) where
  /-- The sentence radical, the positive alternative. -/
  radical : Set W
  /-- The negation of the interrogative. -/
  negation : PolarInterrogative.ClauseNegation

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
