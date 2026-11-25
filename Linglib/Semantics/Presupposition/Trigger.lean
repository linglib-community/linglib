module

public import Linglib.Semantics.Aspect.Phasal

/-!
# Presupposition triggers

A presupposition trigger is an expression whose sentences are true or false only where some
proposition, its presupposition, holds. This file defines the classifications of triggers that
lexical entries record. Abusch divides triggers into hard ones, whose presupposition resists
suspension, and soft ones, whose presupposition a context can suspend. Karttunen divides the
factive predicates into true factives and semi-factives. The adverbs and particles that trigger a
presupposition fall into classes by what they presuppose of their prejacent: a phasal adverb
presupposes a prior state and an iterative a prior occurrence, an additive and an exclusive relate
the prejacent to its alternatives, and a contrastive presupposes that an alternative is false.

The meanings are defined elsewhere. A sentence presupposing `A` and asserting `B` is the
conditional event `Trivalent.condEvent A B`, which lies below `B` in the knowledge order, and the
operators of the classes are `Presupposition.again`, `Aspect.Phasal.denote`, `Focus.additive` and
`Focus.only`.

## Main definitions

* `Presupposition.Hardness`: hard and soft triggers.
* `Presupposition.Factivity`: true factives and semi-factives.
* `Presupposition.TriggerClass`: the classes of adverbs and particles that trigger a
  presupposition.
* `Presupposition.TriggerItem`: the lexical record of such an adverb or particle.

## Implementation notes

The entry of a clause-embedding predicate records its factivity class where a source gives one,
and nothing otherwise: there is no class for a non-factive, so an entry without a class is not
counted as one. Whether a predicate is a trigger is derived, not recorded. What a predicate does
with the presuppositions of its complement is not recorded on its entry. It follows from the predicate's semantics: a factive, an
aspectual or an implicative passes them on unchanged, and an attitude verb makes its report
presuppose that the holder believes them, as Karttunen and Heim argue.

A phasal adverb carries the class of the phasal verbs, *still* that of *continue* and *no longer*
that of *stop*, so that one denotation serves an adverb and a verb. `TriggerClass` has no class
for a definite description, a cleft or a factive verb, which are triggers by their own entries and
constructions and are never a `TriggerItem`.

## References

* [abusch-2002]
* [abusch-2010]
* [karttunen-1971b]
* [karttunen-1974-presupposition]
* [heim-1992]
* [von-stechow-1996]
* [ippolito-2007]
* [kripke-2009]
-/

@[expose] public section

namespace Presupposition

/-- Whether a presupposition trigger is hard or soft, in the classification of [abusch-2002] and
[abusch-2010]. The presupposition of a hard trigger, *too*, *also*, *again* or a cleft, resists
suspension, and that of a soft trigger, *stop*, *know* or *win*, is suspended in a context that
leaves it open. -/
inductive Hardness where
  /-- A trigger whose presupposition a context that leaves it open does not suspend. -/
  | hard
  /-- A trigger whose presupposition can be suspended in context. -/
  | soft
  deriving DecidableEq, Repr

/-- The factivity class of a predicate ([karttunen-1971b]). -/
inductive Factivity where
  /-- A true factive such as *regret* or *forget*, whose complement follows even from the
  possibility of the sentence. -/
  | full
  /-- A semi-factive such as *realize* or *discover*, whose complement follows from the sentence
  and its negation only. -/
  | semi
  deriving DecidableEq, Repr

/-- The class of a presupposition trigger, by the kind of expression that hosts it. -/
inductive TriggerClass where
  /-- A phasal adverb presupposes the prior state of its class and asserts the result state, as a
  phasal verb does: *still* ([ippolito-2007]) and *no longer* both presuppose that the state held
  before, and differ in whether it holds now. Its meaning is `Aspect.Phasal.denote`. -/
  | phasal (t : Aspect.Phasal)
  /-- An iterative, *again*, presupposes a prior occurrence ([von-stechow-1996]). Its meaning is
  `Presupposition.again`. -/
  | iterative
  /-- An additive, *too* or *also*, presupposes that a distinct salient alternative satisfies
  the predicate, and is the paradigm anaphoric trigger ([kripke-2009]). Its meaning is
  `Focus.additive`. -/
  | additive
  /-- An exclusive, *only*, presupposes that an alternative at least as strong as its prejacent
  is true. Its meaning is `Focus.only`. -/
  | exclusive
  /-- A contrastive, *instead*, presupposes that a salient alternative is false. -/
  | contrastive
  deriving DecidableEq, Repr

/-- A presupposition trigger that is an adverb, particle or affix, with its trigger class. A
clause-embedding predicate's presuppositions are recorded on its `Clause.Embedding`. -/
structure TriggerItem where
  /-- The citation form, a romanization where the language is not written in Latin script. -/
  form : String
  /-- The native-script form of a romanized item. -/
  script : Option String := none
  /-- The trigger class. -/
  triggerClass : TriggerClass
  deriving DecidableEq, Repr

end Presupposition
