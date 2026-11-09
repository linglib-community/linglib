module

public import Linglib.Data.Examples.Judgment

/-!
# Verb class catalogues: schema

Typed schema for a book's catalogue of verb classes: for each class, the section number and title
the book prints, its members, and its properties, each an alternation of the book's catalogue of
alternations, named by its section number, or a further property. A property is a numbered example
line of the class's entry, so it carries the mark the book puts before an example (`Judgment`), and
it applies to the members the book's qualification leaves it (`Scope.AppliesTo`). Generated
catalogues live in `Data/VerbClasses/<Book>.lean`, emitted from the canonical `<Book>.json` by
`scripts/gen_verb_classes.py`.

This is data: it imports from `Linglib/` only the marks of `Data/Examples` and states no theorems.
The vocabulary is that of Levin's catalogue: an alternation is named by its section number in her
Part One, and the further properties are those her class descriptions name. A catalogue with
another vocabulary, such as VerbNet's thematic roles and frames, needs its own schema.

## References

* [levin-1993]
-/

@[expose] public section

namespace Data.VerbClasses

/-- The members of a class a property applies to, as the book qualifies the property: all of them
but those it excepts, as in "except *kill*", when it does not qualify it otherwise, or "most",
"many", "some" or "a few" verbs. -/
inductive Scope where
  | all (exceptions : List String := [])
  | most
  | many
  | some
  | few
  deriving DecidableEq, Repr, Inhabited

/-- The property applies to the member `m`: the book qualifies it by no share of the class and
does not except `m`. -/
def Scope.AppliesTo : Scope → String → Prop
  | .all exceptions, m => m ∉ exceptions
  | _, _ => False

instance : ∀ s m, Decidable (Scope.AppliesTo s m)
  | .all exceptions, m => inferInstanceAs (Decidable (m ∉ exceptions))
  | .most, _ | .many, _ | .some, _ | .few, _ => .isFalse id

/-- A derived nominal may have only its active or only its passive interpretation. -/
inductive NominalReading where
  | active
  | passive
  deriving DecidableEq, Repr, Fintype

/-- The goal of a verb of communication is expressed by an object or by a *to* phrase. -/
inductive GoalPhrase where
  | object
  | toPhrase
  deriving DecidableEq, Repr, Fintype

/-- A sentential complement's goal is expressed as the book leaves it, not at all, by a required
phrase, or by an optional one. -/
inductive GoalRealization where
  | unspecified
  | absent
  | required (g : GoalPhrase)
  | optional (g : GoalPhrase)
  deriving DecidableEq, Repr

/-- A property the book lists for a class that is not one of its alternations. -/
inductive PageProperty where
  | zeroRelatedNominal
  | erNominal
  | ingNominal
  | processNominal
  | resultNominal
  | derivedNominal (reading : NominalReading)
  | ableAdjective
  | zeroRelatedAdjective
  | sententialComplement (goal : GoalRealization)
  | extraposition
  | directSpeech
  | parentheticalUse
  | infinitivalCopularClause
  | measurePhrase
  | pathPhrase
  | depictivePhrase
  | substanceObject
  | bodyPartObject
  | collectiveNPSubject
  | impersonalPassive
  | passivePrepositionChoice
  | fromPhrase
  | withAlternatesWithIn
  | ofAlternatesWithOut
  | unspecifiedObjectPlusLocativePP
  | coreferentialInterpretationVaries
  deriving DecidableEq, Repr

/-- A property line names an alternation by its section number in the book's catalogue of
alternations, or a further property. -/
inductive Heading where
  | alternation (number : List ℕ)
  | property (p : PageProperty)
  deriving DecidableEq, Repr

/-- The section number of the alternation a heading names, if it names one. -/
def Heading.number? : Heading → Option (List ℕ)
  | .alternation n => some n
  | .property _ => none

/-- A line of a class's property table records what it names, the mark the book puts before it,
the members it applies to, and any further qualifier the book prints with it, such as "based on
*with* variant". -/
structure PropertyLine where
  heading : Heading
  judgment : Judgment
  scope : Scope
  qualifier : Option String
  deriving DecidableEq, Repr

/-- A verb class as the book describes it has the section number and title the book prints, the
page on which the class begins, the members and those of them the book marks as doubtful, and the
property table in the book's order. -/
structure VerbClass where
  number : String
  title : String
  page : ℕ
  members : List String
  doubtful : List String
  properties : List PropertyLine
  deriving Repr, Inhabited

end Data.VerbClasses
