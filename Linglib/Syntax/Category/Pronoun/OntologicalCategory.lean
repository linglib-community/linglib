module

public import Linglib.Data.UD.UPOS

/-!
# Ontological categories of pro-forms

The members of an interrogative or indefinite series differ in the ontological category they
stand for: a person (*who*, *someone*), a thing (*what*, *something*), a place (*where*,
*somewhere*) and so on. The pronoun types of a language express roughly the same categories, so
that its interrogatives, demonstratives, relatives and indefinites line up in a table of
correlatives, which takes in the pronominal adverbs. The category fixes the word class of the
member: a pronoun for a person or a thing, a determiner for a property or a selection, an adverb
for a place, a time, a manner or a reason.

## TODO

The word class of an amount pro-form differs across languages and is not a datum of the entry;
`Pronoun.OntologicalCategory.upos` gives it a pronoun's.

## References

* [haspelmath-1997]
-/

@[expose] public section

/-- The ontological categories of pro-forms. Person, thing, property, place, time, manner and
amount are the seven Haspelmath finds most often expressed by simple means, the cut between
person and thing (*somebody* against *something*) being made nearly everywhere. Many languages
add a determiner (*which*) distinct from the substantival *who* and *what* and the adjectival
*what kind*, and some a reason (*why*), which English and German have as an interrogative but
not as an indefinite. -/
inductive Pronoun.OntologicalCategory where
  /-- Person is the category of *somebody*, *someone* and interrogative *who*. -/
  | person
  /-- Thing is the category of *something* and interrogative *what*. -/
  | thing
  /-- Property or kind is the category of *some kind of* and interrogative *what kind*. -/
  | property
  /-- Place is the category of *somewhere* and interrogative *where*. -/
  | place
  /-- Time is the category of *sometime* and interrogative *when*. -/
  | time
  /-- Manner is the category of *somehow* and interrogative *how*. -/
  | manner
  /-- Amount is the category of *some amount* and interrogative *how much*. -/
  | amount
  /-- Determiner is the category of *some* N and interrogative *which*. -/
  | determiner
  /-- Reason is the category of *for some reason* and interrogative *why*. -/
  | reason
  deriving DecidableEq, Repr

namespace Pronoun.OntologicalCategory

/-- The word class of a pro-form: a pronoun where it stands for a person or a thing, a determiner
where it stands for a property or selects among the referents of a noun, and an adverb where it
stands for a place, a time, a manner or a reason. -/
def upos : OntologicalCategory → UD.UPOS
  | .person | .thing | .amount => .PRON
  | .property | .determiner => .DET
  | .place | .time | .manner | .reason => .ADV

end Pronoun.OntologicalCategory
