module

public import Linglib.Syntax.Case.Basic

/-!
# Icelandic case

Icelandic has four cases, the nominative, the accusative, the dative and the genitive, in the
order of the school paradigms, and its nouns, adjectives, articles and pronouns inflect for all
four in both numbers, as Thráinsson's overview of the nominal inflection sets out. Subjects
and objects alike bear all four: the verbs of `Icelandic.Verbs` record the case frame of each,
and every case is the case of some subject and of some object
(`Icelandic.Verbs.subject_cases`, `Icelandic.Verbs.object_cases`). Blake gives the system as the
four-case stage of his hierarchy, beside German's (`Studies/Blake1994.lean`).

## Main definitions

* `Icelandic.Case`, `Icelandic.Case.label`: the four cases, and the comparative value each is
  named for.

## References

* [thrainsson-2007]
* [blake-1994]
-/

@[expose] public section

namespace Icelandic

/-- The four cases, in the order of the school paradigms. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  /-- The genitive. -/
  | gen
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | dat => .dat
  | gen => .gen

end Icelandic
