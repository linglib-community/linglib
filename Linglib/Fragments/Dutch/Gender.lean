module

public import Linglib.Syntax.Gender.Basic

/-!
# Dutch gender

Dutch has two controller genders. The common gender, which Broekhuis and Corver's grammar calls
non-neuter, is the merger of the historical masculine and feminine and is the gender of the
*de*-words; the neuter is the gender of the *het*-words. The definite article and the
demonstratives distinguish the two genders in the singular only, and
`Dutch.Determiners.singular` records that evidence. The genders are read off the determiners
rather than the pronouns, since pronominal agreement is partly semantic and follows the
individuation of the referent ([kraaikamp-2012]).

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume V: Nouns and Noun Phrases 2: Prenominal
  Elements, Pronouns and Syntactic Uses of Noun Phrases* (2026)][broekhuis-corver-2026b]
* [M. Kraaikamp, *The Semantics of the Dutch Gender System* (2012)][kraaikamp-2012]
-/

@[expose] public section

namespace Dutch.Gender

/-- Dutch has two controller genders, the common gender of the *de*-words and the neuter of the
*het*-words. -/
inductive Value where
  | common
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Each Dutch gender bears the comparative label of the same name. -/
def Value.toLabel : Value → Gender.Label
  | .common => .common
  | .neuter => .neuter

end Dutch.Gender
