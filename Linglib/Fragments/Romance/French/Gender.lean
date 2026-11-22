module

public import Linglib.Morphology.Morph
public import Mathlib.Tactic.DeriveFintype

/-!
# French gender

French has two genders, the masculine and the feminine, shown by the agreement of articles and
adjectives with the noun: *un grand garçon* 'a big boy' and *un grand jardin* 'a big garden'
beside *une grande femme* 'a big woman' and *une grande fleur* 'a big flower'.

## References

* [corbett-1991]
-/

@[expose] public section

namespace French.Gender

/-- The two genders. -/
inductive Value where
  | masculine
  | feminine
  deriving DecidableEq, Repr, Fintype

/-- The indefinite article, *un* with a masculine noun and *une* with a feminine one. -/
def indefiniteArticle : Value → String
  | .masculine => "un"
  | .feminine => "une"

/-- *-e*, the feminine suffix of an adjective in writing, as in *grand-e*. -/
def feminineSuffix : Morphology.Morph := .suff "e"

end French.Gender
