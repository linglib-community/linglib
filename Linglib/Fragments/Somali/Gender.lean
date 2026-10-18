module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Agreement.Classes
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Somali noun gender

This file defines the two Somali controller genders, the remote definite article and the
verbal subject prefix each takes in each number, and the nouns the sources cite.

The remote definite article is polar. The masculine singular and the feminine plural take
*-kii*, the feminine singular and the masculine plural *-tii*, so changing gender or number
alone changes the article and changing both restores it. The subject prefix of the verbs
that conjugate by prefix, such as *imid* 'came', is not polar. It is *y-* for the masculine
singular and for both plurals and *t-* for the feminine singular alone. Masculine nouns whose
plural is formed by reduplication, *nin* ~ *niman* 'man', keep the singular article in the
plural.

## Main definitions

* `Somali.Gender.Value` — the controller genders
* `Somali.Gender.Value.article`, `Somali.Gender.Value.verbPrefix` — the article and the
  verbal prefix by gender and number
* `Somali.Gender.Noun`, `Somali.Gender.allNouns` — the nouns, with their plurals

## Main results

* `Somali.Gender.polar_article` — the article is polar
* `Somali.Gender.faithful_article`, `Somali.Gender.faithful_verbPrefix` — either exponent
  distinguishes the two genders

## References

* [J. Saeed, *Somali* (1999)][saeed-1999]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
-/

@[expose] public section

namespace Somali.Gender

open Number.System (singularPlural)

/-! ### Genders and their exponents -/

/-- The two controller genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine

/-- The basic forms of the remote definite article. After a vowel other than *i*, *-kii* is
*-hii*, and after any vowel *-tii* is *-dii*. -/
inductive Article where
  | kii
  | tii
  deriving DecidableEq, Repr, Fintype

/-- Somali distinguishes the singular and the plural. -/
abbrev numberSystem : Number.System := .singularPlural

/-- The article a gender takes in each number. -/
def Value.article (g : Value) : numberSystem.values → Article :=
  singularPlural.elim (match g with | .masc => .kii | .fem => .tii)
    (match g with | .masc => .tii | .fem => .kii)

/-- The subject prefix of the verbs that conjugate by prefix. -/
inductive VerbPrefix where
  | y
  | t
  deriving DecidableEq, Repr, Fintype

/-- The verbal prefix a gender takes in each number. -/
def Value.verbPrefix (g : Value) : numberSystem.values → VerbPrefix :=
  singularPlural.elim (match g with | .masc => .y | .fem => .t) .y

/-- The article is polar. -/
theorem polar_article : Gender.Polar Value.article := by decide

/-- The article distinguishes the two genders. -/
theorem faithful_article : Gender.Faithful Value.article := polar_article.faithful

/-- The verbal prefix distinguishes the two genders. -/
theorem faithful_verbPrefix : Gender.Faithful Value.verbPrefix := by decide

/-! ### Nouns -/

/-- A Somali noun with its gender, its plural form and whether that plural is formed by
reduplication. -/
structure Noun extends GenderedNoun Value where
  /-- The plural form. -/
  plural : String
  /-- Whether the plural is formed by reduplication and so keeps the singular article. -/
  reduplicatedPlural : Bool
  deriving DecidableEq, Repr

/-- The article a noun takes in the singular and in the plural. -/
def Noun.article (n : Noun) (num : numberSystem.values) : Article :=
  n.gender.article (if n.reduplicatedPlural then numberSystem.value .singular else num)

/-- The noun *ìnan* 'boy'. -/
def inan : Noun := ⟨⟨⟨"ìnan", "boy"⟩, .masc, some .masculine⟩, "inammá", false⟩

/-- The noun *inán* 'girl'. -/
def inan' : Noun := ⟨⟨⟨"inán", "girl"⟩, .fem, some .feminine⟩, "ináma", false⟩

/-- The noun *nin* 'man', whose plural *niman* is reduplicated. -/
def nin : Noun := ⟨⟨⟨"nin", "man"⟩, .masc, some .masculine⟩, "niman", true⟩

/-- The nouns the sources cite. -/
def allNouns : List Noun := [inan, inan', nin]

end Somali.Gender
