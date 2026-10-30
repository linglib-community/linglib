module

public import Linglib.Semantics.Quantification.Determiner

/-!
# French determiners

This file records the French determiners the studies consume. The quantificational determiners
are `QuantificationalDeterminer` records with the readings the literature makes available for
them, so `⟦tous⟧` is `{every}`. French has no lexical dual universal, and Jeretic and
colleagues take *les deux* to serve as its indirect alternative, marked with the dual number it
realizes; *toujours* is the adverbial universal they set beside English *always*, and has no
determiner reading. The articles *un* and *les* are `Article`s.

## References

* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [chemla-2007]
* [de-swart-sag-2002]
* [zeijlstra-2004]
-/

@[expose] public section

namespace French.Determiners

/-! ## Quantificational determiners

The n-word *aucun* reads as `no`, a negative quantifier ([de-swart-sag-2002]), or as
`Quantifier.Det.some`, an indefinite whose negation the clause supplies ([zeijlstra-2004]). -/

/-- *Tous*, read as `every`, with a plural or a mass noun. -/
def tous : QuantificationalDeterminer :=
  { form := "tous", readings := {.every}, numberRestriction := some .plural, selectsMass := true }

/-- *Chaque*, read as `every`, with a singular noun. -/
def chaque : QuantificationalDeterminer :=
  { form := "chaque", readings := {.every}, numberRestriction := some .singular }

/-- *Aucun*, read as `no` or as `Quantifier.Det.some`, with a singular noun. -/
def aucun : QuantificationalDeterminer :=
  { form := "aucun", readings := {.no, .some}, numberRestriction := some .singular }

/-- *Les deux*, read as `both`, with the dual, the core concept it realizes. -/
def les_deux : QuantificationalDeterminer :=
  { form := "les deux", readings := {.both}, numberRestriction := some .dual }

/-- *Quelques*, read as `Quantifier.Det.some`, with a plural noun. -/
def quelques : QuantificationalDeterminer :=
  { form := "quelques", readings := {.some}, numberRestriction := some .plural }

/-- The adverb *toujours*, with no determiner reading. -/
def toujours : QuantificationalDeterminer :=
  { form := "toujours", numberRestriction := some .plural }

/-! ## Articles -/

/-- *un* — indefinite article, singular. -/
def un : Article :=
  { form := "un"
  , definiteness := .indefinite
  , exponent := .dedicatedMorpheme
  , numberRestriction := some .singular }

/-- *les* — definite plural article. -/
def les : Article :=
  { form := "les"
  , definiteness := .definite
  , exponent := .dedicatedMorpheme
  , uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- All French quantifier entries. -/
def allQuantifiers : List QuantificationalDeterminer :=
  [tous, chaque, aucun, les_deux, quelques, toujours]

/-- All French article entries. -/
def allArticles : List Article := [un, les]

/-- The French determiner inventory. -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ allQuantifiers.map .quantifier

end French.Determiners
