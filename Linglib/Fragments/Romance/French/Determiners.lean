module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# French determiners

This file records the French determiners the studies consume. The quantificational determiners
are the carrier `QuantityWord`, whose members project to a `Quantifier` record by
`QuantityWord.toQuantifier` and denote the readings the literature makes available for them,
so `⟦QuantityWord.tous⟧` is `{every}`. French has no lexical dual universal, and Jeretic and
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

/-! ## Quantificational determiners -/

/-- The quantificational determiners are *tous*, *chaque*, *aucun*, *les deux*, *quelques* and the
adverb *toujours*. -/
inductive QuantityWord where
  | tous | chaque | aucun | les_deux | quelques | toujours
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The surface form. -/
def form : QuantityWord → String
  | .tous => "tous"
  | .chaque => "chaque"
  | .aucun => "aucun"
  | .les_deux => "les deux"
  | .quelques => "quelques"
  | .toujours => "toujours"

/-- *Tous*, *quelques* and *toujours* select the plural, *chaque* and *aucun* the singular, and
*les deux* the dual, the core concept it realizes. -/
def numberRestriction : QuantityWord → Option Number
  | .tous | .quelques | .toujours => some .plural
  | .chaque | .aucun => some .singular
  | .les_deux => some .dual

/-- Whether a word selects mass nouns, which only *tous* does. -/
def selectsMass : QuantityWord → Bool
  | .tous => true
  | _ => false

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form, numberRestriction := w.numberRestriction, selectsMass := w.selectsMass }

/-- All the words. -/
def toList : List QuantityWord := [.tous, .chaque, .aucun, .les_deux, .quelques, .toujours]

universe u

/-- The readings the literature makes available for a word. *Tous* and *chaque* read as
`every`, *quelques* as `Quantifier.GQ.some` and *les deux* as `both`; *toujours* has no
determiner reading. The n-word *aucun* reads as `no`, a negative quantifier
([de-swart-sag-2002]), or as `Quantifier.GQ.some`, an indefinite whose negation the clause
supplies ([zeijlstra-2004]). -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .tous | .chaque => {Quantifier.GQ.Family.every}
    | .aucun => {Quantifier.GQ.Family.no, Quantifier.GQ.Family.some}
    | .quelques => {Quantifier.GQ.Family.some}
    | .les_deux => {Quantifier.GQ.Family.both}
    | .toujours => ∅

end QuantityWord

/-! ## Articles -/

/-- *un* — indefinite article, singular. -/
def un : Article :=
  { form := "un"
  , definiteness := .indefinite
  , exponent := .dedicatedMorpheme }

/-- *les* — definite plural article. -/
def les : Article :=
  { form := "les"
  , definiteness := .definite
  , exponent := .dedicatedMorpheme
  , uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- All French quantifier entries. -/
def allQuantifiers : List Quantifier := QuantityWord.toList.map QuantityWord.toQuantifier

/-- All French article entries. -/
def allArticles : List Article := [un, les]

/-- The French determiner inventory. -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ allQuantifiers.map .quantifier

end French.Determiners
