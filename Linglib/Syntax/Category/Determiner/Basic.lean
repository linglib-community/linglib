/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Image
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Feature.Number.Basic
public import Linglib.Semantics.Quantifier.Symbol

/-!
# Determiners

This file defines the determiner as a lexical record and the determiner inventory of a language.
A determiner is an article, a demonstrative, a quantificational determiner or a possessive, and
an inventory is a list of them.

The records hold what a descriptive grammar states of a form. An article records the degrees of
definiteness it marks, the number it selects and the uses of a definite description it expones,
among the anaphoric use, the two situational uses and the two bridging uses that Hawkins
distinguishes. A quantificational determiner records the number it selects, whether it takes mass
nouns and the determiner symbols that name its readings.

## Main definitions

* `Determiner`: the base record, a surface form.
* `Article`, `DemonstrativeDeterminer`, `QuantificationalDeterminer`, `PossessiveDeterminer`: the
  four kinds of determiner.
* `Determiner.Entry`: a determiner of one of the four kinds, with `Determiner.Entry.kind` and
  `Determiner.Entry.Selects`.
* `Determiner.Inventory`: the determiners of a language.

## Implementation notes

The records carry no denotation and no classification by a theory of definiteness. Articles,
demonstratives and possessives denote definite descriptions, a determiner symbol denotes a
generalized quantifier, and the strengths of Schwarz are read off an article's uses; each is
defined in a file that imports this one.

An inventory is a type synonym of `List Determiner.Entry` and not an abbreviation, so that its
operations resolve by dot notation; its membership is the list's.

## References

* [hawkins-1978]
-/

@[expose] public section


/-- A determiner has a surface form, a representative morpheme or a construction label. The
specializations extend it. -/
structure Determiner where
  /-- The surface form. -/
  form : String
  deriving DecidableEq, Repr

namespace Determiner

/-- An article is exponed by a dedicated morpheme or by a classifier construction. Whether the
form marks definiteness is a matter of the uses it expones, not of its exponent. -/
inductive Exponent where
  /-- A dedicated article morpheme, as English *the* and German *der*. -/
  | dedicatedMorpheme
  /-- A bare classifier phrase, as the Cantonese definite [Clf-N]. -/
  | classifierPhrase
  /-- A numeral-classifier phrase, as the Cantonese indefinite [jat-Clf-N]. -/
  | numeralClassifier
  deriving DecidableEq, Repr

end Determiner

/-! ### The specializations -/

/-- An article is the definite or indefinite determiner. -/
structure Article extends Determiner where
  /-- The degrees of definiteness of the nominals the article can mark: the definite degree for a
  definite article and both indefinite degrees for a plain indefinite one. -/
  definiteness : Finset Definiteness
  /-- The exponent of the article. -/
  exponent : Determiner.Exponent
  /-- The uses of a definite description the article expones, none for an indefinite. -/
  uses : Finset Definite.Use := ∅
  /-- The grammatical number the article selects, or none when it is number-neutral, as English
  *a* selects the singular. -/
  numberRestriction : Option Number := none
  deriving DecidableEq

/-- A demonstrative determiner carries its deictic content, the participant sets of the referents
in whose vicinity it locates its referent. -/
structure DemonstrativeDeterminer extends Determiner where
  /-- The participant sets of the referents in whose vicinity the form locates its referent. -/
  deixis : Finset (Finset SpeechAct.Role)
  deriving DecidableEq

/-- A quantificational determiner records its readings, the determiner symbols whose
denotations it may have, and what its denotation leaves open, the grammatical number it selects
and whether it selects mass nouns, since synonymous determiners such as *every* and *all* differ
there. Everything a reading fixes, its force, monotonicity, strength and conservativity, is a
theorem about the reading. -/
structure QuantificationalDeterminer extends Determiner where
  /-- The readings available for the determiner, empty when its standard is left to context. -/
  readings : Finset Quantifier.Det.Symbol := ∅
  /-- The grammatical number the determiner selects, or none when it is number-neutral. -/
  numberRestriction : Option Number := none
  /-- The determiner selects mass nouns. -/
  selectsMass : Bool := false
  deriving DecidableEq

/-- A possessive determiner denotes a definite through a possession relation. -/
structure PossessiveDeterminer extends Determiner
  deriving DecidableEq, Repr

namespace Determiner

/-! ### Entries -/

/-- An entry is a determiner of one of the four kinds. -/
inductive Entry where
  | article (a : Article)
  | demonstrative (d : DemonstrativeDeterminer)
  | quantifier (q : QuantificationalDeterminer)
  | possessive (p : PossessiveDeterminer)
  deriving DecidableEq

namespace Entry

/-- The kind of an entry. -/
inductive Kind where
  | article
  | demonstrative
  | quantifier
  | possessive
  deriving DecidableEq, Repr

/-- The kind of an entry. -/
def kind : Entry → Kind
  | .article _ => .article
  | .demonstrative _ => .demonstrative
  | .quantifier _ => .quantifier
  | .possessive _ => .possessive

/-- The degrees of definiteness an entry can mark are an article's; a demonstrative, quantifier
or possessive marks none by its lexicon. -/
def definiteness : Entry → Finset Definiteness
  | .article a => a.definiteness
  | .demonstrative _ | .quantifier _ | .possessive _ => ∅

/-- The uses of a definite description an entry expones are an article's; a demonstrative,
quantifier or possessive expones none by its lexicon. -/
def uses : Entry → Finset Definite.Use
  | .article a => a.uses
  | .demonstrative _ | .quantifier _ | .possessive _ => ∅

/-- The grammatical number an entry selects is an article's or a quantifier's restriction; a
demonstrative or possessive selects none. -/
def numberRestriction : Entry → Option Number
  | .article a => a.numberRestriction
  | .quantifier q => q.numberRestriction
  | .demonstrative _ | .possessive _ => none

variable (e : Entry)

/-- An entry applies to a nominal of number `num` when it selects that number or none. -/
def Selects (num : Number) : Prop := ∀ n ∈ e.numberRestriction, n = num

instance (num : Number) : Decidable (e.Selects num) :=
  inferInstanceAs (Decidable (∀ n ∈ e.numberRestriction, n = num))

end Entry

/-! ### Inventories -/

/-- A determiner inventory is the list of a language's determiners. -/
def Inventory := List Entry

namespace Inventory

instance : Membership Entry Inventory := inferInstanceAs (Membership Entry (List Entry))
instance : DecidableEq Inventory := inferInstanceAs (DecidableEq (List Entry))
instance (ds : Inventory) (p : Entry → Prop) [DecidablePred p] : Decidable (∃ e ∈ ds, p e) :=
  List.decidableBEx p ds
instance (ds : Inventory) (p : Entry → Prop) [DecidablePred p] : Decidable (∀ e ∈ ds, p e) :=
  List.decidableBAll p ds

end Inventory

end Determiner
