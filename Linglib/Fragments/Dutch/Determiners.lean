module

public import Linglib.Fragments.Dutch.Gender
public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Dutch determiners

This file records the Dutch articles and demonstratives after Broekhuis and Corver's grammar.
The definite article is *de* with common-gender singulars and with every plural and *het* with
neuter singulars, and it is one syncretic definite over Schwarz's use types. The
indefinite article *een* occurs with singular count nouns only, since indefinite plural and mass
noun phrases are bare. The negative article *geen* occurs with singular, plural and mass nouns
alike, and the grammar argues that it is a quantifier rather than an article. The proximate
demonstrative *deze* ~ *dit* and the distal demonstrative *die* ~ *dat* agree exactly as the
definite article does. These three agreeing determiners are the agreement evidence for the
two genders of `Dutch.Gender`.

## Main declarations

* `Dutch.Determiners.Target` enumerates the determiners whose singular form agrees in gender,
  and `Dutch.Determiners.singular` gives that form. `Dutch.Determiners.plural` is the
  common-gender form, which every plural takes.
* `Dutch.Determiners.injective_singular` shows that each agreeing determiner distinguishes the
  two genders, and `Dutch.Determiners.faithful` concludes that the two genders are faithful to the
  evidence.
* `Dutch.Determiners.inventory` is the inventory, whose citation forms are the plural forms,
  and `Dutch.Determiners.isSyncretic_inventory` says that its definite article marks both strengths.

## Implementation notes

The uses of *de* are Schwarz's use types. The generic and proper-name uses of the definite
article, on which Schmuck's micro-typology places Dutch between English and
German, are not `Description.Use` cells and so go unrecorded.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume V: Nouns and Noun Phrases 2: Prenominal
  Elements, Pronouns and Syntactic Uses of Noun Phrases* (2026)][broekhuis-corver-2026b]
* [F. Schwarz, *Two Types of Definites in Natural Language* (2009)][schwarz-2009]
* [M. Moroney, *Definiteness and quantification: Evidence from Shan* (2021)][moroney-2021]
* [M. Schmuck, *The Grammaticalisation of Definite Articles in German, Dutch, and English: A
  Micro-Typological Approach* (2020)][schmuck-2020]
-/

@[expose] public section

namespace Dutch.Determiners

/-! ### Gender agreement -/

/-- The determiners whose singular form agrees in gender are the definite article and the
proximate and distal demonstratives. -/
inductive Target where
  | definite
  | proximate
  | distal
  deriving DecidableEq, Repr, Fintype

/-- The singular form of each agreeing determiner is *de*, *deze* or *die* with a common-gender
noun and *het*, *dit* or *dat* with a neuter noun. -/
def singular : Gender.Value → Target → String
  | .common, .definite => "de"
  | .common, .proximate => "deze"
  | .common, .distal => "die"
  | .neuter, .definite => "het"
  | .neuter, .proximate => "dit"
  | .neuter, .distal => "dat"

/-- The plural form of each agreeing determiner is its common-gender singular form. -/
def plural (t : Target) : String := singular .common t

/-- Each agreeing determiner distinguishes the two genders in the singular. -/
theorem injective_singular : ∀ t, Function.Injective (singular · t) := by decide

/-- The two genders are faithful to the determiner evidence. -/
theorem faithful : Gender.Faithful singular :=
  fun _ _ h ↦ injective_singular .definite (congrFun h _)

/-! ### The inventory -/

/-- The definite article *de* ~ *het* is one syncretic definite over the [schwarz-2009] use
types. -/
def de : Article :=
  { form := plural .definite, definiteness := .definite, exponent := .dedicatedMorpheme
    uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- The indefinite article *een* occurs with singular count nouns, since indefinite plural and
mass noun phrases are bare. -/
def een : Article :=
  { form := "een", definiteness := .indefinite, exponent := .dedicatedMorpheme,
    numberRestriction := some .singular }

/-- The negative article *geen* occurs with singular, plural and mass nouns alike, and the
grammar argues that it is a quantifier rather than an article. -/
def geen : QuantificationalDeterminer := { form := "geen", selectsMass := true }

/-- The proximate demonstrative is *deze* ~ *dit*. -/
def deze : DemonstrativeDeterminer :=
  { form := plural .proximate, deixis := Person.first.participantSets }

/-- The distal demonstrative is *die* ~ *dat*. -/
def die : DemonstrativeDeterminer :=
  { form := plural .distal, deixis := Person.first.participantSetsᶜ }

/-- The inventory lists the two articles, *geen* and the two demonstratives. -/
def inventory : Determiner.Inventory :=
  [.article de, .article een, .quantifier geen, .demonstrative deze, .demonstrative die]

/-- A single article marks both strengths. -/
theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end Dutch.Determiners
