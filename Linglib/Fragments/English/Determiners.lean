module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# English determiners

The quantificational determiners of English are the carrier `QuantityWord`. A word projects to a
`Quantifier` record by `QuantityWord.toQuantifier`, which carries only what the readings leave
open, the number the word selects and whether it selects mass nouns. The readings themselves are
the `Denotes` instance, a set of `Quantifier.GQ.Family` per word: a word with one consensus
reading denotes a singleton, so `⟦QuantityWord.all⟧` is `{every}`, and *many*, whose standard
Barwise and Cooper leave to context, denotes `∅`. Everything a reading fixes, its force,
monotonicity, strength and conservativity, is a theorem about it, as in
`Studies/BarwiseCooper1981.lean`. The articles, demonstratives and possessives are the other
determiner kinds.

## Main declarations

* `QuantityWord`: the quantificational determiners, with the six-word scale
  `QuantityWord.scale` of van Tiel, Franke and Sauerland inside it.
* `QuantityWord.toQuantifier`: a word as a determiner record.
* `inventory`: the English determiner inventory, whose *the* marks both strengths
  (`isSyncretic_inventory`).

## References

* [barwise-cooper-1981]
* [horn-1972]
* [van-tiel-franke-sauerland-2021]
* [von-fintel-1993]
* [harbour-2014]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [schwarz-2009]
* [moroney-2021]
-/

@[expose] public section

namespace English.Determiners

/-! ## Quantificational determiners -/

/-- The quantificational determiners of English are the six-word quantity scale *none*, *few*,
*some*, *half*, *most* and *all*, and *every*, *each*, *many*, *both* and *neither*. -/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all | every | each | many | both | neither
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The form of a word is its spelling. -/
def form : QuantityWord → String
  | .none_ => "none"
  | .few => "few"
  | .some_ => "some"
  | .half => "half"
  | .most => "most"
  | .all => "all"
  | .every => "every"
  | .each => "each"
  | .many => "many"
  | .both => "both"
  | .neither => "neither"

/-- The grammatical number a word selects is left open by the denotation, so *every* and *all*
share a denotation and differ here. *Both* and *neither* select the dual, the core concept
`[−atomic, +minimal]` of [harbour-2014], whose cardinality clause the denotation reflects
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]). -/
def numberRestriction : QuantityWord → Option Number
  | .few | .most | .all | .many => some .plural
  | .every | .each => some .singular
  | .both | .neither => some .dual
  | .none_ | .some_ | .half => none

/-- `selectsMass w` says whether `w` combines with mass nouns, which the denotation likewise
leaves open. -/
def selectsMass : QuantityWord → Bool
  | .none_ | .some_ | .half | .most | .all => true
  | .few | .every | .each | .many | .both | .neither => false

/-- The determiner record of a word carries its form, its number and its mass selection. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form, numberRestriction := w.numberRestriction, selectsMass := w.selectsMass }

/-- The six-word quantity scale of [van-tiel-franke-sauerland-2021] runs from *none* to *all*;
quantifier theories such as those of [barwise-cooper-1981] and [von-fintel-1993] are compared on
it. -/
def scale : List QuantityWord := [.none_, .few, .some_, .half, .most, .all]

/-- `toList` lists every word. -/
def toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all, .every, .each, .many, .both, .neither]

theorem mem_toList (w : QuantityWord) : w ∈ toList := by cases w <;> decide

/-! ### The available readings -/

universe u

/-- A word denotes the readings the literature makes available for it, as generalized
quantifiers on every finite domain. *None* reads as `no`, *some* as `Quantifier.GQ.some`, *all*,
*every* and *each* as `every`, *most* as `most`, *few* as `few`, *half* as `half`, *both* as
`both` and *neither* as `neither`; *many* has no reading, since [barwise-cooper-1981] leave its
standard to context. -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .none_ => {Quantifier.GQ.Family.no}
    | .some_ => {Quantifier.GQ.Family.some}
    | .all | .every | .each => {Quantifier.GQ.Family.every}
    | .most => {Quantifier.GQ.Family.most}
    | .few => {Quantifier.GQ.Family.few}
    | .half => {Quantifier.GQ.Family.half}
    | .both => {Quantifier.GQ.Family.both}
    | .neither => {Quantifier.GQ.Family.neither}
    | .many => ∅

end QuantityWord

/-! ## Articles, demonstratives and possessives

The articles and demonstratives are not quantifiers, since what they denote is definiteness and
not a generalized quantifier. -/

/-- *The* is the definite article, syncretic over both strengths of [schwarz-2009]. -/
def the : Article :=
  { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme
  , uses := {.immediateSituation, .largerSituation, .anaphoric} }

/-- *A* is the singular indefinite article. -/
def a : Article :=
  { form := "a", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- *An* is the singular indefinite article, the allomorph of *a* before a vowel. -/
def an : Article :=
  { form := "an", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- *This* is the singular proximal demonstrative. -/
def this : DemonstrativeDeterminer := { form := "this", deixis := Person.first.participantSets }

/-- *That* is the singular distal demonstrative. -/
def that : DemonstrativeDeterminer := { form := "that", deixis := Person.first.participantSetsᶜ }

/-- *These* is the plural proximal demonstrative. -/
def these : DemonstrativeDeterminer := { form := "these", deixis := Person.first.participantSets }

/-- *Those* is the plural distal demonstrative. -/
def those : DemonstrativeDeterminer := { form := "those", deixis := Person.first.participantSetsᶜ }

/-- *My* is the first-person possessive determiner. -/
def my : PossessiveDeterminer := { form := "my" }

/-- *Your* is the second-person possessive determiner. -/
def your : PossessiveDeterminer := { form := "your" }

/-! ## The inventory -/

/-- The quantificational determiners as records. -/
def allQuantifiers : List Quantifier := QuantityWord.toList.map QuantityWord.toQuantifier

/-- The articles. -/
def allArticles : List Article := [the, a, an]

/-- The demonstratives. -/
def allDemonstratives : List DemonstrativeDeterminer := [this, that, these, those]

/-- The possessive determiners. -/
def allPossessives : List PossessiveDeterminer := [my, your]

/-- The determiner inventory collects every kind of determiner. -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ allDemonstratives.map .demonstrative ++
    allQuantifiers.map .quantifier ++ allPossessives.map .possessive

theorem isSyncretic_inventory : inventory.IsSyncretic := by decide

end English.Determiners
