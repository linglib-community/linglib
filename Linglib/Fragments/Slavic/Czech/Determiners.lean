module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# Czech determiner inventory

Czech has neither a definite nor an indefinite article, so its inventory holds only the
demonstrative *ten* and the quantificational determiners, and it marks neither strength of
definiteness (`strengths_inventory`). The quantificational determiners are the carrier
`QuantityWord`, whose words project to `QuantificationalDeterminer` records and denote the
readings the literature makes available for them. Two of them are polarity sensitive, the concord item
*žádný* 'no' and the positive polarity item *nějaký* 'some', and their entries in
`PolarityItems.lean` take their forms from here.

## Implementation notes

* *Žádný* has two readings. On de Swart's analysis of n-words as negative quantifiers, negative
  concord being their resumptive interpretation, it reads as `no`. On Zeijlstra's, which
  Staňková and Šimík adopt for Czech, it is a non-negative indefinite whose negation the
  clause's negative operator contributes, and it reads as `some`.
* WALS codes Czech with a two-way distance contrast, *ten* 'neutral / proximal' against
  *onen* 'contrastive'. Only *ten* is entered, as distance-neutral; the contrastive deixis of
  *onen* has no counterpart among participant sets.

## References

* [diessel-2013b]
* [moroney-2021]
* [de-swart-2010]
* [zeijlstra-2004]
* [stankova-simik-2025]
-/

@[expose] public section

universe u

namespace Czech.Determiners

/-- *ten* 'that, the' is the distance-neutral demonstrative, so it covers every participant
set. -/
def ten : DemonstrativeDeterminer := { form := "ten", deixis := Finset.univ }

/-- The quantificational determiners are *každý* 'every', *žádný* 'no', *nějaký* 'some' and
*některý* 'some, certain'. -/
inductive QuantityWord where
  | kazdy | zadny | nejaky | nektery
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The surface form. -/
def form : QuantityWord → String
  | .kazdy => "každý"
  | .zadny => "žádný"
  | .nejaky => "nějaký"
  | .nektery => "některý"

/-- The grammatical number a word selects, which only *každý* fixes, to the singular. -/
def numberRestriction : QuantityWord → Option Number
  | .kazdy => some .singular
  | _ => none

/-- Whether a word selects mass nouns, which *žádný* and *nějaký* do. -/
def selectsMass : QuantityWord → Bool
  | .zadny | .nejaky => true
  | .kazdy | .nektery => false

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : QuantificationalDeterminer :=
  { form := w.form, numberRestriction := w.numberRestriction, selectsMass := w.selectsMass }

/-- All the words. -/
def toList : List QuantityWord := [.kazdy, .zadny, .nejaky, .nektery]

/-- The readings available for a word. *Každý* reads as `every`, *žádný* as `no` or as
`Quantifier.Det.some`, and *nějaký* and *některý* as `Quantifier.Det.some`, the partitive
specificity of *některý* being no part of its truth conditions. -/
instance : Denotes QuantityWord (Set Quantifier.Det.Family.{u}) where
  denote
    | .kazdy => {Quantifier.Det.Family.every}
    | .zadny => {Quantifier.Det.Family.no, Quantifier.Det.Family.some}
    | .nejaky | .nektery => {Quantifier.Det.Family.some}

end QuantityWord

/-- The Czech determiners are the demonstrative and the quantifiers, with no article. -/
def inventory : Determiner.Inventory :=
  .demonstrative ten :: QuantityWord.toList.map (.quantifier ·.toQuantifier)

theorem strengths_inventory : inventory.strengths = ∅ := by decide

end Czech.Determiners
