module

public import Linglib.Semantics.Quantification.Determiner

/-!
# Czech determiner inventory

Czech has neither a definite nor an indefinite article, so its inventory holds only the
demonstrative *ten* and the quantificational determiners, and it marks neither strength of
definiteness (`strengths_inventory`). The quantificational determiners are
`QuantificationalDeterminer` records with the readings the literature makes available for them.
Two of them are polarity sensitive, the concord item
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


namespace Czech.Determiners

/-- *ten* 'that, the' is the distance-neutral demonstrative, so it covers every participant
set. -/
def ten : DemonstrativeDeterminer := { form := "ten", deixis := Finset.univ }

/-- *Každý* 'every', read as `every`, with a singular noun. -/
def kazdy : QuantificationalDeterminer :=
  { form := "každý", readings := {.every}, numberRestriction := some .singular }

/-- *Žádný* 'no', read as `no` or as `Quantifier.Det.some`, with a count or a mass noun. -/
def zadny : QuantificationalDeterminer :=
  { form := "žádný", readings := {.no, .some}, selectsMass := true }

/-- *Nějaký* 'some', read as `Quantifier.Det.some`, with a count or a mass noun. -/
def nejaky : QuantificationalDeterminer :=
  { form := "nějaký", readings := {.some}, selectsMass := true }

/-- *Některý* 'some, certain', read as `Quantifier.Det.some`, the partitive specificity of
*některý* being no part of its truth conditions. -/
def nektery : QuantificationalDeterminer :=
  { form := "některý", readings := {.some} }

/-- The quantificational determiners. -/
def allQuantifiers : List QuantificationalDeterminer := [kazdy, zadny, nejaky, nektery]

/-- The Czech determiners are the demonstrative and the quantifiers, with no article. -/
def inventory : Determiner.Inventory :=
  .demonstrative ten :: allQuantifiers.map .quantifier

theorem strengths_inventory : inventory.strengths = ∅ := by decide

end Czech.Determiners
