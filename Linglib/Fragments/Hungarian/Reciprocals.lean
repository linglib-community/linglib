module

public import Linglib.Syntax.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Hungarian reciprocals

Hungarian expresses reciprocity with the pronoun *egymás* 'each other', the compound of the
numeral *egy* 'one' and the distributor *más* 'other', which fills the object position and
keeps the verb transitive, *a gyerekek látták egymást* 'the children saw each other', and with
the verbal suffix *-óz-*, which yields a monovalent verb, *János és Mari csókolóztak* 'János and
Mari kissed'. As Rákosi notes, *egymás* is invariable, showing no person or number
inflection, whereas the reflexive has the full paradigm of `Hungarian.Pronouns.reflexives`. The
antecedents *egymás* tolerates are the matter of `Studies/Rakosi2019.lean`.

## Main definitions

* `Hungarian.Reciprocals.egymas`, `Hungarian.Reciprocals.ozSuffix`,
  `Hungarian.Reciprocals.markers`: the reciprocal pronoun, the verbal suffix and the marker
  inventory.

## References

* [rakosi-2019]
* [nordlinger-2023]
* [siloni-2008]
-/

@[expose] public section

namespace Hungarian.Reciprocals

open Reciprocal

/-- The reciprocal pronoun *egymás* 'each other', invariable. -/
def egymas : ReciprocalPronoun := { form := "egymás", person := some .third, number := none }

/-- The reciprocal verbal suffix *-óz-*. -/
def ozSuffix : Marker := { morphs := [.suff "óz"], strategy := .verbalAffix }

/-- The reciprocal markers. -/
def markers : Finset Marker := {ozSuffix, egymas.toMarker}

end Hungarian.Reciprocals
