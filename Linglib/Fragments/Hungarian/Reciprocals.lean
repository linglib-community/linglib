module

public import Linglib.Syntax.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Hungarian reciprocals

Hungarian expresses reciprocity with the pronoun *egymás* 'each other', the compound of the
numeral *egy* 'one' and the distributor *más* 'other', which fills the object position and
keeps the verb transitive, *a gyerekek látták egymást* 'the children saw each other'. It is
invariable, the same form for an antecedent of any person and number, whereas the reflexive
inflects (`Hungarian.Pronouns.reflexives`). The antecedents *egymás* tolerates are the matter of
`Studies/Rakosi2020.lean`.

A reciprocal verb such as *csókolózik* 'kiss' is intransitive, *János és Mari csókolóztak* 'János
and Mari kissed'. Its suffix *-óz-* is one of the derivational suffixes of argument reduction,
which also form reflexive verbs such as *mosakodik* 'wash oneself' and plain intransitives such
as *érkezik* 'arrive', so the suffix does not by itself mark a verb as reciprocal.

## Main definitions

* `Hungarian.Reciprocals.egymas`, `Hungarian.Reciprocals.ozSuffix`,
  `Hungarian.Reciprocals.markers`: the reciprocal pronoun, the verbal suffix and the marker
  inventory.

## References

* [rakosi-2020]
* [rakosi-2008]
* [rounds-2001]
* [nordlinger-2023]
* [siloni-2008]
-/

@[expose] public section

namespace Hungarian.Reciprocals

open Reciprocal

/-- The reciprocal pronoun *egymás* 'each other', invariable in person and number. -/
def egymas : ReciprocalPronoun := { form := "egymás" }

/-- The verbal suffix *-óz-* of the reciprocal verb *csókolózik* 'kiss'. -/
def ozSuffix : Marker := { morphs := [.suff "óz"], strategy := .verbalAffix }

/-- The reciprocal markers. -/
def markers : Finset Marker := {ozSuffix, egymas.toMarker}

end Hungarian.Reciprocals
