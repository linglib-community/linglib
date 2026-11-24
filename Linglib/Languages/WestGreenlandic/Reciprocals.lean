module

public import Linglib.Syntax.Reciprocal

/-!
# West Greenlandic reciprocals

West Greenlandic expresses the reciprocal and the reflexive meaning with one pronoun, the stem
*immi-* with a person suffix and a case: *immi-ssin-nut tuqun-niar-pusi* 'you are going to kill
each other' or 'yourselves'. The construction is available for transitive verbs only and relates
the two core participants. The example is Fortescue's, a row of
`Data.Examples.MaslovaNedjalkov2013`.

## References

* [maslova-nedjalkov-2013]
-/

@[expose] public section

namespace WestGreenlandic.Reciprocals

open Reciprocal

/-- The pronoun stem *immi-*, reciprocal and reflexive. -/
def immi : Marker := { morphs := [.root "immi"], strategy := .recipPronoun }

/-- The marker inventory. -/
def markers : Finset Marker := {immi}

/-- The form of the reflexive pronoun, the same stem. -/
def reflexiveForms : Finset (List Morphology.Morph) := {immi.morphs}

/-- The value of the inventory on the map of [maslova-nedjalkov-2013] is the one the map gives
the language. -/
theorem lookup_wals :
    Data.WALS.F106A.allData.lookup "grw" = some (type markers reflexiveForms) := by
  decide +kernel

end WestGreenlandic.Reciprocals
