module

public import Linglib.Syntax.Reciprocal

/-!
# Imbabura Quechua reciprocals

Imbabura Quechua has two verbal suffixes that express the reciprocal meaning. The primary one,
*-ri*, is also reflexive: *wambra-kuna riku-ri-rka* 'the children saw each other' or 'saw
themselves'. The other, *-naju*, has a collective meaning beside the reciprocal one:
*ñukanchi maka-naju-nchi* 'we hit jointly' or 'we hit each other'. The examples are Cole's, rows
of `Data.Examples.MaslovaNedjalkov2013`.

## References

* [maslova-nedjalkov-2013]
-/

@[expose] public section

namespace Quechua.Reciprocals

open Reciprocal

/-- The suffix *-ri*, reciprocal and reflexive. -/
def ri : Marker := { morphs := [.suff "ri"], strategy := .verbalAffix }

/-- The suffix *-naju*, reciprocal and collective. -/
def naju : Marker := { morphs := [.suff "naju"], strategy := .verbalAffix }

/-- The marker inventory. -/
def markers : Finset Marker := {ri, naju}

/-- The form of the reflexive suffix *-ri*. -/
def reflexiveForms : Finset (List Morphology.Morph) := {ri.morphs}

/-- The value of the inventory on the map of [maslova-nedjalkov-2013] is the one the map gives
the language. -/
theorem lookup_wals :
    Data.WALS.F106A.allData.lookup "qim" = some (type markers reflexiveForms) := by
  decide +kernel

end Quechua.Reciprocals
