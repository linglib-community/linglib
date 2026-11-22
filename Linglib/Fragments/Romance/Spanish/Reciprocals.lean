module

public import Linglib.Fragments.Romance.Spanish.Clitics
public import Linglib.Syntax.Reciprocal

/-!
# Spanish reciprocals

Spanish marks reciprocity with the clitic *se*, shared with the reflexive, and with the periphrastic
*el uno al otro*, beside a class of lexical reciprocal verbs whose reciprocal reading also emerges
without *se* in language-specific environments, the matter of Palmieri's second chapter, whose
list of the verbs is `Studies/Palmieri2024.lean`.

## References

* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
* [maslova-nedjalkov-2013]
-/

@[expose] public section

namespace Spanish.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { morphs := [.free "se"], strategy := .recipClitic }

/-- el uno al otro — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { morphs := [.free "el", .free "uno", .free "al", .free "otro"], strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {seClitic, bipartite}

/-- The forms of the reflexive clitics. -/
def reflexiveForms : Finset (List Morphology.Morph) :=
  Spanish.Clitics.reflexive.image fun r ↦ [.free r.form]

/-- The value of the inventory on the map of [maslova-nedjalkov-2013] is the one the map gives
the language. -/
theorem lookup_wals :
    Data.WALS.F106A.allData.lookup "spa" = some (type markers reflexiveForms) := by
  decide +kernel

end Spanish.Reciprocals
