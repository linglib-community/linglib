module

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
-/

@[expose] public section

namespace Spanish.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { morphs := [.free "se"], strategy := .recipClitic
  , readings := {.reciprocal, .reflexive} }

/-- el uno al otro — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { morphs := [.free "el", .free "uno", .free "al", .free "otro"], strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {seClitic, bipartite}

end Spanish.Reciprocals
