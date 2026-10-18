module

public import Linglib.Syntax.Reciprocal

/-!
# Catalan reciprocals

Catalan encodes reciprocity with the clitic *es*, identical to the reflexive, and the
periphrastic *l'un a l'altre*, alongside a class of lexical reciprocal verbs, verbs with a
transitive entry whose reciprocal reading also emerges without *es* in language-specific
environments. These are the matter of Palmieri's second chapter, whose list of the verbs is
`Studies/Palmieri2024.lean`.

## References

* [palmieri-2024]
-/

@[expose] public section

namespace Catalan.Reciprocals

open Reciprocal

/-- es — reflexive/reciprocal clitic ([palmieri-2024] ch. 2). -/
def seClitic : Marker :=
  { morphs := [.free "es"], strategy := .recipClitic
  , readings := {.reciprocal, .reflexive} }

/-- l'un a l'altre — periphrastic bipartite reciprocal (consensus periphrastic). -/
def bipartite : Marker :=
  { morphs := [.free "l'un", .free "a", .free "l'altre"], strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {seClitic, bipartite}

end Catalan.Reciprocals
