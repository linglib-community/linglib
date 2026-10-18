module

public import Linglib.Syntax.Reciprocal

/-!
# Modern Greek reciprocals

Modern Greek marks reciprocity with nonactive verbal morphology, which also expresses reflexives,
passives and middles, and with the periphrastic *o enas ton allon* 'the one the other'. Nonactive
reciprocal verbs form discontinuous reciprocals with *me* 'with', *O Giannis filithike me ti Maria*
'John and Maria kissed each other', Nordlinger's examples 27b and 36, from Dimitriadis (p. 388).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [A. Dimitriadis, *Irreducible Symmetry in Reciprocal Constructions* (2008)][dimitriadis-2008]
-/

@[expose] public section

namespace Greek.StandardModern.Reciprocals

open Reciprocal

def nonactive : Marker :=
  { morphs := [.suff "ome"], strategy := .verbalAffix }

/-- *o enas ton allon* 'the one the other', the periphrastic reciprocal, which does not carry the
    reflexive reading. -/
def oEnasTonAllon : Marker :=
  { morphs := [.free "o", .free "enas", .free "ton", .free "allon"], strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {nonactive, oEnasTonAllon}

end Greek.StandardModern.Reciprocals
