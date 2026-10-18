module

public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Reciprocal

/-!
# Russian reciprocals

Russian marks reciprocity with the bipartite *drug druga* 'other other-ACC', the bipartite
quantifier strategy of English *each other* ([nordlinger-2023] ex. 9): it fills the object position,
its second part taking the case the verb assigns while the first stays nominative. The verbal
postfix *-sja* also forms reciprocal verbs (ex. 31) and is shared with the reflexive.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
-/

@[expose] public section

namespace Russian.Reciprocals

open Pronoun Reciprocal

/-- друг друга *drug druga* — bipartite reciprocal 'other other-ACC'
    ([nordlinger-2023] ex. 9). -/
def drugDruga : Marker :=
  { morphs := [.free "drug", .free "druga"], script := some "друг друга"
  , strategy := .bipartiteNP }

/-- -ся *-sja* — verbal postfix, reflexive-identical reciprocal uses
    ([nordlinger-2023] ex. 31). -/
def sja : Marker :=
  { morphs := [.suff "sja"], script := some "-ся", strategy := .verbalAffix
   }

/-- себя *sebja* — the reflexive pronoun (for contrast), one form for every person and
    number. -/
def sebja : ReflexivePronoun := { form := "sebja", script := some "себя" }

/-- Marker inventory. -/
def markers : Finset Marker := {drugDruga, sja}

end Russian.Reciprocals
