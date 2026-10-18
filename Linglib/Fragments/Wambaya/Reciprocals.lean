module

public import Linglib.Syntax.Reciprocal

/-!
# Wambaya reciprocals

Wambaya marks reflexivity and reciprocity with the clitic *-ngg-* (glossed RR) in the object
position of the second-position auxiliary: *Alag-bulu wurlu-ngg-a nyurrunyurru* 'The two children
are chasing each other', an example of Nordlinger's from her grammar. Though it looks like a
reflexive or reciprocal object pronoun such as Warlpiri *-nyanu*, Evans, Gaby and Nordlinger show
that the clause is intransitive: the subject noun phrase is nominative rather than ergative, a
controlled complement takes the subject-control form, and *-ngg-* also occurs with
semi-transitive verbs, whose objects the auxiliary never cross-references. It is a
valency-reducing marker of the predicate, not an argument.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [R. Nordlinger, *A grammar of Wambaya, Northern Territory (Australia)* (1998)][nordlinger-1998]
* [N. Evans, A. Gaby and R. Nordlinger, *Valency Mismatches and the Coding of Reciprocity in
  Australian Languages* (2007)][evans-et-al-2007]
-/

@[expose] public section

namespace Wambaya.Reciprocals

open Reciprocal

/-- The clitic *-ngg-* is a reciprocal marker, reflexive as well; it marks the predicate and
fills no object slot. Its surface allomorphs vary with the paradigm of the auxiliary. -/
def rr : Marker :=
  { morphs := [.suff "ngg"], strategy := .recipClitic, alsoReflexive := true }

/-- The marker inventory. -/
def markers : Finset Marker := {rr}

end Wambaya.Reciprocals
