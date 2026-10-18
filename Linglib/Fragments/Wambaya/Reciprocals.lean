module

public import Linglib.Syntax.Reciprocal

/-!
# Wambaya reciprocals

Wambaya marks reflexivity and reciprocity with the clitic *-ngg-* (glossed RR) in the object
position of the second-position auxiliary: *Alag-bulu wurlu-ngg-a nyurrunyurru* 'The two children
are chasing each other', example (5-25) of Nordlinger's grammar. Nordlinger calls it a bound
pronoun, and it looks like a reflexive or reciprocal object pronoun such as Warlpiri *-nyanu*,
but Evans, Gaby and Nordlinger show (§3.2.2) that the clause is intransitive: the subject noun
phrase is nominative rather than ergative, a controlled complement takes the subject-control
form, and *-ngg-* also occurs with semi-transitive verbs, whose indirect objects the auxiliary
never cross-references. It is a valency-reducing marker of the predicate, not an argument.

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
fills no object slot. A tense suffix follows it, presumably replacing the final vowel of an
underlying *-ngga*, the Gudanji form. -/
def rr : Marker :=
  { morphs := [.suff "ngg"], strategy := .recipClitic }

/-- The marker inventory. -/
def markers : Finset Marker := {rr}

end Wambaya.Reciprocals
