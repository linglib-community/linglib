module

public import Linglib.Fragments.German.Pronouns

/-!
# German reciprocals

German marks reciprocity with the reciprocal pronoun *einander* and with *sich*, the form of the
third person reflexive. [gast-haas-2008] split *sich* into two lexical entries of one shape:
pronominal *sich*, a noun phrase that is only reflexive, and clitic *sich*, a middle marker that
is also reciprocal. Only clitic *sich* is reciprocal, so *sich* has no reciprocal reading where
only a noun phrase can stand, after a preposition, in the forefield, coordinated or stressed;
after a preposition *einander* is the only reciprocal (*an-einander*). On [siloni-2012]'s analysis
(footnotes 13 and 38), clitic *sich* marks a syntactically formed reciprocal verb, as Romance *se*
does: embedded under *sagen* 'say', a *sich* reciprocal lacks the "I" reading that *einander*
allows.

## References

* [V. Gast and F. Haas, *On Reciprocal and Reflexive Uses of Anaphors in German and Other European
  Languages* (2008)][gast-haas-2008]
* [T. Siloni, *Reciprocal Verbs and Symmetry* (2012)][siloni-2012]
-/

@[expose] public section

namespace German.Reciprocals

open Reciprocal

/-- The marker of the reciprocal pronoun *einander*. -/
def einander : Marker := Pronouns.einander.toMarker

/-- *sich* in its reciprocal use is the clitic *sich* of [gast-haas-2008], which marks the
predicate rather than filling the object slot and also has the reflexive reading. -/
def sich : Marker :=
  { morphs := [.free Pronouns.sich.form], strategy := .recipClitic }

/-- The reciprocal marker inventory. -/
def markers : Finset Marker := {einander, sich}

end German.Reciprocals
