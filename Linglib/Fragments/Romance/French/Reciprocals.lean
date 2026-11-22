module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Fragments.Romance.French.Clitics
public import Linglib.Syntax.Reciprocal

/-!
# French reciprocals

French marks reciprocity with the clitic *se*, shared with the reflexive, and with the bipartite
*l'un l'autre* 'the one the other'. With a direct object *l'un l'autre* cannot mark reciprocity on
its own: *se* stays obligatory, *Jean et Marie s'aiment l'un l'autre* beside
\**Jean et Marie aiment l'un l'autre* ([maslova-2008] (32)), and so the bipartite disambiguates
the *se*-reciprocal rather than replacing it. It is added bare where *se* suppresses an
accusative and after *à* where it suppresses a dative ([siloni-2008] fn. 21). Reciprocal verbs
with *se* are formed in the syntax ([siloni-2008]), so they have no discontinuous counterpart with
*avec* 'with' ([nordlinger-2023] ex. 39).

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [T. Siloni, *The Syntax of Reciprocal Verbs: An Overview* (2008)][siloni-2008]
* [E. Maslova, *Reflexive Encoding of Reciprocity: Cross-Linguistic and Language-Internal
  Variation* (2008)][maslova-2008]
* [maslova-nedjalkov-2013]
-/

@[expose] public section

namespace French.Reciprocals

open Reciprocal

/-- se — reflexive/reciprocal clitic ([nordlinger-2023] ex. 28, 47). -/
def se : Marker :=
  { morphs := [.free "se"], strategy := .recipClitic }

/-- *l'un l'autre*, the bipartite reciprocal; with a direct object it accompanies *se* rather than
    replacing it ([maslova-2008] (32)). -/
def lunLautre : Marker :=
  { morphs := [.free "l'un", .free "l'autre"], strategy := .bipartiteNP }

/-- Marker inventory. -/
def markers : Finset Marker := {se, lunLautre}

/-- The form of the reflexive clitic *se*. -/
def reflexiveForms : Finset (List Morphology.Morph) := {[.free French.Clitics.se.form]}

/-- The value of the inventory on the map of [maslova-nedjalkov-2013] is the one the map gives
the language. -/
theorem lookup_wals :
    Data.WALS.F106A.allData.lookup "fre" = some (type markers reflexiveForms) := by
  decide +kernel

end French.Reciprocals
