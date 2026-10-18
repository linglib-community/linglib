module

public import Linglib.Fragments.English.Pronouns
public import Linglib.Syntax.Reciprocal

/-!
# English reciprocals

English marks reciprocity with the two-part noun phrases *each other* and *one another*, which fill
an argument slot of a bivalent clause and are distinct from the reflexive *themselves*. A closed
class of predicates such as *meet*, *quarrel* and *kiss* is reciprocal without any marker. The
markers are those of the pronoun entries in `Fragments/English/Pronouns.lean`. The lexical strategy
has no exponent: the verbs' Levin classes record it, not the marker inventory.

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
* [T. Siloni, *Reciprocal Verbs and Symmetry* (2012)][siloni-2012]
-/

@[expose] public section

namespace English.Reciprocals

open Reciprocal

/-- The marker of *each other*, from its pronoun entry. -/
def eachOther : Marker := Pronouns.eachOther.toMarker

/-- The marker of *one another*, from its pronoun entry. -/
def oneAnother : Marker := Pronouns.oneAnother.toMarker

/-- The reciprocal marker inventory. -/
def markers : Finset Marker := {eachOther, oneAnother}

end English.Reciprocals
