module

public import Linglib.Syntax.Negation

/-!
# Zarma-Sonrai negation

Zarma-Sonrai is a Songhay language spoken mainly in southwestern Niger. Its standard negators are
chosen by aspect, *si* in the imperfective and *mana* in the perfective, and possession is negated
by *sinda* 'not have'. All three occur expletively, contributing no negation: *a batu a mana
graduate manang* 'he delayed graduating last year', *ey si batu a ma si ka* 'I cannot wait for him
to come'. The description follows Jin and Koenig, whose examples are the rows of
`Data.Examples.JinKoenig2021`.

## References

* [jin-koenig-2021]
-/

@[expose] public section

open Negation

namespace ZarmaSonrai.Negation

/-- *si*, the imperfective negator. -/
def si : Marker := { pieces := [[.free "si"]] }

/-- *mana*, the perfective negator. -/
def mana : Marker := { pieces := [[.free "mana"]] }

/-- *sinda* 'not have', the negative possessive verb. -/
def sinda : Marker := { pieces := [[.free "sinda"]] }

/-- The standard negators. -/
def standard : List Marker := [si, mana]

end ZarmaSonrai.Negation
