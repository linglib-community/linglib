module

public import Linglib.Syntax.Negation

/-!
# Januubi Arabic negation

Januubi is a dialect of Gulf Arabic spoken in the province of Asir in southwestern Saudi Arabia. Its
standard negator is the preverbal particle *maa*, and prohibitions use *laa*. Both occur
expletively, contributing no negation: *maa* under *gabl* 'before' and *b-il-guwah* 'barely', and
*laa* under verbs of fearing. The description follows Jin and Koenig, whose examples are the rows of
`Data.Examples.JinKoenig2021`.

## References

* [jin-koenig-2021]
-/

@[expose] public section

open Negation

namespace Januubi.Negation

/-- *maa*, the standard negator. -/
def maa : Marker := { pieces := [[.free "maa"]] }

/-- *laa*, the prohibitive negator. -/
def laa : Marker := { pieces := [[.free "laa"]] }

/-- The standard negators. -/
def standard : List Marker := [maa]

end Januubi.Negation
