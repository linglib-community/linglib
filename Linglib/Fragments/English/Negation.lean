module

public import Linglib.Syntax.Negation

/-!
# English negation

English negates a declarative verbal clause with the particle *not* after the first auxiliary,
*chris is not dancing*, or with a negative form of the auxiliary, *chris isn't dancing*, whose
suffix *-n't* is an inflection rather than a clitic. A clause in a simple tense has no auxiliary,
and its negative is built on *do*, which carries the tense and agreement while the lexical verb
is bare: *chris does not dance*. The same periphrasis serves in the affirmative for emphasis,
*chris does dance*, so a simple tense has two affirmatives, plain and emphatic, and one negative.
Miestamo's examples are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [zwicky-pullum-1983]
-/

@[expose] public section

open Negation

namespace English.Negation

/-- *not*, the standard negator. -/
def not : Marker := { pieces := [[.free "not"]] }

/-- *-n't*, the suffix of the negative forms of the auxiliaries ([zwicky-pullum-1983]). -/
def nt : Marker := { pieces := [[.suff "n't"]] }

/-- The standard negators. -/
def standard : List Marker := [not, nt]

end English.Negation
