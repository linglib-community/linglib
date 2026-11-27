module

public import Linglib.Syntax.Negation

/-!
# Hixkaryana negation

Hixkaryana, a Cariban language of Brazil, negates a verb with the suffix *-hɨra*, also *-hra*,
which deverbalizes it. The negated verb is the complement of the copula, and the
copula carries the person, tense, aspect, number and mood marking that the verb carries in the
affirmative: *kɨ-amryekɨ-no* 'I went hunting', *amryekɨ-hɨra w-ah-ko* 'I did not go hunting'.
Miestamo's examples, from Derbyshire's grammar, are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [derbyshire-1979]
-/

@[expose] public section

open Negation

namespace Hixkaryana.Negation

/-- The deverbalizing negative suffix *-hɨra*. -/
def hira : Marker := { pieces := [[.suff "hɨra"]] }

/-- The standard negators. -/
def standard : List Marker := [hira]

end Hixkaryana.Negation
