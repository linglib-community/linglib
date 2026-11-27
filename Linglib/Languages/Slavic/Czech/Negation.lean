module

public import Linglib.Syntax.Negation

/-!
# Czech negation

Czech negates a clause with the prefix *ne-* on the verb, *Petr neplave* 'Peter doesn't swim', as
Short describes it (p. 510). In the past tense and the conditional the prefix goes on the
*l*-participle, in the imperfective future on the auxiliary, *Petr se nebude učit* 'Peter won't
study', and on a modal auxiliary, which it then negates, *Petr se nemusí učit* 'Peter needn't
study'; Short's modal examples are rows of `Data.Examples.Short1993`. Negation is concordant: "any
negative subject or object pronoun or pronoun-adverb is reinforced by ne- in the verb", *Nikdo to
nekoupil* 'No one bought it' (p. 511). The concord items are in the sibling `PolarityItems.lean`.

## References

* [short-1993-czech]
-/

@[expose] public section

open Negation

namespace Czech.Negation

/-- *ne-*, the standard negation prefix. -/
def ne : Marker := { pieces := [[.pref "ne"]] }

end Czech.Negation
