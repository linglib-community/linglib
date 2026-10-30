module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# German distributive expressions

This file defines the German universal determiners *jeder* 'each, every' and *alle* 'all'.
Durrell describes *jeder* as used only in the singular, as a determiner or a pronoun, and *alle*
as chiefly plural, in the singular with mass nouns and mostly in formal registers. The distance
distributor *jeweils* has no determiner use. Haslinger and colleagues class the items by
obligatory distributivity and exception intolerance in their study.

## References

* [durrell-2011]
* [haslinger-etal-2025]
-/

@[expose] public section

namespace German.Distributives

/-- *Jeder* 'each, every' is a determiner of singular nouns. -/
def jeder : QuantificationalDeterminer := { form := "jeder", numberRestriction := some .singular }

/-- *Alle* 'all' is a determiner chiefly of plural nouns, and in the singular of mass nouns. -/
def alle : QuantificationalDeterminer := { form := "alle", selectsMass := true }

end German.Distributives
