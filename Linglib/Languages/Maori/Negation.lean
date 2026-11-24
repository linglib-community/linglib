module

public import Linglib.Syntax.Negation

/-!
# Maori negation

Maori negates a clause with the negative verb *kāore*, which stands first and takes the negated
clause as its complement; the subject usually follows *kāore* directly, ahead of the tense
particle and the verb: *e haere ana ia* 'he is going', *kāore ia e haere ana* 'he is not going'.
The perfect particle *kua* of the affirmative is *kia* under *kāore*, as in complement clauses
generally. Miestamo's examples, from Harlow's grammar, are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [harlow-1996]
-/

@[expose] public section

open Negation

namespace Maori.Negation

/-- The negative verb *kāore*. -/
def kaore : Marker := { pieces := [[.free "kāore"]] }

/-- The standard negators. -/
def standard : List Marker := [kaore]

end Maori.Negation
