module

public import Linglib.Syntax.Reciprocal

/-!
# Mandarin reciprocals

Mandarin can express reciprocity by compounding a verb with *lái* 'come' and *qù* 'go' in the
pattern V-*lái*-V-*qù*: *Tāmen dǎ-lái-dǎ-qù* 'They beat each other', [konig-kokutani-2006]'s example
as [nordlinger-2023] cites it. König and Kokutani class it as a compound verbal strategy, and
[nordlinger-2023] notes that [evans-2008]'s typology places it among the multiclausal strategies, as
verb compounding with a repeated one-way predicate. The adverb *hùxiāng* 互相 'mutually' also marks
reciprocity; adverbs are outside the strategy vocabulary of `Reciprocal.Strategy`.

## References

* [nordlinger-2023]
* [konig-kokutani-2006]
* [evans-2008]
-/

@[expose] public section

namespace Mandarin.Reciprocals

open Reciprocal

/-- The V-*lái*-V-*qù* compound, as *dǎ-lái-dǎ-qù* 打来打去 'beat each other': *lái* 'come' and
*qù* 'go' follow the two copies of the verb. -/
def compound : Marker :=
  { morphs := [.suff "lái", .suff "qù"], script := some "打来打去", strategy := .compoundVerb }

/-- The reciprocal markers. -/
def markers : Finset Marker := {compound}

end Mandarin.Reciprocals
