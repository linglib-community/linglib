module

public import Linglib.Syntax.Comparative

/-!
# Mandarin comparison

This file defines the Mandarin comparative of superiority, *tā bǐ nǐ gāo* 'she is taller than
you': the compared item, *bǐ* 'compare with' followed by the standard, and the predicate naming
the dimension. The standard is the object of *bǐ*, a role the construction fixes rather than one
copied from the compared item, so the construction is an exceed comparative
(`Comparative.type`). The comparatives of inferiority, with *méi(yǒu)* or *bùrú*, and of
equality, with *gēn … yíyàng*, have the same shape, and the superlative is the adverb *zuì*
'most' before the predicate.

## References

* [li-thompson-1981]
* [stassen-2013]
-/

@[expose] public section

namespace Mandarin.Comparison

open Comparative

/-- The *bǐ*-comparative, whose standard is the object of *bǐ* 'compare with'. -/
def bi : Comparative :=
  { standardMarker := [.free "bǐ"]
  , caseAssignment := .fixed
  , fixedEncoding := some .directObject }

theorem bi_type : bi.type = .exceed := rfl

end Mandarin.Comparison
