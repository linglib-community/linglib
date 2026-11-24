module

public import Linglib.Syntax.Comparative
public import Linglib.Fragments.HindiUrdu.Adpositions

/-!
# Hindi-Urdu comparison

Hindi-Urdu compares with *X Y se (zyaadaa) Adj hai*. The postposition *se* 'from' marks the
standard, a locational comparative in the atlas, and the free degree word *zyaadaa* 'more' is
optional. The superlative is the comparative with a universal standard, *sab se* 'than all'.

## References

* [stassen-2013]
-/

@[expose] public section

namespace HindiUrdu.Comparison

open Comparative

/-- The *se*-comparative, whose standard takes the postposition *se* in its ablative use. -/
def se : Comparative :=
  { standardMarker := Adpositions.se.morphs
  , standard := .adverbial (some .abl)
  , degreeMarkers := [.free "zyaadaa"] }

theorem case?_standard_functions_inter_nonempty :
    ∀ k ∈ se.standard.case?, (k.functions ∩ Adpositions.se.functions).Nonempty := by
  decide

end HindiUrdu.Comparison
