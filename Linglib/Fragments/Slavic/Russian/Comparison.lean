module

public import Linglib.Syntax.Comparative

/-!
# Russian comparison

Russian compares with *X Adj-ee, chem Y*. The particle *chem* marks the standard, a particle
comparative in the atlas, and a bare genitive standard, *X Adj-ee Y*, is also available and is
not entered. The degree is marked by the suffix *-ee* or its variant *-ej*.

## TODO

`superlative` is entered as morphological, while `Russian/Adjectives.lean` records the
periphrastic superlative with *samyj*, beside which a morphological one is literary;
`SuperlativeStrategy` has no case for a superlative formed with a degree word.

## References

* [stassen-2013]
-/

@[expose] public section

namespace Russian.Comparison

open Comparative

/-- The *chem*-comparative, with a particle-marked standard. -/
def chem : Comparative :=
  { standardMarker := [.free "chem"], standard := .derived
    degreeMarkers := [.suff "ee", .suff "ej"] }

/-- The superlative is morphological. -/
def superlative : SuperlativeStrategy := .morphological

end Russian.Comparison
