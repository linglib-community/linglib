module

public import Linglib.Syntax.Comparative

/-!
# Russian comparison

Russian compares with *X Adj-ee, chem Y*. The particle *chem* marks the standard, a particle
comparative in the atlas, and a bare genitive standard, *X Adj-ee Y*, is also available and is
not entered. The degree is marked by the suffix *-ee* or its variant *-ej*.

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

end Russian.Comparison
