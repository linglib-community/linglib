module

public import Linglib.Syntax.Comparative

/-!
# Finnish comparison

Finnish compares with *X on Adj-mpi kuin Y*. The particle *kuin* marks the standard, a particle
comparative in the atlas, and a secondary construction puts the standard in the partitive
instead; Stassen classes Finnish as primarily particle and secondarily separative. The degree is
marked by the suffix *-mpi*, and the superlative is morphological.

## References

* [stassen-1985]
* [stassen-2013]
-/

@[expose] public section

namespace Finnish.Comparison

open Comparative

/-- The suffix of the comparative. -/
def mpi : Morphology.Morph := .suff "mpi"

/-- The *kuin*-comparative, the primary construction, with a particle-marked standard. -/
def kuin : Comparative :=
  { standardMarker := [.free "kuin"], standard := .derived, degreeMarkers := [mpi] }

/-- The secondary construction, with the standard in the partitive. -/
def partitive : Comparative :=
  { standard := .adverbial (some .part)
    degreeMarkers := [mpi] }

end Finnish.Comparison
