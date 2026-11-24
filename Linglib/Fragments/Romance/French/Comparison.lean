module

public import Linglib.Syntax.Comparative

/-!
# French comparison

French compares with *X est plus Adj que Y*. The particle *que* marks the standard, a particle
comparative in the atlas, and the free word *plus* marks the degree. The superlative is the
definite article with the comparative, *le plus grand*.

## References

* [stassen-2013]
-/

@[expose] public section

namespace French.Comparison

open Comparative

/-- The *que*-comparative, with a particle-marked standard and the degree word *plus*. -/
def que : Comparative :=
  { standardMarker := [.free "que"], standard := .derived
    degreeMarkers := [.free "plus"] }

/-- The superlative is the definite article with the comparative. -/
def superlative : SuperlativeStrategy := .definiteComparative

end French.Comparison
