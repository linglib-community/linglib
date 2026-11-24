module

public import Linglib.Syntax.Comparative
public import Linglib.Fragments.Latin.Adjectives

/-!
# Latin comparison

Latin has two productive comparative constructions, *X Adj-ior quam Y* with the particle *quam*
and *X Adj-ior Y* with the standard in the bare ablative; Stassen classes Latin as primarily
particle and secondarily separative. The atlas does not code Latin, and the type of each
construction is derived from its anatomy. The degree is marked by the suffix *-ior* of
`Latin.Adjectives`, and the superlative is morphological.

## References

* [stassen-1985]
-/

@[expose] public section

namespace Latin.Comparison

open Comparative

/-- The *quam*-comparative, the primary construction, with a particle-marked standard. -/
def quam : Comparative :=
  { standardMarker := [.free "quam"], standard := .derived
    degreeMarkers := [Adjectives.ior] }

/-- The comparative with the standard in the bare ablative and no segmental marker. -/
def ablative : Comparative :=
  { standard := .adverbial (some .abl)
    degreeMarkers := [Adjectives.ior] }

/-- The superlative is morphological. -/
def superlative : SuperlativeStrategy := .morphological

end Latin.Comparison
