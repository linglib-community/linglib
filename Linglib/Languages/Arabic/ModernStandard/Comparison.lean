module

public import Linglib.Syntax.Comparative

/-!
# Modern Standard Arabic comparison

Modern Standard Arabic compares with *X ʔafʕal min Y*. The preposition *min* 'from' marks the
standard, a locational comparative in the atlas, and the elative pattern *ʔafʕal* of the
adjective carries the comparison, with no separate degree word. The superlative is the elative
without a standard of comparison.

## References

* [stassen-2013]
-/

@[expose] public section

namespace Arabic.ModernStandard.Comparison

open Comparative

/-- The *min*-comparative, whose standard follows the separative preposition *min*. -/
def min : Comparative :=
  { standardMarker := [.free "min"]
  , standard := .adverbial (some .abl) }

end Arabic.ModernStandard.Comparison
