module

public import Linglib.Morphology.Morph

/-!
# Hungarian forms with several uses

The word *is* is the additive particle 'also, too' and, after each of two conjuncts, a
coordinator. This file gives the form, which the entries for each use share.

## References

* [szabolcsi-2015]
-/

@[expose] public section

namespace Hungarian.Morphs

/-- The word *is*. -/
def is_ : Morphology.Morph := .free "is"

end Hungarian.Morphs
