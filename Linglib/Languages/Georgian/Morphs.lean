module

public import Linglib.Morphology.Morph

/-!
# Georgian forms with several uses

The enclitic *-c*, *-ca* after a consonant, is the additive particle 'too, also' and, on each of
several conjuncts, a coordinator. This file gives the form, which the entries for each use share.

## References

* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.Morphs

/-- The enclitic *-c*. -/
def c : Morphology.Morph := .encl "c"

end Georgian.Morphs
