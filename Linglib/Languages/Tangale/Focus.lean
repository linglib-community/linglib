module

public import Linglib.Morphology.Morph

/-!
# Tangale focus morphology

Tangale (West Chadic) marks a focused intransitive predicate with the verbal suffix *-i*,
which Hartmann and Zimmermann show on the verb, or the whole verb phrase, of an answer to a
predicate question; the suffix is homophonous with the pronominal suffix of a nominalized verb
and does not occur with every verb.

## References

* [hartmann-zimmermann-2004]
-/

@[expose] public section

namespace Tangale

/-- The suffix *-i* of a focused intransitive predicate. -/
def focusSuffix : Morphology.Morph := .suff "i"

end Tangale
