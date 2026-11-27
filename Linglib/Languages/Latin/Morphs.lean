module

public import Linglib.Morphology.Morph

/-!
# Latin forms with several uses

The enclitic *-que* is the coordinator 'and' and the particle of *quisque* 'each'. This file
gives the form, which the entries for each use share.

## References

* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Latin.Morphs

/-- The enclitic *-que*. -/
def que : Morphology.Morph := .encl "que"

end Latin.Morphs
