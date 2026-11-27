module

public import Linglib.Morphology.Morph

/-!
# Japanese forms with several uses

The enclitic *mo* is a coordinator 'and' on each conjunct, the additive particle 'also, too', and
the particle of the universal indeterminate quantifiers, *dare-mo* 'everyone'. The enclitic *ka*
is the coordinator 'or' and the particle of the existential indeterminate quantifiers, *dare-ka*
'someone'. This file gives the two forms, which the entries for each use share.

## References

* [haspelmath-1997]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Japanese.Morphs

/-- The enclitic *mo*. -/
def mo : Morphology.Morph := .encl "mo"

/-- The enclitic *ka*. -/
def ka : Morphology.Morph := .encl "ka"

end Japanese.Morphs
