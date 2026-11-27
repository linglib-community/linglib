module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Japanese focus particles

The additive particle *mo* 'also, too' is an enclitic on the phrase it adds, *Mary-mo wakaru*
'Mary understands too'. On each of two conjuncts it is the coordinator `Japanese.Coordination.mo`
'and', and on an indeterminate pronoun the particle of the indeterminate quantifiers,
*nani-mo* 'nothing'.

## Main definitions

* `Japanese.FocusParticles.mo`: the additive particle.

## References

* [haspelmath-1997]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Japanese.FocusParticles

/-- *mo* 'also, too', enclitic on the phrase it adds. -/
def mo : AdditiveParticle := { morph := .encl "mo", gloss := "also, too" }

end Japanese.FocusParticles
