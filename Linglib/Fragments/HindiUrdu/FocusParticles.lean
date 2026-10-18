module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Hindi-Urdu focus particles

The additive particle *bhii* 'also, even' follows the phrase it adds; on the indefinite *koii*
'someone' it gives *koii bhii* 'anybody'. Repeated after each of two conjuncts it is the
coordinator `HindiUrdu.Coordination.bhii`.

## Main definitions

* `HindiUrdu.FocusParticles.bhii`: the additive particle.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace HindiUrdu.FocusParticles

/-- *bhii* 'also, even', after the phrase it adds. -/
def bhii : AdditiveParticle := { morph := .free "bhii", gloss := "also, even" }

end HindiUrdu.FocusParticles
