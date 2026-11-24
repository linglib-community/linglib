module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Hungarian focus particles

The additive particle *is* 'also, too' follows the phrase it adds, *Ezt én is tudom* 'I know this,
too'. After each of two conjuncts it is the coordinator `Hungarian.Coordination.is_` 'and'.

## Main definitions

* `Hungarian.FocusParticles.is_`: the additive particle.

## References

* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Hungarian.FocusParticles

/-- *is* 'also, too', after the phrase it adds. -/
def is_ : AdditiveParticle := { morph := .free "is", gloss := "also, too" }

end Hungarian.FocusParticles
