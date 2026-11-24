module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# English focus particles

English has the additive particles *too*, which follows the phrase it adds, *Mary is well too*,
and *also*, which precedes it. Neither is the coordinator *and*, as Mitrović and Sauerland point
out, while in Haspelmath's account an additive particle of either kind is one source of a
coordinator.

## Main definitions

* `English.FocusParticles.too`, `English.FocusParticles.also`: the additive particles.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace English.FocusParticles

/-- *too* 'also', after the phrase it adds. -/
def too : AdditiveParticle := { morph := .free "too", gloss := "too" }

/-- *also*, before the phrase it adds. -/
def also : AdditiveParticle := { morph := .free "also", gloss := "also" }

end English.FocusParticles
