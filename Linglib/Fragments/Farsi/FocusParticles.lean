module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Persian focus particles

The additive particle *ham* 'also, too', repeated with each of two conjuncts, is the coordinator
`Farsi.Coordination.ham` 'both … and'.

## Main definitions

* `Farsi.FocusParticles.ham`: the additive particle.

## TODO

The entry has not been checked against a grammar of Persian.
-/

@[expose] public section

namespace Farsi.FocusParticles

/-- *ham* 'also, too'. -/
def ham : AdditiveParticle := { morph := .free "ham", gloss := "also, too" }

end Farsi.FocusParticles
