module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Tanti Dargwa focus particles

The additive particle is the enclitic *=ra* 'also, too', which repeated after each conjunct is the
coordinator `Dargwa.Coordination.ra` 'and', as Sumbatova describes it.

## Main definitions

* `Dargwa.FocusParticles.ra`: the additive particle.

## References

* [sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.FocusParticles

/-- *=ra* 'also, too', enclitic on the phrase it adds. -/
def ra : AdditiveParticle := { morph := .encl "ra", gloss := "also, too" }

end Dargwa.FocusParticles
