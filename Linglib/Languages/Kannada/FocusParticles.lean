module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Kannada focus particles

The enclitic *-uu* is the additive particle 'also' and, on each of two conjuncts, the coordinator
`Kannada.Coordination.uu` 'and'; on the interrogative *yaar* 'who' it gives *yaar-uu* 'anyone'.

## Main definitions

* `Kannada.FocusParticles.uu`: the additive particle.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Kannada.FocusParticles

/-- *-uu* 'also', enclitic on the phrase it adds. -/
def uu : AdditiveParticle := { morph := .encl "uu", gloss := "also" }

end Kannada.FocusParticles
