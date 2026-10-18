module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Turkish focus particles

The clitic *de*, *da* by vowel harmony, is the additive particle 'too' and the coordinator
`Turkish.Coordination.de` 'and'.

## Main definitions

* `Turkish.FocusParticles.de`: the additive particle.

## References

* [goksel-kerslake-2005]
-/

@[expose] public section

namespace Turkish.FocusParticles

/-- *de*, *da* by vowel harmony, 'too', enclitic. -/
def de : AdditiveParticle := { morph := .encl "de", gloss := "too, also" }

end Turkish.FocusParticles
