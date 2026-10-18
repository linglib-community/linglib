module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Korean focus particles

The delimiter *-do* 'also', Sohn's *to*, is the additive particle of Korean, and after each of two
conjuncts the coordinator `Korean.Coordination.do_`.

## Main definitions

* `Korean.FocusParticles.do_`: the additive particle.

## References

* [sohn-1999]
-/

@[expose] public section

namespace Korean.FocusParticles

/-- *-do* 'also', Sohn's *to*, enclitic on the phrase it adds. -/
def do_ : AdditiveParticle := { morph := .encl "do", gloss := "also" }

end Korean.FocusParticles
