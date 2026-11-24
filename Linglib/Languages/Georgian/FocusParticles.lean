module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Georgian focus particles

The additive particle is the clitic *-c* 'too, also', *-ca* after a consonant, *mankana-c
ga-v-(Ø-)t'ex-e* 'I smashed the car too'. On each of several conjuncts it gives 'both … and', and it
is then the coordinator `Georgian.Coordination.c`.

## Main definitions

* `Georgian.FocusParticles.c`: the additive particle.

## References

* [hewitt-1995]
-/

@[expose] public section

namespace Georgian.FocusParticles

/-- *-c* 'too, also', *-ca* after a consonant, enclitic on the phrase it adds. -/
def c : AdditiveParticle := { morph := .encl "c", gloss := "too, also" }

end Georgian.FocusParticles
