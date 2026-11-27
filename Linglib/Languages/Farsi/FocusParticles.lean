module

public import Linglib.Syntax.Category.Particle.Additive

/-!
# Persian focus particles

The additive particle of Persian is the clitic *-hæm*, *-æm* 'also, too', as in *mæn-æm mi-ya-m*
'I'll come too'. Forms are in Mahootian's transcription.

## Main definitions

* `Farsi.FocusParticles.ham`: the additive particle.

## References

* [mahootian-1997]
-/

@[expose] public section

namespace Farsi.FocusParticles

/-- *-hæm*, also *-æm*, 'also, too', one of the two non-pronominal clitics with the connective
*-o* 'and', [mahootian-1997] p. 271, (543). -/
def ham : AdditiveParticle := { morph := .encl "hæm", gloss := "also, too" }

end Farsi.FocusParticles
