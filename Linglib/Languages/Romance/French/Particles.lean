module

public import Linglib.Morphology.Morph

/-!
# French polarity particles

The polarity particles *oui*, *non* and *si* (`French.PolarityParticles`). *Si*, glossed
yes.REV, is the polarity-reversing affirmative: after a negative question it replaces *oui*,
which cannot confirm the positive alternative, *Tu n'es pas fatigué? — \*Oui / Si*, as Holmberg
notes, and it reverses a negative assertion, *Il ne fait pas beau. — Si (il fait beau)*. Unlike
the Italian *sì che* and Spanish *sí que* constructions, *si* is limited to answering a
preceding opposite turn, as Garassino and Jacob observe. What each particle marks is a matter of
analysis: a valued polarity feature for Holmberg, features of the response for Farkas and Bruce.

## References

* [holmberg-2016]
* [farkas-bruce-2010]
* [garassino-jacob-2018]
-/

@[expose] public section

namespace French.PolarityParticles

/-- *oui* 'yes': *Tu es fatigué?* 'Are you tired?' — *Oui*. -/
def oui : Morphology.Morph := .free "oui"

/-- *non* 'no'. -/
def non : Morphology.Morph := .free "non"

/-- *si* 'yes.REV', contradicting a negative: *Tu n'es pas fatigué?* 'Are you not tired?' —
*Si*, I am. -/
def si : Morphology.Morph := .free "si"

/-- The polarity particles. -/
def all : List Morphology.Morph := [oui, non, si]

end French.PolarityParticles
