module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Marathi utterance-final particles

The utterance-final discourse particles of Marathi as `Particle` values with their clause-type
distribution. *Bərə* occurs with declaratives, imperatives and wh-interrogatives and never with
polar interrogatives (Deo's study of *bərə*, §1); its commitment semantics is the subject of
`Studies/Deo2025.lean`. *Na* signals a preference for independent shared commitment, as Deo
argues in earlier work; only its imperative use is recorded here, from footnotes 5 and 6 of the
*bərə* study.

## References

* [deo-2025-bara]
* [deo-2023]
-/

@[expose] public section

namespace Marathi.Particles

/-- *bərə*, the utterance-final particle of declaratives, imperatives and wh-interrogatives,
never of polar interrogatives ([deo-2025-bara] §1). -/
def bara : Particle where
  form := "bərə"
  position := some .clauseFinal
  distribution
    | .declarative, .matrix => some .optional
    | .polar, .matrix => some .excluded
    | .constituent, .matrix => some .optional
    | .imperative, .matrix => some .optional
    | _, _ => none

/-- *na*, the utterance-final particle that augments an imperative while leaving the addressee
the choice ([deo-2025-bara] fn. 5); its other uses are not recorded. -/
def na : Particle where
  form := "na"
  position := some .clauseFinal
  distribution
    | .imperative, .matrix => some .optional
    | _, _ => none

end Marathi.Particles
