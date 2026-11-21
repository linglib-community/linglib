module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Slovene question particles

Slovene polar questions may be introduced by the clause-initial particle *ali*, optional in the
default quiz question ([simik-2024] ex. 28), or by the colloquial *a* and *kaj*, neutral yet
excluded from the quiz scenario ([simik-2024] §4.1). The strategy profile is in
`Studies/Simik2024.lean`.

## References

* [simik-2024]
-/

@[expose] public section

namespace Slovenian.QuestionParticles

/-- *ali*, the clause-initial polar question particle. -/
def ali : Particle where
  form := "ali"
  position := some .clauseInitial
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *a*, the colloquial clause-initial polar question particle. -/
def a : Particle where
  form := "a"
  position := some .clauseInitial
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *kaj* (literally 'what'), the colloquial clause-initial polar question particle. -/
def kaj : Particle where
  form := "kaj"
  position := some .clauseInitial
  distribution := a.distribution

end Slovenian.QuestionParticles
