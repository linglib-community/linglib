module

public import Linglib.Syntax.Clause.Particle

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
def ali : Clause.Particle where
  morphs := [.free "ali"]
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *a*, the colloquial clause-initial polar question particle. -/
def a : Clause.Particle where
  morphs := [.free "a"]
  anchor := .clause {.initial}
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *kaj* (literally 'what'), the colloquial clause-initial polar question particle. -/
def kaj : Clause.Particle where
  morphs := [.free "kaj"]
  anchor := .clause {.initial}
  distribution := a.distribution

end Slovenian.QuestionParticles
