module

public import Linglib.Syntax.Clause.Particle

/-!
# Ukrainian question particles

Ukrainian default polar questions are introduced by clause-initial *čy*, which the quiz question
requires (Šimík's (29)). The mirative *xiba* is the Ukrainian kin of Russian *razve* (Šimík
§4.2.4).

## References

* [simik-2024]
-/

@[expose] public section

namespace Ukrainian.QuestionParticles

/-- чи *čy*, the clause-initial polar question particle. -/
def cy : Clause.Particle where
  morphs := [.free "čy"]
  script := some "чи"
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .obligatory
    | _ => none

/-- хіба *xiba*, the clause-initial mirative particle, kin of Russian *razve*. -/
def xiba : Clause.Particle where
  morphs := [.free "xiba"]
  script := some "хіба"
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

end Ukrainian.QuestionParticles
