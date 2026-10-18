module

public import Linglib.Syntax.Category.Particle.Basic

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
def cy : Particle where
  form := "čy"
  script := some "чи"
  position := some .clauseInitial
  distribution
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .obligatory
    | _, _ => none

/-- хіба *xiba*, the clause-initial mirative particle, kin of Russian *razve*. -/
def xiba : Particle where
  form := "xiba"
  script := some "хіба"
  position := some .clauseInitial
  distribution
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

end Ukrainian.QuestionParticles
