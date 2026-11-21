module

public import Linglib.Syntax.Clause.Particle

/-!
# Polish question particles

Polish default polar questions are introduced by clause-initial *czy*, which the quiz question
requires (Šimík's (30)); declarative polar questions without it are grammatical but carry
evidential bias. The mirative *czyżby* is the Polish kin of Russian *razve* (Šimík §4.2.4).

## References

* [simik-2024]
-/

@[expose] public section

namespace Polish.QuestionParticles

/-- *czy*, the clause-initial polar question particle. -/
def czy : Clause.Particle where
  morphs := [.free "czy"]
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .obligatory
    | _ => none

/-- *czyżby*, the clause-initial mirative particle, kin of Russian *razve*. -/
def czyzby : Clause.Particle where
  morphs := [.free "czyżby"]
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

end Polish.QuestionParticles
