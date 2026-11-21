module

public import Linglib.Syntax.Clause.Particle

/-!
# Macedonian question particles

Macedonian default polar questions are introduced by clause-initial *dali*, which admits negation
without inducing bias (Šimík's (32)), or carry the enclitic *li* on the fronted verb, which is
reported to convey surprise or a negative answer expectation, unlike Bulgarian and Russian *li*
(Šimík §4.2.5). As in Bulgarian, *li* also introduces embedded polar questions (Franks and King
§8.1.2). The mirative *zar* is the Macedonian kin of Russian *razve* (Šimík §4.2.4).

## References

* [simik-2024]
* [franks-king-2000]
-/

@[expose] public section

namespace Macedonian.QuestionParticles

/-- дали *dali*, the clause-initial polar question particle. -/
def dali : Clause.Particle where
  morphs := [.free "dali"]
  script := some "дали"
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

/-- ли *li*, the polar question particle enclitic on the fronted verb, whose negated form conveys
positive epistemic bias ([simik-2024] ex. 32b). -/
def li : Clause.Particle where
  morphs := [.encl "li"]
  script := some "ли"
  anchor := .clause {.second}
  distribution
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .optional
    | _ => none

/-- зар *zar*, the clause-initial mirative particle, kin of Russian *razve*. -/
def zar : Clause.Particle where
  morphs := [.free "zar"]
  script := some "зар"
  anchor := .clause {.initial}
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

end Macedonian.QuestionParticles
