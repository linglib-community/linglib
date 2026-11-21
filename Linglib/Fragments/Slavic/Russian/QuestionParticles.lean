module

public import Linglib.Syntax.Clause.Particle

/-!
# Russian question particles

Russian marks formal polar questions with the second-position enclitic *li*, obligatory in
embedded polar questions, while colloquial matrix polar questions are marked by intonation alone
and can be used rhetorically ([esipova-romero-2023]). The clause-initial mirative *razve* cannot be
used in embedded interrogatives or in wh-interrogatives ([simik-2024] §4.2.4, after Korotkova);
*neuželi* is its sibling that lexicalizes VERUM.

## References

* [esipova-romero-2023]
* [simik-2024]
* [repp-geist-2022]
-/

@[expose] public section

namespace Russian.QuestionParticles

/-- ли li is the neutral polar question particle (formal register), a
second-position enclitic on the focused constituent. -/
def li : Clause.Particle where
  morphs := [.encl "li"]
  script := some "ли"
  anchor := .clause {.second}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .obligatory
    | _ => none

/-- разве razve is the mirative/dubitative question particle, signalling
conflict between the speaker's prior epistemic state and current
contextual evidence. -/
def razve : Clause.Particle where
  morphs := [.free "razve"]
  script := some "разве"
  anchor := .clause {.initial}
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .excluded
    | (.constituent, .matrix) => some .excluded
    | _ => none

/-- неужели neuželi is the mirative question particle that, unlike *razve*,
lexicalizes VERUM and so combines with inner negation only
([repp-geist-2022] as reported by [simik-2024]). -/
def neuzeli : Clause.Particle where
  morphs := [.free "neuželi"]
  script := some "неужели"
  anchor := .clause {.initial}
  distribution := razve.distribution

end Russian.QuestionParticles
