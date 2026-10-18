module

public import Linglib.Syntax.Category.Particle.Basic

/-!
# Bulgarian question particles

Bulgarian marks polar questions with two complementizers, the enclitic *li* and the
clause-initial *dali*, and a topic may precede either. *Li* attaches to the focus of the question,
the verb in a neutral question, where Russian *li* follows a single constituent (Šimík §4.1), and
it marks the canonical information-seeking question. *Dali* adds a 'wondering' component and does
not necessarily solicit a response, and so is out of place in a quiz (Šimík fn. 40, after
Simeonova and Kamali). Both introduce embedded polar questions (Simeonova and Kamali's (5); Franks
and King §8.1.2), and *li* also follows a focused wh-phrase in a constituent question. *Dali*
occurs only in interrogatives, while *li* has non-interrogative uses in conditionals, disjunctions
and expressions such as *edva li* 'hardly'. The mirative *nima* is the Bulgarian kin of Russian
*razve* (Šimík §4.2.4).

## References

* [simik-2024]
* [simeonova-kamali-2024]
* [franks-king-2000]
-/

@[expose] public section

namespace Bulgarian.QuestionParticles

/-- ли *li*, the canonical polar question complementizer, an enclitic on the focus of the
question. -/
def li : Particle where
  form := "li"
  script := some "ли"
  position := some .postHost
  distribution
    | .polar, .matrix => some .optional
    | .polar, .subordinated => some .optional
    | .constituent, .matrix => some .optional
    | _, _ => none

/-- дали *dali*, the clause-initial polar question complementizer, which in a root question
raises an issue without expecting the addressee to resolve it. -/
def dali : Particle where
  form := "dali"
  script := some "дали"
  position := some .clauseInitial
  distribution
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | .polar, .subordinated => some .optional
    | _, _ => none

/-- нима *nima*, the clause-initial mirative particle, kin of Russian *razve*. -/
def nima : Particle where
  form := "nima"
  script := some "нима"
  position := some .clauseInitial
  distribution
    | .declarative, .matrix => some .excluded
    | .polar, .matrix => some .optional
    | _, _ => none

end Bulgarian.QuestionParticles
