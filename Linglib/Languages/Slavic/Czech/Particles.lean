module

public import Linglib.Syntax.Clause.Marker

/-!
# Czech particles

The Czech discourse particles of polar questions are `Particle` values. Staňková uses *náhodou*,
*ještě*, *fakt* and *vůbec* to diagnose the position of negation, and *snad* and *copak* are
question particles. The diagnostics are in `Studies/Stankova2026.lean` and the bias experiments
in `Studies/StankovaSimik2025.lean`.

## References

* [stankova-simik-2025]
* [stankova-2026]
* [stankova-2023]
* [simik-2024]
* [nekula-1996]
-/

@[expose] public section

namespace Czech.Particles

/-- *náhodou* 'by (any) chance' is, in its particle use, restricted to negative polar questions
([stankova-2026] §2.2.1; the adverbial reading 'accidentally' is a separate item, her fn. 3).
It diagnoses outer negation. -/
def nahodou : Clause.Marker where
  morphs := [.free "náhodou"]
  distribution
    | (.declarative, .matrix) => some .excluded
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *ještě* 'yet, still' is an aspectual particle of declaratives and polar questions
([stankova-2026] (13)-(14)), and diagnoses inner negation. -/
def jeste : Clause.Marker where
  morphs := [.free "ještě"]
  distribution
    | (.declarative, .matrix) => some .optional
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *fakt* 'really' is an emphatic particle of declaratives and polar questions
([stankova-2026] (15)), and diagnoses inner or medial negation. -/
def fakt : Clause.Marker where
  morphs := [.free "fakt"]
  distribution
    | (.declarative, .matrix) => some .optional
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *vůbec* 'at all' is a negative polarity particle of assertions and polar questions
([stankova-2026] (9)), like English *at all*. -/
def vubec : Clause.Marker where
  morphs := [.free "vůbec"]
  distribution
    | (.declarative, .matrix) => some .optional
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *snad* 'perhaps, surely not' is an adversative and mirative particle of polar questions
([nekula-1996], [stankova-2023]), which optionally supports their rhetorical readings
([simik-2024] ex. 8). -/
def snad : Clause.Marker where
  morphs := [.free "snad"]
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *copak* 'what then' is a particle of the Russian *razve* family ([simik-2024] §4.2.4) in
positive and negative polar questions ([stankova-simik-2025] exs. 19a-b, [nekula-1996]). -/
def copak : Clause.Marker where
  morphs := [.free "copak"]
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

end Czech.Particles
