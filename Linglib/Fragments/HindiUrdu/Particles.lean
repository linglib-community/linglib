module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Hindi-Urdu interrogative particles

Hindi-Urdu has no polar *wh*-complementizer (English *whether*, Italian
*se*): finite complements of every clause type are introduced by the
general subordinator *ki* (compare Hungarian *hogy*), and matrix polar
questions are marked by rising intonation plus the optional particle
*kya:*. *kya:* occurs in polar and alternative but not constituent
questions and occupies a projection above CP (Bhatt and Dayal's ForceP,
Dayal's later PerspP); it embeds only in quasi-subordination. Since
nothing clause-types a bare embedded polar clause, subordinated polar
questions require the overt alternative *ya: nahĩ:* "or not". This file
provides *kya:* and *ya: nahĩ:* as `Clause.Marker` values and *ki* as a
`Complementizer`, with recorded licensing distributions.

## Main declarations

* `HindiUrdu.Particles.kya` — the polar question particle.
* `HindiUrdu.Particles.ki` — the general subordinator.
* `HindiUrdu.Particles.ya_nahi` — the overt polar alternative.

## References

* [bhatt-dayal-2014]
* [bhatt-dayal-2020], §2, §5
* [dayal-2025], §1.3, ex. 70–71
-/

@[expose] public section

namespace HindiUrdu.Particles

/-- *ki* is the general subordinator, distinct from the homophonous
disjunction `HindiUrdu.Coordination.ki` of alternative questions. -/
def ki : Complementizer where
  morphs := [.free "ki"]
  anchor := .clause {.initial}
  distribution := fun (c, e) ↦ match c with
    | .declarative | .polar | .alternative | .constituent =>
      match e with
      | .matrix => some .excluded
      | .subordinated => some .optional
      | .quasiSubordinated => some .optional
      | .quotation | .insubordinated => none
    | _ => none

/-- *kya:* is a polar question particle. -/
def kya : Clause.Marker where
  morphs := [.free "kya:"]
  anchor := .clause .univ
  distribution
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .excluded
    | (.polar, .quasiSubordinated) => some .optional
    | (.alternative, .matrix) => some .optional
    | (.constituent, _) => some .excluded
    | _ => none

/-- *ya: nahĩ:* "or not" is the overt disjunct forming a polar
alternative question. -/
def ya_nahi : Clause.Marker where
  morphs := [.free "ya:", .free "nahĩ:"]
  anchor := .clause {.final}
  distribution
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .obligatory
    | (.polar, .quasiSubordinated) => some .optional
    | _ => none

end HindiUrdu.Particles
