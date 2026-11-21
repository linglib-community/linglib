module

public import Linglib.Syntax.Clause.Marker

/-!
# Serbian question particles

Serbian polar questions are marked by intonation alone, by the enclitic *li*
hosted by the fronted finite verb, or by sentence-initial *da li*, which
[browne-1993] regards as the full form of *li* and which leaves the order of
the rest of the clause free; both markers also introduce embedded and
alternative questions. Colloquial *je li* and the mirative *zar* are the
tag-forming markers *je li?* and *zar ne?* of [browne-1993]; [simik-2024]
reports *je li* as the colloquial rival of the neutral *da li* strategy and
*zar* as the Serbian kin of Russian *razve*, whose formal semantics the
chapter leaves open. Bias profiles of the strategies live in `Simik2024`.

## References

* [browne-1993], §4.2
* [simik-2024], §4.1, §4.2.4
-/

@[expose] public section

namespace Serbian.QuestionParticles

/-- *li* is the enclitic polar question marker, hosted by the finite verb in
its full form, which it draws to the front of the clause. -/
def li : Clause.Marker where
  morphs := [.encl "li"]
  anchor := .clause {.second}
  distribution
    | (.polar, .matrix) => some .optional
    | (.polar, .subordinated) => some .optional
    | (.alternative, .matrix) => some .optional
    | _ => none

/-- *da li* is the sentence-initial polar question marker, the full form of
*li* that leaves the order of the remaining clause free. -/
def daLi : Clause.Marker where
  morphs := [.free "da", .encl "li"]
  anchor := .clause {.initial}
  distribution := li.distribution

/-- *je li* is the colloquial sentence-initial polar question marker, also
the tag *je li?*. -/
def jeLi : Clause.Marker where
  morphs := [.free "je", .encl "li"]
  anchor := .clause {.initial}
  distribution
    | (.polar, .matrix) => some .optional
    | _ => none

/-- *zar* is the clause-initial mirative particle, kin of Russian *razve*,
also the tag *zar ne?*. -/
def zar : Clause.Marker where
  morphs := [.free "zar"]
  anchor := .clause {.initial}
  distribution := jeLi.distribution

end Serbian.QuestionParticles
