module

public import Linglib.Semantics.Aspect.Marker

/-!
# Cantonese aspect markers

The postverbal aspect suffixes of Cantonese (ISO `yue`) with the viewpoint each marks, following
[matthews-yip-1994] and [cheung-2007]: the perfective *-zo*, the experiential *-gwo*, an
experiential perfect, and the two imperfectives, the progressive *-gan* of ongoing activity and
the continuous *-zyu* of a maintained state or posture. The association of these suffixes with
the outer and inner aspect projections is the analysis of [liu-yip-2026]; the postverbal
*again*-suffix *-faan* is a presupposition trigger and is entered with the other *again*-elements
in `Languages/Cantonese/Particles.lean`.

## References

* [matthews-yip-1994]
* [cheung-1972]
* [cheung-2007]
-/

@[expose] public section

namespace Cantonese.Aspect

/-- The perfective *-zo* 咗. -/
def zo : Aspect.Marker :=
  { morphs := [.suff "zo2"], script := some "咗", gloss := "PFV", viewpoint := .perfective }

/-- The experiential *-gwo* 過, an experiential perfect. -/
def gwo : Aspect.Marker :=
  { morphs := [.suff "gwo3"], script := some "過", gloss := "EXP", viewpoint := .perfect }

/-- The progressive *-gan* 緊, an imperfective of ongoing activity. -/
def gan : Aspect.Marker :=
  { morphs := [.suff "gan2"], script := some "緊", gloss := "PROG", viewpoint := .imperfective }

/-- The continuous *-zyu* 住, an imperfective of a maintained state or posture. -/
def zyu : Aspect.Marker :=
  { morphs := [.suff "zyu6"], script := some "住", gloss := "CONT", viewpoint := .imperfective }

/-- The aspect suffixes. -/
def markers : List Aspect.Marker := [zo, gwo, gan, zyu]

end Cantonese.Aspect
