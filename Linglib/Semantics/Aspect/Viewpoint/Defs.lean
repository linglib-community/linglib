module

public import Mathlib.Tactic.DeriveFintype

/-!
# Viewpoints

A viewpoint is the presentation of a situation: one of Klein's four relations between the topic
time and the situation time, or Smith's neutral viewpoint. At its coarsest it is the opposition
of perfective and imperfective. The operators that viewpoints denote are in
`Semantics/Aspect/Viewpoint/Basic.lean`.

## References

* [smith-1997]
* [klein-1994]
-/

@[expose] public section

namespace Aspect

/-- The viewpoints are the four relations of [klein-1994] between the topic time and the situation
time, and the neutral viewpoint of [smith-1997], the default in the absence of aspect
morphology. -/
inductive ViewpointType
  | imperfective
  | perfective
  | perfect
  | prospective
  | neutral
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The opposition of perfective and imperfective is viewpoint aspect at its coarsest, the right
granularity where the fact at issue is that the perfective requires actualization and the
imperfective does not, or where the opposition is lexically encoded, as in `Verb.perfectivity`. -/
inductive Perfectivity
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

end Aspect
