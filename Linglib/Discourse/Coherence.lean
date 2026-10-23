module

public import Mathlib.Tactic.DeriveFintype

/-!
# Coherence relations

This file defines the coherence relations of [kehler-2002], the ways two adjacent discourse
segments are understood to connect, and their classification into the three kinds of connection
between ideas Hume distinguished: resemblance, cause–effect, and contiguity. The classes differ in
the inference that establishes the relation. A resemblance relation aligns the predicates and
arguments of the two segments and compares them; a cause–effect relation infers a proposition from
each segment and connects the two by an implication; a contiguity relation reads the second
segment's eventuality as continuing from the end state of the first. A cause–effect relation is
oriented by which segment supplies the cause, and the orientation is defined on exactly that
class (`Relation.causalDirection_isSome_iff`), so Explanation is Result with the segments
exchanged, and Denial of Preventer is Violated Expectation with the segments exchanged.

## Main definitions

* `Discourse.Coherence.Class`: resemblance, cause–effect, or contiguity.
* `Discourse.Coherence.Relation`: the eleven relations, with `Relation.toClass`.
* `Discourse.Coherence.Direction`, `Relation.causalDirection`: which segment a cause–effect
  relation takes as the cause.

## References

* [kehler-2002]
* [hobbs-1979]
-/

@[expose] public section

namespace Discourse.Coherence

/-- The three kinds of connection between ideas, which classify coherence relations by the
inference that establishes them. -/
inductive Class where
  /-- The predicates and arguments of the segments are aligned and compared. -/
  | resemblance
  /-- A proposition inferred from each segment, the two connected by an implication. -/
  | causeEffect
  /-- The second segment's eventuality continues from the end state of the first. -/
  | contiguity
  deriving DecidableEq, Repr, Fintype

/-- The coherence relations of [kehler-2002], each holding between a first segment and the
second that continues it. -/
inductive Relation where
  /-- A common predicate over pairwise similar arguments. -/
  | parallel
  /-- A common predicate over pairwise similar arguments, one negated or the arguments
  contrasted. -/
  | contrast
  /-- A generalization, then an instance of it. -/
  | exemplification
  /-- An instance, then the generalization it instantiates. -/
  | generalization
  /-- A generalization and an instance that runs against it, in either order. -/
  | exception
  /-- A second description of the first segment's eventuality. -/
  | elaboration
  /-- The first segment's proposition brings about the second's (*and so*). -/
  | result
  /-- The second segment's proposition brings about the first's (*because*). -/
  | explanation
  /-- The first segment's proposition would normally rule out the second's (*but*). -/
  | violatedExpectation
  /-- The second segment's proposition would normally rule out the first's (*even though*). -/
  | denialOfPreventer
  /-- The second segment's eventuality follows on the end state of the first's. -/
  | occasion
  deriving DecidableEq, Repr, Fintype

/-- Which segment a cause–effect relation takes as the cause: the first, so that the cause
precedes its effect, or the second, so that the effect precedes its cause. -/
inductive Direction where
  | forward
  | backward
  deriving DecidableEq, Repr, Fintype

namespace Relation

/-- The class of a relation. -/
def toClass : Relation → Class
  | .parallel | .contrast | .exemplification | .generalization | .exception | .elaboration =>
    .resemblance
  | .result | .explanation | .violatedExpectation | .denialOfPreventer => .causeEffect
  | .occasion => .contiguity

/-- The direction of a cause–effect relation: Result and Violated Expectation take the first
segment as the cause, Explanation and Denial of Preventer the second. -/
def causalDirection : Relation → Option Direction
  | .result | .violatedExpectation => some .forward
  | .explanation | .denialOfPreventer => some .backward
  | _ => none

theorem causalDirection_isSome_iff (r : Relation) :
    r.causalDirection.isSome ↔ r.toClass = .causeEffect := by
  cases r <;> decide

end Relation

end Discourse.Coherence
