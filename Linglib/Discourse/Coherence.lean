module

public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Coherence relations

This file defines the coherence relations of [kehler-2002], the ways two adjacent discourse
segments are understood to connect, by the constraints that establish them. They fall into the
three kinds of connection between ideas Hume distinguished. A Cause–Effect relation infers a
proposition `P` from the first segment and `Q` from the second and presupposes that one normally
implies the other or its negation; the four relations are the choices of which segment supplies
the cause and whether the effect holds, so that Explanation is Result with the segments exchanged
and Denial of Preventer is Violated Expectation with the segments exchanged
(`Direction.presupposes_backward`). A Resemblance relation infers a common relation of the
parallel arguments of both segments, holding or negated in the second, and compares the
arguments by their properties: sharing one, contrasting in one, one being a member or subset of
the other, or identity. Contrast and Exception each have two definitions, and Generalization is
Exemplification with the segments exchanged (`Resemblance.holds_generalization_iff`). The one
Contiguity relation, Occasion, is stated informally in the source and has no constraint here.

## Main definitions

* `Discourse.Coherence.Relation`: the relations, a resemblance relation, a cause–effect relation
  by its direction and polarity, or Occasion, with Kehler's names as abbreviations.
* `Discourse.Coherence.Direction.presupposes`: the presupposition of a cause–effect relation.
* `Discourse.Coherence.Resemblance.Holds`: the constraint of a resemblance relation.

## Implementation notes

* The defeasible implication of a cause–effect relation, "could plausibly follow from", and the
  properties a resemblance relation compares are arguments, inferred by the hearer.
* Membership and subset among arguments are stated, as in Table 1, as strict inclusion of their
  property sets, the more general argument having fewer properties.

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

/-- Which segment a cause–effect relation takes as the cause: the first, so that the cause
precedes its effect, or the second, so that the effect precedes its cause. -/
inductive Direction where
  | forward
  | backward
  deriving DecidableEq, Repr, Fintype

/-- How a resemblance relation compares the parallel arguments `aᵢ` of the first segment and
`bᵢ` of the second ([kehler-2002] Table 1). -/
inductive Comparison where
  /-- Each pair shares a property. -/
  | common
  /-- Some `aᵢ` has a property its parallel `bᵢ` lacks. -/
  | contrasting
  /-- Some `bᵢ` is a member or subset of `aᵢ`. -/
  | memberOfFirst
  /-- Some `aᵢ` is a member or subset of `bᵢ`. -/
  | memberOfSecond
  /-- The parallel arguments are identical. -/
  | identical
  deriving DecidableEq, Repr, Fintype

/-- The resemblance relations of [kehler-2002] Table 1. -/
inductive Resemblance where
  | parallel
  | contrast
  | exemplification
  | generalization
  | exception
  | elaboration
  deriving DecidableEq, Repr, Fintype

/-- The coherence relations of [kehler-2002], each holding between a first segment and the
second that continues it: a resemblance relation, a cause–effect relation by the segment that
supplies the cause and whether the effect holds, or Occasion. -/
inductive Relation where
  | resemblance (r : Resemblance)
  | causeEffect (d : Direction) (s : Polarity)
  | occasion
  deriving DecidableEq, Repr, Fintype

namespace Relation

/-- Parallel: a common relation over pairwise similar arguments (*and*). -/
@[match_pattern] abbrev parallel : Relation := resemblance .parallel

/-- Contrast: a common relation negated in the second segment, or contrasting arguments
(*but*). -/
@[match_pattern] abbrev contrast : Relation := resemblance .contrast

/-- Exemplification: a generalization, then an instance of it (*for example*). -/
@[match_pattern] abbrev exemplification : Relation := resemblance .exemplification

/-- Generalization: an instance, then the generalization it instantiates (*in general*). -/
@[match_pattern] abbrev generalization : Relation := resemblance .generalization

/-- Exception: a generalization and an instance that runs against it, in either order
(*however*, *nonetheless*). -/
@[match_pattern] abbrev exception : Relation := resemblance .exception

/-- Elaboration: a second description of the first segment's eventuality (*that is*). -/
@[match_pattern] abbrev elaboration : Relation := resemblance .elaboration

/-- Result: the first segment's proposition normally implies the second's (*and so*). -/
@[match_pattern] abbrev result : Relation := causeEffect .forward .positive

/-- Explanation: the second segment's proposition normally implies the first's (*because*). -/
@[match_pattern] abbrev explanation : Relation := causeEffect .backward .positive

/-- Violated Expectation: the first segment's proposition normally implies the negation of the
second's (*but*). -/
@[match_pattern] abbrev violatedExpectation : Relation := causeEffect .forward .negative

/-- Denial of Preventer: the second segment's proposition normally implies the negation of the
first's (*even though*). -/
@[match_pattern] abbrev denialOfPreventer : Relation := causeEffect .backward .negative

/-- The class of a relation. -/
def toClass : Relation → Class
  | resemblance _ => .resemblance
  | causeEffect _ _ => .causeEffect
  | occasion => .contiguity

/-- The direction of a cause–effect relation. -/
def causalDirection : Relation → Option Direction
  | causeEffect d _ => some d
  | _ => none

theorem causalDirection_isSome_iff (r : Relation) :
    r.causalDirection.isSome ↔ r.toClass = .causeEffect := by
  cases r <;> simp [causalDirection, toClass]

end Relation

section CauseEffect

variable {α : Type*} [MulAction Polarity α] (N : α → α → Prop)

/-- The presupposition of a cause–effect relation ([kehler-2002] Table 2): the proposition of
the segment supplying the cause normally implies that of the other segment, or its negation when
the polarity is negative. -/
def Direction.presupposes (s : Polarity) (P Q : α) : Direction → Prop
  | .forward => N P (s • Q)
  | .backward => N Q (s • P)

/-- A backward cause–effect relation is the forward one with the segments exchanged: Explanation
is Result and Denial of Preventer is Violated Expectation with reversed clause ordering
([kehler-2002] p. 21). -/
theorem Direction.presupposes_backward (s : Polarity) (P Q : α) :
    Direction.backward.presupposes N s P Q ↔ Direction.forward.presupposes N s Q P :=
  Iff.rfl

end CauseEffect

section Resemblance

variable {ι E Φ : Type*} (props : E → Set Φ) (q : ι → Φ) (a b : ι → E)

/-- How the parallel arguments compare, given the properties `props` of each entity and the
property vector `q` the hearer infers ([kehler-2002] Table 1). -/
def Comparison.Holds : Comparison → Prop
  | .common => ∀ i, q i ∈ props (a i) ∧ q i ∈ props (b i)
  | .contrasting => ∃ i, q i ∈ props (a i) ∧ q i ∉ props (b i)
  | .memberOfFirst => ∃ i, props (a i) ⊂ props (b i)
  | .memberOfSecond => ∃ i, props (b i) ⊂ props (a i)
  | .identical => a = b

/-- The polarity of the common relation in the second segment and the comparison of the
arguments that each resemblance relation requires, two for Contrast and Exception
([kehler-2002] Table 1). -/
def Resemblance.definitions : Resemblance → List (Polarity × Comparison)
  | .parallel => [(.positive, .common)]
  | .contrast => [(.negative, .common), (.positive, .contrasting)]
  | .exemplification => [(.positive, .memberOfFirst)]
  | .generalization => [(.positive, .memberOfSecond)]
  | .exception => [(.negative, .memberOfFirst), (.negative, .memberOfSecond)]
  | .elaboration => [(.positive, .identical)]

/-- A resemblance relation holds of the parallel arguments `a` and `b` when the common relation
`p` holds of `a`, holds or fails of `b` as one of its definitions requires, and the arguments
compare as that definition requires. -/
def Resemblance.Holds (p : Set (ι → E)) (r : Resemblance) : Prop :=
  a ∈ p ∧ ∃ d ∈ r.definitions, b ∈ d.1 • p ∧ d.2.Holds props q a b

variable {props q a b} {p : Set (ι → E)}

/-- Generalization is Exemplification with the segments exchanged ([kehler-2002] p. 17). -/
theorem Resemblance.holds_generalization_iff :
    Resemblance.generalization.Holds props q a b p ↔
      Resemblance.exemplification.Holds props q b a p := by
  simp only [Holds, definitions, Comparison.Holds, List.mem_singleton, exists_eq_left,
    Polarity.positive_smul]
  tauto

/-- Elaboration is the limiting case of Parallel in which the parallel arguments are identical
([kehler-2002] p. 18). -/
theorem Resemblance.Holds.parallel_of_elaboration
    (h : Resemblance.elaboration.Holds props q a b p) (hq : ∀ i, q i ∈ props (a i)) :
    Resemblance.parallel.Holds props q a b p := by
  obtain ⟨ha, d, hd, hb, hc⟩ := h
  simp only [definitions, List.mem_singleton] at hd
  subst hd
  obtain rfl : a = b := hc
  exact ⟨ha, _, List.mem_singleton_self _, hb, fun i ↦ ⟨hq i, hq i⟩⟩

end Resemblance

end Discourse.Coherence
