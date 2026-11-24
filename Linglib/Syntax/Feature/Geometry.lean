/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.FeatureGeometry
public import Linglib.Syntax.Feature.Bundle
public import Linglib.Syntax.Feature.Person.Segment

/-!
# The φ-feature geometry of a feature bundle

A nominal bears nodes of the φ-feature geometry: the root, the person nodes of its person, and
the number nodes of its number. A node is borne only together with the nodes that dominate it, so
the nodes a feature bundle bears form a lower set of the geometry. A probe relativized to a node
is satisfied by the bundles that bear it.

## Main definitions

* `Person.Segment.toNode`: the person segments as nodes of the geometry, an order embedding.
* `Agreement.Bundle.nodes`: the lower set of nodes a feature bundle bears, with
  `Agreement.Bundle.nodeFinset` its finset and `Agreement.Bundle.numberNodeFinset` its number
  nodes.

## Main results

* `Agreement.Bundle.participant_mem_nodes`: a bundle bears Participant exactly when its person
  is a speech-act participant's.

## Implementation notes

The number nodes are those of an inventory without a contrastive Minimal node, so that a singular
bears Individuation alone. A bundle unspecified for person bears the root alone, and one
unspecified for number, or of a number the geometry does not assign, bears no number node.

## References

* [harley-ritter-2002]
* [bejar-rezac-2009]
-/

@[expose] public section

open Morphology.FeatureGeometry

/-- `Finset.Ici n` is the node `n` and the nodes it dominates. -/
instance : LocallyFiniteOrderTop Node :=
  .ofIci' Node (fun a ↦ Finset.univ.filter (a ≤ ·)) fun _ _ ↦ by simp

/-- A person segment as a node of the geometry, the root `π` as the Referring Expression node. -/
def Person.Segment.toNode : Person.Segment ↪o Node :=
  .ofMapLEIff (fun a ↦ a.casesOn' .referringExpression .participant .speaker .addressee)
    (by decide)

namespace Agreement.Bundle

/-- The number nodes a feature bundle bears, those of its number in an inventory without a
contrastive Minimal node. -/
def numberNodeFinset (c : Bundle) : Finset Node :=
  (c .number).recBotCoe ∅ fun n ↦ (numberNodes ∅ n).getD ∅

/-- The nodes a feature bundle bears, as a finset: the nodes of the segments of its person, and
its number nodes. -/
def nodeFinset (c : Bundle) : Finset Node :=
  (c .person).segments.map Person.Segment.toNode.toEmbedding ∪ c.numberNodeFinset

private theorem isLowerSet_segments (x : Person.Specification) :
    IsLowerSet (↑(x.segments.map Person.Segment.toNode.toEmbedding) : Set Node) := by
  revert x; decide

private theorem isLowerSet_number (c : Bundle) :
    IsLowerSet (↑(insert ⊥ c.numberNodeFinset) : Set Node) := by
  unfold numberNodeFinset
  generalize c .number = y
  induction y using Flat.recBotCoe with
  | bot => decide
  | coe n => cases n <;> decide

/-- The nodes a feature bundle bears. A bundle bears whatever dominates a node it bears, so they
form a lower set of the geometry. -/
def nodes (c : Bundle) : LowerSet Node where
  carrier := ↑c.nodeFinset
  lower' := by
    have h : c.nodeFinset = (c .person).segments.map Person.Segment.toNode.toEmbedding ∪
        insert ⊥ c.numberNodeFinset := by
      rw [Finset.union_insert, Finset.insert_eq_of_mem]
      · rfl
      · exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨⊥, by simp, rfl⟩)
    rw [h, Finset.coe_union]
    exact (isLowerSet_segments _).union (isLowerSet_number c)

variable {c : Bundle} {n : Node}

@[simp] theorem coe_nodes : (c.nodes : Set Node) = ↑c.nodeFinset := rfl

theorem mem_nodes : n ∈ c.nodes ↔ n ∈ c.nodeFinset := .rfl

instance (c : Bundle) : DecidablePred (· ∈ c.nodes) := fun n ↦
  inferInstanceAs (Decidable (n ∈ c.nodeFinset))

/-- Every bundle bears the root. -/
@[simp] theorem bot_mem_nodes : ⊥ ∈ c.nodes :=
  Finset.mem_union_left _ (Finset.mem_map.2 ⟨⊥, by simp, rfl⟩)

/-- A bundle bears Participant exactly when its person is a speech-act participant's. -/
@[simp] theorem participant_mem_nodes : Node.participant ∈ c.nodes ↔ c.IsSAP := by
  have key : ∀ (x : Person.Specification) (y : Flat Number),
      Node.participant ∈ x.segments.map Person.Segment.toNode.toEmbedding ∪
        y.recBotCoe (C := fun _ ↦ Finset Node) ∅ (fun n ↦ (numberNodes ∅ n).getD ∅) ↔
          x.IsSAP := by
    intro x y
    induction y using Flat.recBotCoe with
    | bot => revert x; decide
    | coe n => cases n <;> (revert x; decide)
  exact key _ _

/-- A plural bundle bears Group. -/
theorem IsPlural.group_mem_nodes (h : c.IsPlural) : Node.group ∈ c.nodes := by
  rw [mem_nodes, nodeFinset, numberNodeFinset, show c .number = ↑Number.plural from h]
  exact Finset.mem_union_right _ (by decide)

end Agreement.Bundle
