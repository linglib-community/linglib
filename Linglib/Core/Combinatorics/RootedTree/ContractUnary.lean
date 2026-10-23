/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic

@[expose] public section

open RoseTree UnorderedTree

/-!
# Contracting unary vertices of a rose tree

`contractUnary` collapses every unary vertex (one with exactly one child) into that
child — the series reduction normalizing a rooted tree to one with no unary vertices.
Each contracted vertex disappears whole, so the vertex count drops by exactly the
number of unary vertices.

## Main definitions

* `RoseTree.contractUnary`, `RoseTree.numUnary`: the contraction and the unary-vertex
  count, with descents to the `UnorderedTree` quotient.

## Main results

* `RoseTree.numUnary_contractUnary`: the result has no unary vertices.
* `RoseTree.contractUnary_eq_self_iff`: the fixed points are exactly the unary-free
  trees; hence `contractUnary_idem`.
* `RoseTree.numNodes_contractUnary_add_numUnary`: each contraction removes one vertex.

`[UPSTREAM]` candidate alongside the `RoseTree` carrier.

-/

namespace RoseTree

variable {α : Type*} (a : α) (c d : RoseTree α) (cs : List (RoseTree α))

/-! ### The contraction -/

/-- Rebuild a node from already-contracted children: a lone child replaces the node,
    otherwise the node is kept. -/
def contractCombine : List (RoseTree α) → RoseTree α
  | [c] => c
  | cs  => node a cs

private theorem contractCombine_cons₂ :
    contractCombine a (c :: d :: cs) = node a (c :: d :: cs) := rfl

/-- Contract every unary (single-child) vertex into its child. -/
def contractUnary : RoseTree α → RoseTree α :=
  fold contractCombine

private theorem contractUnary_node :
    contractUnary (node a cs) = contractCombine a (cs.map contractUnary) := by
  simp only [contractUnary, fold_node]

@[simp] theorem contractUnary_leaf : contractUnary (node a []) = node a [] := rfl

@[simp] theorem contractUnary_node_singleton :
    contractUnary (node a [c]) = contractUnary c := rfl

@[simp] theorem contractUnary_node_cons₂ :
    contractUnary (node a (c :: d :: cs)) = node a ((c :: d :: cs).map contractUnary) := by
  rw [contractUnary_node, List.map_cons, List.map_cons, contractCombine_cons₂]

/-- The number of unary (single-child) vertices. -/
def numUnary : RoseTree α → ℕ :=
  fold fun _ ns => (if ns.length = 1 then 1 else 0) + ns.sum

@[simp] theorem numUnary_node :
    numUnary (node a cs) = (if cs.length = 1 then 1 else 0) + (cs.map numUnary).sum := by
  simp only [numUnary, fold_node, List.length_map]

/-! ### Vertex-count conservation -/

theorem numNodes_contractUnary_node :
    (contractUnary (node a cs)).numNodes + (if cs.length = 1 then 1 else 0)
      = 1 + (cs.map fun c => (contractUnary c).numNodes).sum := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩ <;> simp [Nat.add_comm, Function.comp_def]

/-- Each contracted unary vertex removes exactly one vertex. -/
theorem numNodes_contractUnary_add_numUnary (t : RoseTree α) :
    (contractUnary t).numNodes + t.numUnary = t.numNodes := by
  induction t with
  | node a cs ih =>
    rw [numUnary_node, numNodes_node, ← List.map_congr_left ih, List.sum_map_add,
      ← Nat.add_assoc, numNodes_contractUnary_node, Nat.add_assoc]
    omega

/-! ### `contractUnary` normalizes: no unary vertices remain -/

theorem numUnary_contractUnary_node :
    (contractUnary (node a cs)).numUnary = (cs.map fun c => (contractUnary c).numUnary).sum := by
  rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩ <;> simp [Function.comp_def]

/-- After contraction no unary vertices remain. -/
@[simp] theorem numUnary_contractUnary (t : RoseTree α) : (contractUnary t).numUnary = 0 := by
  induction t with
  | node a cs ih =>
    rw [numUnary_contractUnary_node, List.map_congr_left ih]
    simp

private theorem eq_zero_of_sum_eq_zero {l : List ℕ} (h : l.sum = 0) : ∀ n ∈ l, n = 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, Nat.add_eq_zero_iff] at h
    exact List.forall_mem_cons.mpr ⟨h.1, ih h.2⟩

/-- The fixed points of `contractUnary` are exactly the unary-free trees. -/
theorem contractUnary_eq_self_iff {t : RoseTree α} :
    contractUnary t = t ↔ t.numUnary = 0 := by
  refine ⟨fun h => h ▸ numUnary_contractUnary t, fun h => ?_⟩
  induction t with
  | node a cs ih =>
    rcases cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
    · rfl
    · simp at h
    · rw [numUnary_node, ite_eq_right (by simp only [List.length_cons]; omega), Nat.zero_add] at h
      rw [contractUnary_node_cons₂, List.map_congr_left fun x hx =>
          ih x hx (eq_zero_of_sum_eq_zero h _ (List.mem_map_of_mem hx)), List.map_id']

/-- `contractUnary` is idempotent. -/
@[simp] theorem contractUnary_idem (t : RoseTree α) :
    contractUnary (contractUnary t) = contractUnary t :=
  contractUnary_eq_self_iff.mpr (numUnary_contractUnary t)

/-! ### `Perm` invariance -/

theorem numUnary_perm {t s : RoseTree α} (h : Perm t s) : t.numUnary = s.numUnary :=
  fold_perm (fun _ _ _ h' => by rw [h'.length_eq, h'.sum_eq]) h

/-- `contractUnary` respects `Perm`: contraction descends to the nonplanar quotient
    (`fold_rel` at `S := Perm`; the algebra congruence is the inline match). -/
theorem Perm.contractUnary {t s : RoseTree α} (h : Perm t s) :
    Perm t.contractUnary s.contractUnary :=
  fold_rel (fun a {L₁ L₂} h' =>
      match L₁, L₂, (PermList.of_rel h').length_eq, PermList.of_rel h' with
      | [], [], _, _ => .refl _
      | [_], [_], _, h => h.singleton_inv
      | _ :: _ :: _, _ :: _ :: _, _, h => .node h
      | [], _ :: _, hl, _ | [_], [], hl, _ | [_], _ :: _ :: _, hl, _
      | _ :: _ :: _, [], hl, _ | _ :: _ :: _, [_], hl, _ => by simp at hl) h

end RoseTree

/-! ### Descent to `UnorderedTree` -/

namespace UnorderedTree

variable {α : Type*}

/-- The number of unary vertices of a nonplanar tree. -/
def numUnary : UnorderedTree α → ℕ :=
  Quotient.lift RoseTree.numUnary fun _ _ h => RoseTree.numUnary_perm h

@[simp] theorem numUnary_mk (t : RoseTree α) : (mk t).numUnary = t.numUnary := rfl

/-- Contract every unary vertex into its child. -/
def contractUnary : UnorderedTree α → UnorderedTree α :=
  Quotient.map RoseTree.contractUnary fun _ _ h => h.contractUnary

@[simp] theorem contractUnary_mk (t : RoseTree α) :
    contractUnary (mk t) = mk t.contractUnary := rfl

/-- Each contracted unary vertex removes exactly one vertex. -/
theorem numNodes_contractUnary_add_numUnary (t : UnorderedTree α) :
    (contractUnary t).numNodes + t.numUnary = t.numNodes :=
  Quotient.inductionOn t fun p => RoseTree.numNodes_contractUnary_add_numUnary p

/-- After contraction no unary vertices remain. -/
@[simp] theorem numUnary_contractUnary (t : UnorderedTree α) : (contractUnary t).numUnary = 0 :=
  Quotient.inductionOn t fun p => RoseTree.numUnary_contractUnary p

/-- `contractUnary` is idempotent. -/
@[simp] theorem contractUnary_idem (t : UnorderedTree α) :
    contractUnary (contractUnary t) = contractUnary t :=
  Quotient.inductionOn t fun p => congrArg mk (RoseTree.contractUnary_idem p)

end UnorderedTree
