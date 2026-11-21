/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.InsertionUnordered

/-!
# The grafting pre-Lie product on rooted trees

The grafting product `T ◁ S` of two rooted trees is the multiset of the trees obtained by
grafting `S` onto one vertex of `T`, that is, by making `S` a new child of that vertex. It has
one summand for each vertex of `T` (`RoseTree.insertSum_eq_map_graft`), the new child at the root
or inside one child (`RoseTree.insertSum_node`), and is the one-guest case of the multi-insertion
`insertion T gs`, which grafts every guest of `gs` at once. On nonplanar trees, grafting `S₁` and
then `S₂` is grafting `S₁ ◁ S₂`, plus grafting both at once
(`UnorderedTree.insertSum_bind_insertSum`), so the associator is symmetric in its last two
arguments (`UnorderedTree.insertSum_assoc_symm`). This is the right pre-Lie identity, by which
Chapoton and Livernet make the rooted trees a pre-Lie algebra.

## Implementation notes

The pre-Lie identity holds only once children are unordered: grafting `S₁` and then `S₂` at one
vertex makes the new children `[S₂, S₁]`, where grafting both at once makes them `[S₁, S₂]`.

## References

* [chapoton-livernet-2001]
* [foissy-2021]
* [oudom-guin-2008]
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

/-- The grafting product `T ◁ S` is the multiset of trees obtained by grafting `S` as a new
first child of one vertex of `T`. -/
def insertSum (T S : RoseTree α) : Multiset (RoseTree α) :=
  insertion T [S]

@[inherit_doc] scoped infixl:65 " ◁ " => insertSum

/-- `T ◁ S` sums, over the vertices `p` of `T`, the grafting of `S` at `p`. -/
theorem insertSum_eq_map_graft (T S : RoseTree α) :
    T ◁ S = ((vertices T).map fun p ↦ graft T (Function.update (fun _ ↦ []) p [S]) :
      Multiset (RoseTree α)) := by
  rw [insertSum, insertion_def, List.length_singleton, List.replicate_one, List.sections_singleton,
    List.map_map]
  refine congrArg _ (List.map_congr_left fun p _ ↦ congrArg _ (funext fun q ↦ ?_))
  by_cases h : p = q <;> simp [h, eq_comm]

/-- Grafting into a node either adds a child at the root or grafts inside the children. -/
theorem insertSum_node (a : α) (cs : List (RoseTree α)) (S : RoseTree α) :
    node a cs ◁ S = node a (S :: cs) ::ₘ (insertionForest cs [S]).map (node a) := by
  rw [insertSum, insertion_node, show [S].sublists'.revzip = [([], [S]), ([S], [])] from rfl,
    ← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_singleton, Multiset.singleton_bind,
    insertionForest_nil_guests, Multiset.map_singleton, add_comm, Multiset.singleton_add]
  rfl

@[simp] theorem insertSum_leaf (a : α) (S : RoseTree α) : leaf a ◁ S = {node a [S]} := by
  rw [insertSum_node, insertionForest_empty_host_nonempty_guests, Multiset.map_zero]
  rfl

theorem card_insertSum (T S : RoseTree α) : Multiset.card (T ◁ S) = T.numNodes := by
  rw [insertSum_eq_map_graft, Multiset.coe_card, List.length_map, length_vertices]

/-- Grafting a leaf onto a two-vertex path adds it at the root or at the old leaf. -/
example : node 0 [leaf 1] ◁ leaf 2 = {node 0 [leaf 2, leaf 1], node 0 [node 1 [leaf 2]]} := by
  decide

/-! ### The pre-Lie identity -/

private theorem insertionForest_cons_singleton (T : RoseTree α) (F : List (RoseTree α))
    (S : RoseTree α) :
    insertionForest (T :: F) [S] =
      (T ◁ S).map (· :: F) + (insertionForest F [S]).map (T :: ·) := by
  rw [insertionForest_cons, show [S].sublists'.revzip = [([], [S]), ([S], [])] from rfl]
  simp only [← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_nil, Multiset.zero_bind,
    add_zero, insertion_nil_guests, insertionForest_nil_guests, Multiset.singleton_bind,
    Multiset.map_singleton, Multiset.bind_singleton, insertSum]
  exact add_comm _ _

private theorem insertionForest_cons_pair (T : RoseTree α) (F : List (RoseTree α))
    (S₁ S₂ : RoseTree α) :
    insertionForest (T :: F) [S₁, S₂] =
      (insertion T [S₁, S₂]).map (· :: F) +
        (T ◁ S₁).bind (fun X => (insertionForest F [S₂]).map (X :: ·)) +
        (T ◁ S₂).bind (fun X => (insertionForest F [S₁]).map (X :: ·)) +
        (insertionForest F [S₁, S₂]).map (T :: ·) := by
  rw [insertionForest_cons,
    show [S₁, S₂].sublists'.revzip = [([], [S₁, S₂]), ([S₂], [S₁]), ([S₁], [S₂]), ([S₁, S₂], [])]
      from rfl]
  simp only [← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_nil, Multiset.zero_bind,
    add_zero, insertion_nil_guests, insertionForest_nil_guests, Multiset.singleton_bind,
    Multiset.map_singleton, Multiset.bind_singleton, insertSum]
  abel

private theorem insertion_node_pair (a : α) (cs : List (RoseTree α)) (S₁ S₂ : RoseTree α) :
    insertion (node a cs) [S₁, S₂] =
      {node a (S₁ :: S₂ :: cs)} +
        (insertionForest cs [S₂]).map (fun Y => node a (S₁ :: Y)) +
        (insertionForest cs [S₁]).map (fun Y => node a (S₂ :: Y)) +
        (insertionForest cs [S₁, S₂]).map (node a) := by
  rw [insertion_node,
    show [S₁, S₂].sublists'.revzip = [([], [S₁, S₂]), ([S₂], [S₁]), ([S₁], [S₂]), ([S₁, S₂], [])]
      from rfl]
  simp only [← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_nil, Multiset.zero_bind,
    add_zero, insertionForest_nil_guests, Multiset.map_singleton, List.nil_append,
    List.cons_append]
  abel

open UnorderedTree in
mutual
theorem map_mk_bind_insertSum : ∀ (T S₁ S₂ : RoseTree α),
    ((T ◁ S₁).bind (· ◁ S₂)).map mk =
      ((S₁ ◁ S₂).bind (T ◁ ·)).map mk + (insertion T [S₁, S₂]).map mk
  | node a cs, S₁, S₂ => by
    have e1 : mk (node a (S₂ :: S₁ :: cs)) = mk (node a (S₁ :: S₂ :: cs)) :=
      mk_eq_mk_iff.mpr (Perm.node_of_perm (List.Perm.swap _ _ _))
    have e5 := congrArg (Multiset.map fun L : List (UnorderedTree α) =>
      UnorderedTree.node a (L : Multiset (UnorderedTree α))) (map_mk_bind_insertionForest cs S₁ S₂)
    simp only [Multiset.map_add, Multiset.map_map, Multiset.map_bind, Function.comp_def,
      node_mk_tree_list] at e5
    simp only [insertSum_node, insertion_node_pair, insertionForest_cons_singleton,
      Multiset.cons_bind, Multiset.bind_map, Multiset.map_add, Multiset.map_cons,
      Multiset.map_map, Multiset.map_bind, Multiset.map_singleton, Function.comp_def]
    simp only [Multiset.bind_cons]
    rw [e5, e1]
    simp only [← Multiset.singleton_add]
    abel
theorem map_mk_bind_insertionForest : ∀ (F : List (RoseTree α)) (S₁ S₂ : RoseTree α),
    ((insertionForest F [S₁]).bind (insertionForest · [S₂])).map (List.map mk) =
      ((S₁ ◁ S₂).bind (insertionForest F [·])).map (List.map mk) +
        (insertionForest F [S₁, S₂]).map (List.map mk)
  | [], S₁, S₂ => by simp
  | T :: F, S₁, S₂ => by
    have hT := congrArg (Multiset.map (· :: F.map mk)) (map_mk_bind_insertSum T S₁ S₂)
    have hF := congrArg (Multiset.map (mk T :: ·)) (map_mk_bind_insertionForest F S₁ S₂)
    simp only [Multiset.map_add, Multiset.map_map, Multiset.map_bind, Function.comp_def] at hT hF
    simp only [insertionForest_cons_singleton, insertionForest_cons_pair, Multiset.add_bind,
      Multiset.bind_map, Multiset.bind_add, Multiset.map_add, Multiset.map_map,
      Multiset.map_bind, Function.comp_def, List.map_cons]
    rw [hT, hF, Multiset.bind_map_comm (insertionForest F [S₁]) (T ◁ S₂)]
    abel
end

/-- Every summand of `T ◁ S` has the vertices of `T` and those of `S`. -/
theorem numNodes_of_mem_insertSum {T S X : RoseTree α} (h : X ∈ T ◁ S) :
    X.numNodes = T.numNodes + S.numNodes := by
  rw [insertSum_eq_map_graft, Multiset.mem_coe, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [numNodes_graft, List.sum_map_eq_nsmul_single p _ fun q hq _ ↦ by simp [hq],
    @List.count_eq_one_of_mem _ instBEqOfDecidableEq _ _ _ (nodup_vertices T) hp]
  simp

/-- Grafting is not associative, since `(0 ◁ 1) ◁ 2` has two summands and `0 ◁ (1 ◁ 2)` one. -/
example : (leaf 0 ◁ leaf 1).bind (· ◁ leaf 2) ≠ (leaf 1 ◁ leaf 2).bind (leaf 0 ◁ ·) := by
  decide

end RoseTree

namespace UnorderedTree

variable {α : Type*}

/-- The grafting product on nonplanar trees, the insertion of a single guest. -/
def insertSum (T S : UnorderedTree α) : Multiset (UnorderedTree α) :=
  insertion T {S}

@[inherit_doc] scoped infixl:65 " ◁ " => UnorderedTree.insertSum

@[simp] theorem mk_insertSum (T S : RoseTree α) :
    mk T ◁ mk S = (RoseTree.insertSum T S).map mk :=
  insertion_mk T [S]

theorem card_insertSum (T S : UnorderedTree α) : Multiset.card (T ◁ S) = T.numNodes :=
  Quotient.inductionOn₂ T S fun t s => by
    change Multiset.card (mk t ◁ mk s) = (mk t).numNodes
    rw [mk_insertSum, Multiset.card_map, RoseTree.card_insertSum, numNodes_mk]

/-- Grafting into a node either adds a child at the root or grafts inside the children. -/
theorem insertSum_node (a : α) (F : Multiset (UnorderedTree α)) (S : UnorderedTree α) :
    node a F ◁ S = node a (S ::ₘ F) ::ₘ (insertionMultiset F {S}).map (node a) := by
  rw [insertSum, insertion_node, ← Multiset.cons_zero, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp only [insertionMultiset_zero_right, add_comm, Multiset.map_singleton, Prod.map_apply, id,
    Multiset.cons_bind, Multiset.singleton_bind, Multiset.cons_zero, Multiset.singleton_add,
    add_zero]
  rw [add_comm, Multiset.singleton_add, add_comm F, Multiset.singleton_add]

/-- Every summand of `T ◁ S` has the vertices of `T` and those of `S`. -/
theorem numNodes_of_mem_insertSum {T S X : UnorderedTree α} (h : X ∈ T ◁ S) :
    X.numNodes = T.numNodes + S.numNodes := by
  induction T using Quotient.inductionOn with | h t =>
  induction S using Quotient.inductionOn with | h s =>
  rw [quot_mk_eq_mk, quot_mk_eq_mk, mk_insertSum, Multiset.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  rw [numNodes_mk, RoseTree.numNodes_of_mem_insertSum hx]
  rfl

/-- Grafting `S₁` then `S₂` into `T` is grafting `S₁ ◁ S₂` into `T` plus grafting both at once, the
degree-two case of the recursion by which [oudom-guin-2008] extend a pre-Lie product to the
symmetric algebra. -/
theorem insertSum_bind_insertSum (T S₁ S₂ : UnorderedTree α) :
    (T ◁ S₁).bind (· ◁ S₂) = (S₁ ◁ S₂).bind (T ◁ ·) + insertion T {S₁, S₂} := by
  induction T using Quotient.inductionOn with | h t =>
  induction S₁ using Quotient.inductionOn with | h s₁ =>
  induction S₂ using Quotient.inductionOn with | h s₂ =>
  simp only [quot_mk_eq_mk, mk_insertSum, Multiset.bind_map, ← Multiset.map_bind]
  exact (RoseTree.map_mk_bind_insertSum t s₁ s₂).trans (congrArg _ (insertion_mk t [s₁, s₂]).symm)

/-- The associator of the grafting product is symmetric in its last two arguments, so that
`(T ◁ S₁) ◁ S₂ - T ◁ (S₁ ◁ S₂) = (T ◁ S₂) ◁ S₁ - T ◁ (S₂ ◁ S₁)`, here stated without
subtraction. -/
theorem insertSum_assoc_symm (T S₁ S₂ : UnorderedTree α) :
    (T ◁ S₁).bind (· ◁ S₂) + (S₂ ◁ S₁).bind (T ◁ ·) =
      (T ◁ S₂).bind (· ◁ S₁) + (S₁ ◁ S₂).bind (T ◁ ·) := by
  rw [insertSum_bind_insertSum, insertSum_bind_insertSum T S₂ S₁, Multiset.pair_comm]
  abel

theorem insertion_zero (T : UnorderedTree α) : insertion T 0 = {T} := by
  induction T using Quotient.inductionOn with | h t =>
  exact (insertion_mk t []).trans
    (by rw [RoseTree.insertion_nil_guests, Multiset.map_singleton]; rfl)

/-- Grafting into a forest grafts into its first tree or into the rest. -/
theorem insertionMultiset_cons_singleton (T : UnorderedTree α) (F : Multiset (UnorderedTree α))
    (S : UnorderedTree α) :
    insertionMultiset (T ::ₘ F) {S} =
      (T ◁ S).map (· ::ₘ F) + (insertionMultiset F {S}).map (T ::ₘ ·) := by
  rw [insertionMultiset_cons, ← Multiset.cons_zero S, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp only [insertionMultiset_zero_right, insertion_zero, Multiset.map_singleton, Prod.map_apply,
    id, Multiset.cons_bind, Multiset.singleton_bind, Multiset.cons_zero, Multiset.singleton_add,
    Multiset.bind_singleton, insertSum]
  exact add_comm _ _

theorem insertionMultiset_singleton_singleton (T S : UnorderedTree α) :
    insertionMultiset {T} {S} = (T ◁ S).map ({·}) :=
  insertionMultiset_singleton T {S}

theorem productMultiset_singleton_singleton (T S : UnorderedTree α) :
    productMultiset {T} {S} = {T, S} ::ₘ (T ◁ S).map ({·}) := by
  rw [productMultiset, ← Multiset.cons_zero, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [insertionMultiset_zero_right, insertionMultiset_singleton_singleton, add_comm]

end UnorderedTree
