/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Positions

/-!
# Grafting forests onto the vertices of a rose tree

For a tree `T` and a family `g : List ℕ → List (RoseTree α)` of forests indexed by addresses, we
define `graft T g`, the tree obtained from `T` by making the trees of `g p` new children of the
vertex at address `p`, for every vertex of `T` at once:
`graft (node a cs) g = node a (g [] ++ graftForest cs g)`, where `graftForest cs g` grafts onto
the trees of the forest `cs`, the address `i :: q` naming the vertex at `q` in the `i`-th tree.
Every address is read in `T`, not in a partly grafted tree, and the new children of a vertex come
before its old ones.

Grafting a single tree `S` at the vertex `p` is `graft T (Function.update (fun _ ↦ []) p [S])`,
the summand of the grafting pre-Lie product of [foissy-2021]. Grafting several trees is that
paper's summand of the Guin–Oudom extension, there an iterated single grafting at vertices of
`T`.

We show that `graft` reads `g` only at the vertices of `T` (`graft_congr`), that it commutes with
relabelling (`map_graft`), and that it adds the vertices of the grafted trees
(`numNodes_graft`).

## Implementation notes

The trees to graft are a function of the address and not a list of pairs of an address and a
tree. Descending into the `i`-th child is then composition with `(i :: ·)`, where a list of pairs
has to be filtered by the first index of each address and have that index removed. A list of
pairs is turned into a family by `fun p ↦ (pairs.filter (·.1 = p)).map Prod.snd`.

## References

* [foissy-2021]
-/
@[expose] public section

namespace RoseTree

variable {α β : Type*}

mutual
/-- `graft T g` makes the trees of `g p` new first children of the vertex of `T` at address `p`,
for every vertex of `T`. -/
def graft : RoseTree α → (List ℕ → List (RoseTree α)) → RoseTree α
  | node a cs, g => node a (g [] ++ graftForest cs g)
/-- `graftForest cs g` grafts onto the trees of the forest `cs`, where the address `i :: q` names
the vertex at `q` in the `i`-th tree. -/
def graftForest : List (RoseTree α) → (List ℕ → List (RoseTree α)) → List (RoseTree α)
  | [], _ => []
  | c :: cs, g => graft c (fun q ↦ g (0 :: q)) :: graftForest cs fun p ↦ g (p.modifyHead (· + 1))
end

@[simp] theorem graft_node (a : α) (cs : List (RoseTree α)) (g : List ℕ → List (RoseTree α)) :
    graft (node a cs) g = node a (g [] ++ graftForest cs g) := rfl

@[simp] theorem graftForest_nil (g : List ℕ → List (RoseTree α)) : graftForest [] g = [] := rfl

@[simp] theorem graftForest_cons (c : RoseTree α) (cs : List (RoseTree α))
    (g : List ℕ → List (RoseTree α)) :
    graftForest (c :: cs) g =
      graft c (fun q ↦ g (0 :: q)) :: graftForest cs fun p ↦ g (p.modifyHead (· + 1)) := rfl

/-- Grafting onto a forest grafts onto each of its trees. -/
theorem graftForest_eq_mapIdx (cs : List (RoseTree α)) (g : List ℕ → List (RoseTree α)) :
    graftForest cs g = cs.mapIdx fun i c ↦ graft c fun q ↦ g (i :: q) := by
  induction cs generalizing g with
  | nil => rfl
  | cons c cs ih => rw [graftForest_cons, ih, List.mapIdx_cons]; rfl

@[simp] theorem length_graftForest (cs : List (RoseTree α)) (g : List ℕ → List (RoseTree α)) :
    (graftForest cs g).length = cs.length := by
  rw [graftForest_eq_mapIdx, List.length_mapIdx]

@[simp] theorem value_graft (T : RoseTree α) (g : List ℕ → List (RoseTree α)) :
    (graft T g).value = T.value := by
  cases T; rfl

mutual
/-- Grafting nothing leaves a tree unchanged. -/
@[simp] theorem graft_nil : ∀ T : RoseTree α, graft T (fun _ ↦ []) = T
  | node a cs => by rw [graft_node, List.nil_append, graftForest_nil_right cs]
@[simp] theorem graftForest_nil_right : ∀ cs : List (RoseTree α),
    graftForest cs (fun _ ↦ []) = cs
  | [] => rfl
  | c :: cs => by rw [graftForest_cons, graft_nil c, graftForest_nil_right cs]
end

mutual
/-- `graft T g` depends only on the values of `g` at the vertices of `T`. -/
theorem graft_congr : ∀ {T : RoseTree α} {g g' : List ℕ → List (RoseTree α)},
    (∀ p ∈ vertices T, g p = g' p) → graft T g = graft T g'
  | node a cs, g, g', h => by
    rw [graft_node, graft_node, h [] List.mem_cons_self,
      graftForest_congr fun p hp ↦ h p (List.mem_cons_of_mem _ hp)]
theorem graftForest_congr : ∀ {cs : List (RoseTree α)} {g g' : List ℕ → List (RoseTree α)},
    (∀ p ∈ verticesList cs, g p = g' p) → graftForest cs g = graftForest cs g'
  | [], _, _, _ => rfl
  | c :: cs, g, g', h => by
    rw [graftForest_cons, graftForest_cons,
      graft_congr fun q hq ↦ h (0 :: q) (List.mem_append_left _ (List.mem_map_of_mem hq)),
      graftForest_congr fun p hp ↦ h _ (List.mem_append_right _ (List.mem_map_of_mem hp))]
end

mutual
/-- Relabelling a grafted tree is grafting the relabelled trees onto the relabelled tree. -/
theorem map_graft (f : α → β) : ∀ (T : RoseTree α) (g : List ℕ → List (RoseTree α)),
    (graft T g).map f = graft (T.map f) fun p ↦ (g p).map (map f)
  | node a cs, g => by
    rw [graft_node, map_node, map_node, graft_node, List.map_append, map_graftForest f cs]
theorem map_graftForest (f : α → β) : ∀ (cs : List (RoseTree α))
    (g : List ℕ → List (RoseTree α)),
    (graftForest cs g).map (map f) = graftForest (cs.map (map f)) fun p ↦ (g p).map (map f)
  | [], _ => rfl
  | c :: cs, g => by
    rw [graftForest_cons, List.map_cons, List.map_cons, graftForest_cons, map_graft f c,
      map_graftForest f cs]
end

mutual
/-- A grafted tree has the vertices of the tree and those of the trees grafted at its vertices. -/
theorem numNodes_graft : ∀ (T : RoseTree α) (g : List ℕ → List (RoseTree α)),
    (graft T g).numNodes =
      T.numNodes + ((vertices T).map fun p ↦ ((g p).map numNodes).sum).sum
  | node a cs, g => by
    rw [graft_node, numNodes_node, numNodes_node, List.map_append, List.sum_append,
      sum_map_numNodes_graftForest cs, vertices_node, List.map_cons, List.sum_cons]
    omega
theorem sum_map_numNodes_graftForest : ∀ (cs : List (RoseTree α))
    (g : List ℕ → List (RoseTree α)),
    ((graftForest cs g).map numNodes).sum =
      (cs.map numNodes).sum + ((verticesList cs).map fun p ↦ ((g p).map numNodes).sum).sum
  | [], _ => rfl
  | c :: cs, g => by
    rw [graftForest_cons, List.map_cons, List.sum_cons, numNodes_graft c,
      sum_map_numNodes_graftForest cs, verticesList_cons, List.map_append, List.sum_append,
      List.map_map, List.map_map, List.map_cons, List.sum_cons]
    simp only [Function.comp_def]
    omega
end

/-- Grafting a leaf at the root and another at the first child. -/
example : graft (node 0 [leaf 1]) (fun p ↦ if p = [] then [leaf 2] else if p = [0] then [leaf 3]
    else []) = node 0 [leaf 2, node 1 [leaf 3]] := by
  decide

/-- An address outside the tree is ignored. -/
example : graft (leaf 0) (Function.update (fun _ ↦ []) [0] [leaf 1]) = leaf 0 :=
  (graft_congr fun p hp ↦ by simp_all).trans (graft_nil _)

end RoseTree
