/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Linglib.Core.Order.TreePath
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Nodup

/-!
# Rose trees under Gorn addresses

A **Gorn address** is a `List ℕ` path of child indices from the root, and `subtreeAt` navigates a
rose tree by one. The addresses inside a tree are its positions (`validPaths`), a prefix-closed set
of `TreePath`s, and the subtrees are the trees reached by descending through children
(`IsSubtree`). Navigation recurses on the address, not on the tree. This file also shows that
relabelling commutes with navigation, that a subtree is no larger than its tree and that a tree of
height above `k` descends `k` steps. It defines `vertices`, which enumerates the addresses, and
`replaceAt`, which replaces the subtree at an address.

Unlike `BinaryTree.get` (indexed by a `PosNum` left/right path) there is no `indexOf`: that is
a binary-search-tree lookup, which has no analogue for a general rose tree.

## Main declarations

* `RoseTree.subtreeAt`, `RoseTree.validPaths`: the subtree at an address, and the addresses
  inside a tree, prefix-closed (`validPaths_prefix_closed`).
* `RoseTree.IsSubtree`: the subtree relation, the subtrees being the values of `subtreeAt`
  (`isSubtree_iff_exists_subtreeAt`). It is a partial order (`IsSubtree.antisymm`).
* `RoseTree.subtrees`: the subtrees in preorder, exactly those of `IsSubtree` (`mem_subtrees`),
  which decides it.
* `RoseTree.subtreeAt_map`: relabelling commutes with navigation.
* `RoseTree.exists_subtreeAt_height_sub`: a maximal descent from a tree of height above `k`.
* `RoseTree.numNodes_le_of_subtreeAt`: a subtree is no larger than its tree.
* `RoseTree.vertices`: the addresses in preorder, one per vertex (`length_vertices`,
  `nodup_vertices`) and exactly those inside the tree (`mem_vertices`);
  `RoseTree.positionedSubtrees` pairs each with its subtree (`mem_positionedSubtrees`).
* `RoseTree.positionedLeaves`: the leaves with their addresses, exactly the leaf addresses
  (`subtreeAt_of_mem_positionedLeaves`, `mem_positionedLeaves_of_subtreeAt`) in the order of the
  frontier (`map_snd_positionedLeaves`), which is precedence (`pairwise_precedes_positionedLeaves`).
* `RoseTree.replaceAt`: replacement at an address, leaving the subtrees away from it unchanged
  (`subtreeAt_replaceAt_of_not_prefix`) and those above it holding the replacement
  (`subtreeAt_replaceAt_of_prefix`) and shrinking the tree when the new subtree is smaller
  (`numNodes_replaceAt_lt`). Its effect on the frontier is in `RoseTree/Span.lean`.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*}

/-! ### Navigation by address -/

/-- The subtree at a Gorn address, `none` if the address leaves the tree. -/
def subtreeAt (t : RoseTree α) : List ℕ → Option (RoseTree α)
  | [] => some t
  | i :: rest => t.children[i]?.bind fun c ↦ c.subtreeAt rest

@[simp] theorem subtreeAt_nil (t : RoseTree α) : t.subtreeAt [] = some t := rfl

@[simp] theorem subtreeAt_cons (t : RoseTree α) (i : ℕ) (rest : List ℕ) :
    t.subtreeAt (i :: rest) = t.children[i]?.bind fun c ↦ c.subtreeAt rest := rfl

/-- Descending along `p ++ q` is descending along `p`, then along `q` from there. -/
theorem subtreeAt_append (t : RoseTree α) (p q : List ℕ) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).bind (·.subtreeAt q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    rw [List.cons_append, subtreeAt_cons, subtreeAt_cons]
    rcases t.children[i]? with _ | c
    · rfl
    · exact ih c

theorem subtreeAt_cons_eq_some_iff {t s : RoseTree α} {i : ℕ} {p : List ℕ} :
    t.subtreeAt (i :: p) = some s ↔ ∃ c, t.children[i]? = some c ∧ c.subtreeAt p = some s := by
  simp [Option.bind_eq_some_iff]

/-- Every prefix of an address inside the tree is inside the tree. -/
theorem subtreeAt_take_isSome {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s)
    (k : ℕ) : (t.subtreeAt (p.take k)).isSome := by
  rw [← List.take_append_drop k p, subtreeAt_append] at h
  exact Option.isSome_of_isSome_bind (by rw [h]; rfl)

/-- Relabelling commutes with subtree access. -/
theorem subtreeAt_map {β : Type*} (f : α → β) (t : RoseTree α) (p : List ℕ) :
    (map f t).subtreeAt p = (t.subtreeAt p).map (map f) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨a, cs⟩ := t
    simp only [map_node, subtreeAt_cons, children_node, List.getElem?_map]
    cases cs[i]? with
    | none => rfl
    | some c => exact ih c

/-! ### Positions -/

/-- The positions of `t` are the addresses inside it. Node identity is the position, never the
subtree, since identical subtrees occur at several positions, so orders and graphs live on
positions. -/
def validPaths (t : RoseTree α) : Set TreePath := {p | (t.subtreeAt p.toList).isSome}

instance (t : RoseTree α) : DecidablePred (· ∈ t.validPaths) :=
  fun p ↦ inferInstanceAs (Decidable ((t.subtreeAt p.toList).isSome = true))

theorem bot_mem_validPaths (t : RoseTree α) : (⊥ : TreePath) ∈ t.validPaths := by
  simp [validPaths]

/-- A non-root position descends to one child and is a position there. -/
theorem mem_validPaths_cons {t : RoseTree α} {i : ℕ} {rest : List ℕ} :
    (⟨i :: rest⟩ : TreePath) ∈ t.validPaths ↔
      ∃ c, t.children[i]? = some c ∧ (⟨rest⟩ : TreePath) ∈ c.validPaths := by
  simp only [validPaths, Set.mem_ofPred_eq, subtreeAt_cons]
  rcases t.children[i]? with _ | c <;> simp

/-- Positions are closed under prefixes, so they inherit the rooted-tree order of `TreePath`. -/
theorem validPaths_prefix_closed {t : RoseTree α} {p q : TreePath} (hq : q ∈ t.validPaths)
    (hpq : p ≤ q) : p ∈ t.validPaths := by
  obtain ⟨s, hs⟩ := hpq
  simp only [validPaths, Set.mem_ofPred_eq] at hq ⊢
  rw [← hs, subtreeAt_append] at hq
  exact Option.isSome_of_isSome_bind hq

theorem isLowerSet_validPaths (t : RoseTree α) : IsLowerSet t.validPaths :=
  fun _ _ hpq hq ↦ validPaths_prefix_closed hq hpq

/-- The daughters of a position are its extensions by an index below the arity of its
subtree. -/
theorem mem_validPaths_append_singleton_iff {t : RoseTree α} {p : List ℕ} {i : ℕ} :
    (⟨p ++ [i]⟩ : TreePath) ∈ t.validPaths ↔
      ∃ s, t.subtreeAt p = some s ∧ i < s.children.length := by
  simp only [validPaths, Set.mem_ofPred_eq, subtreeAt_append, subtreeAt_cons, subtreeAt_nil]
  cases t.subtreeAt p with
  | none => simp
  | some s => simp

/-! ### Height and size along addresses -/

/-- A node of height above `1` has a child one shorter. -/
theorem exists_mem_children_height_add_one {t : RoseTree α} (h : 1 < t.height) :
    ∃ c ∈ t.children, c.height + 1 = t.height := by
  cases t with
  | node a cs =>
    rw [height_node] at h ⊢
    have hcs : cs ≠ [] := by rintro rfl; simp at h
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp (List.maximum_mem
      (List.foldr_max_of_ne_nil (l := cs.map height) (by simpa using hcs)).symm)
    exact ⟨c, hc, by rw [hce]; rfl⟩

/-- A tree of height above `k` has a maximal descent of length `k`, along which the subtree at
the prefix of length `i` has height `t.height - i`. -/
theorem exists_subtreeAt_height_sub (t : RoseTree α) (k : ℕ) (hk : k < t.height) :
    ∃ p : List ℕ, p.length = k ∧
      ∀ i ≤ k, ∃ s, subtreeAt t (p.take i) = some s ∧ s.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    exact ⟨[], rfl, fun i hi ↦ by obtain rfl := Nat.le_zero.mp hi; exact ⟨t, rfl, by simp⟩⟩
  | succ k ih =>
    obtain ⟨c, hc, hch⟩ := exists_mem_children_height_add_one
      (Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le k)) hk)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨p, hp, hsub⟩ := ih c (by omega)
    refine ⟨j :: p, by simp [hp], fun i hi ↦ ?_⟩
    cases i with
    | zero => exact ⟨t, rfl, by simp⟩
    | succ i =>
      obtain ⟨s, hs, hsh⟩ := hsub i (Nat.le_of_succ_le_succ hi)
      exact ⟨s, by simp only [List.take_succ_cons, subtreeAt_cons, hj,
        Option.bind_some, hs], by omega⟩

theorem numNodes_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.numNodes < t.numNodes := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [numNodes_node]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := numNodes) h)
    omega

theorem numNodes_le_of_subtreeAt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s) :
    s.numNodes ≤ t.numNodes := by
  induction p generalizing t with
  | nil => exact (Option.some.inj h).symm ▸ Nat.le_refl _
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    exact Nat.le_trans (ih hcs) (Nat.le_of_lt (numNodes_lt_of_mem (List.mem_of_getElem? hc)))

theorem numNodes_lt_of_subtreeAt_cons {t s : RoseTree α} {i : ℕ} {p : List ℕ}
    (h : subtreeAt t (i :: p) = some s) : s.numNodes < t.numNodes := by
  obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
  exact Nat.lt_of_le_of_lt (numNodes_le_of_subtreeAt hcs)
    (numNodes_lt_of_mem (List.mem_of_getElem? hc))

/-! ### Subtrees -/

/-- `IsSubtree s t` holds when `s` is the subtree of `t` rooted at one of its nodes, reached from
`t` by descending through children. -/
def IsSubtree (s t : RoseTree α) : Prop := Relation.ReflTransGen (fun c u ↦ c ∈ u.children) s t

@[refl]
theorem IsSubtree.refl (t : RoseTree α) : IsSubtree t t := Relation.ReflTransGen.refl

theorem IsSubtree.trans {r s t : RoseTree α} (h₁ : IsSubtree r s) (h₂ : IsSubtree s t) :
    IsSubtree r t :=
  Relation.ReflTransGen.trans h₁ h₂

instance : @Trans (RoseTree α) (RoseTree α) (RoseTree α) IsSubtree IsSubtree IsSubtree :=
  ⟨IsSubtree.trans⟩

theorem IsSubtree.of_mem_children {c t : RoseTree α} (h : c ∈ t.children) : IsSubtree c t :=
  Relation.ReflTransGen.single h

/-- The subtrees of `t` are exactly the values of `subtreeAt t` at addresses inside `t`. -/
theorem isSubtree_iff_exists_subtreeAt {s t : RoseTree α} :
    IsSubtree s t ↔ ∃ p, t.subtreeAt p = some s := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hc _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
      exact ⟨p ++ [i], by simp [subtreeAt_append, hp, hi]⟩
  · rintro ⟨p, hp⟩
    induction p generalizing t with
    | nil => cases hp; exact .refl _
    | cons i p ih =>
      obtain ⟨c, hc, hp⟩ := subtreeAt_cons_eq_some_iff.1 hp
      exact (ih hp).tail (List.mem_of_getElem? hc)

theorem isSubtree_node_iff {s : RoseTree α} {a : α} {cs : List (RoseTree α)} :
    IsSubtree s (node a cs) ↔ s = node a cs ∨ ∃ c ∈ cs, IsSubtree s c := by
  rw [IsSubtree, Relation.ReflTransGen.cases_tail_iff]
  simp only [children_node, eq_comm (a := node a cs)]
  exact or_congr_right ⟨fun ⟨c, h, hc⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, h, hc⟩⟩

@[simp] theorem isSubtree_leaf_iff {s : RoseTree α} {a : α} :
    IsSubtree s (leaf a) ↔ s = leaf a := by
  simp [isSubtree_node_iff]

/-- A subtree is no larger than its tree. -/
theorem IsSubtree.numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) : s.numNodes ≤ t.numNodes :=
  let ⟨_, hp⟩ := isSubtree_iff_exists_subtreeAt.1 h; numNodes_le_of_subtreeAt hp

/-- A subtree as large as its tree is the tree. -/
theorem IsSubtree.eq_of_numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) (hn : t.numNodes ≤ s.numNodes) : s = t := by
  obtain ⟨_ | ⟨i, p⟩, hp⟩ := isSubtree_iff_exists_subtreeAt.1 h
  · exact (Option.some.inj hp).symm
  · exact absurd hn (not_le.2 (numNodes_lt_of_subtreeAt_cons hp))

theorem IsSubtree.antisymm {s t : RoseTree α}
    (h₁ : IsSubtree s t) (h₂ : IsSubtree t s) : s = t :=
  h₁.eq_of_numNodes_le h₂.numNodes_le

mutual
/-- `subtrees t` lists the subtrees of `t` in preorder, `t` first, one per vertex. -/
def subtrees : RoseTree α → List (RoseTree α)
  | t@(node _ cs) => t :: subtreesList cs
/-- `subtreesList cs` lists the subtrees of the trees of `cs`. -/
def subtreesList : List (RoseTree α) → List (RoseTree α)
  | [] => []
  | c :: cs => subtrees c ++ subtreesList cs
end

theorem subtreesList_eq (cs : List (RoseTree α)) : subtreesList cs = cs.flatMap subtrees := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [subtreesList, ih, List.flatMap_cons]

@[simp] theorem subtrees_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).subtrees = node a cs :: cs.flatMap subtrees := by
  rw [subtrees, subtreesList_eq]

/-- The listed subtrees are exactly the subtrees. -/
theorem mem_subtrees {s t : RoseTree α} : s ∈ t.subtrees ↔ IsSubtree s t := by
  induction t with
  | node a cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap, isSubtree_node_iff]
    exact or_congr_right (exists_congr fun c ↦ and_congr_right fun hc ↦ ih c hc)

theorem self_mem_subtrees (t : RoseTree α) : t ∈ t.subtrees := mem_subtrees.mpr (.refl t)

instance [DecidableEq α] (s t : RoseTree α) : Decidable (IsSubtree s t) :=
  decidable_of_iff _ mem_subtrees

/-! ### Enumerating the addresses -/

mutual
/-- `vertices t` lists the addresses of the vertices of `t` in preorder, the root `[]` first. -/
def vertices : RoseTree α → List (List ℕ)
  | node _ cs => [] :: verticesList cs
/-- `verticesList cs` lists the addresses of the vertices of the forest `cs`, each starting with
the index of its tree. -/
def verticesList : List (RoseTree α) → List (List ℕ)
  | [] => []
  | c :: cs => (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1))
end

@[simp] theorem vertices_node (a : α) (cs : List (RoseTree α)) :
    vertices (node a cs) = [] :: verticesList cs := rfl

@[simp] theorem verticesList_nil : verticesList ([] : List (RoseTree α)) = [] := rfl

@[simp] theorem verticesList_cons (c : RoseTree α) (cs : List (RoseTree α)) :
    verticesList (c :: cs) =
      (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1)) := rfl

theorem mem_verticesList {cs : List (RoseTree α)} {p : List ℕ} :
    p ∈ verticesList cs ↔ ∃ j q c, p = j :: q ∧ cs[j]? = some c ∧ q ∈ vertices c := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih =>
    rw [verticesList_cons, List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨q, hq, rfl⟩ | ⟨p', hp', rfl⟩)
      · exact ⟨0, q, c, rfl, rfl, hq⟩
      · obtain ⟨j, q, d, rfl, hd, hq⟩ := ih.mp hp'
        exact ⟨j + 1, q, d, rfl, hd, hq⟩
    · rintro ⟨_ | j, q, d, rfl, hd, hq⟩
      · exact .inl ⟨q, Option.some.inj hd ▸ hq, rfl⟩
      · exact .inr ⟨j :: q, ih.mpr ⟨j, q, d, rfl, hd, hq⟩, rfl⟩

theorem exists_cons_of_mem_verticesList {cs : List (RoseTree α)} {p : List ℕ}
    (hp : p ∈ verticesList cs) : ∃ j q, p = j :: q := by
  obtain ⟨j, q, -, rfl, -⟩ := mem_verticesList.mp hp
  exact ⟨j, q, rfl⟩

/-- The addresses listed by `vertices t` are exactly the addresses inside `t`. -/
theorem mem_vertices {t : RoseTree α} {p : List ℕ} :
    p ∈ t.vertices ↔ (subtreeAt t p).isSome := by
  induction t generalizing p with
  | node a cs ih =>
    rcases p with _ | ⟨j, q⟩
    · simp
    · simp only [vertices_node, List.mem_cons, reduceCtorEq, false_or, mem_verticesList,
        List.cons.injEq, subtreeAt_cons, children_node]
      constructor
      · rintro ⟨_, _, c, ⟨rfl, rfl⟩, hc, hq⟩
        rw [hc, Option.bind_some]
        exact (ih c (List.mem_of_getElem? hc)).mp hq
      · intro h
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
        rw [hc, Option.bind_some] at h
        exact ⟨j, q, c, ⟨rfl, rfl⟩, hc, (ih c (List.mem_of_getElem? hc)).mpr h⟩

mutual
theorem length_vertices : ∀ t : RoseTree α, t.vertices.length = t.numNodes
  | node _ cs => by rw [vertices_node, List.length_cons, length_verticesList cs, numNodes_node]
theorem length_verticesList : ∀ cs : List (RoseTree α),
    (verticesList cs).length = (cs.map numNodes).sum
  | [] => rfl
  | c :: cs => by
    rw [verticesList_cons, List.length_append, List.length_map, List.length_map,
      length_vertices c, length_verticesList cs, List.map_cons, List.sum_cons]
end

private theorem modifyHead_succ_injective : Function.Injective (List.modifyHead (· + 1)) := by
  rintro (_ | ⟨a, l⟩) (_ | ⟨b, m⟩) h <;> simp_all

mutual
theorem nodup_vertices : ∀ t : RoseTree α, t.vertices.Nodup
  | node _ cs => by
    rw [vertices_node, List.nodup_cons]
    refine ⟨fun h ↦ ?_, nodup_verticesList cs⟩
    obtain ⟨_, _, h⟩ := exists_cons_of_mem_verticesList h
    exact List.cons_ne_nil _ _ h.symm
theorem nodup_verticesList : ∀ cs : List (RoseTree α), (verticesList cs).Nodup
  | [] => List.nodup_nil
  | c :: cs => by
    rw [verticesList_cons, List.nodup_append]
    refine ⟨List.Nodup.map List.cons_injective (nodup_vertices c),
      List.Nodup.map modifyHead_succ_injective (nodup_verticesList cs), ?_⟩
    rintro _ hp _ hq rfl
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    obtain ⟨p', hp', h⟩ := List.mem_map.mp hq
    obtain ⟨j, q', rfl⟩ := exists_cons_of_mem_verticesList hp'
    simp at h
end

/-- The subtrees of `t` with their positions, in preorder. -/
def positionedSubtrees (t : RoseTree α) : List (TreePath × RoseTree α) :=
  t.vertices.filterMap fun p ↦ (t.subtreeAt p).map (⟨p⟩, ·)

theorem mem_positionedSubtrees {t s : RoseTree α} {p : TreePath} :
    (p, s) ∈ t.positionedSubtrees ↔ t.subtreeAt p.toList = some s := by
  simp only [positionedSubtrees, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  refine ⟨fun ⟨_, _, _, hs, rfl, rfl⟩ ↦ hs, fun hs ↦ ?_⟩
  exact ⟨p.toList, mem_vertices.mpr (by rw [hs]; rfl), s, hs, rfl, rfl⟩

theorem nodup_map_fst_positionedSubtrees (t : RoseTree α) :
    (t.positionedSubtrees.map Prod.fst).Nodup := by
  rw [positionedSubtrees, List.map_filterMap]
  refine (nodup_vertices t).filterMap fun p q r hp hq ↦ ?_
  simp only [Option.map_map, Function.comp_def, Option.mem_def, Option.map_eq_some_iff] at hp hq
  obtain ⟨-, -, rfl⟩ := hp
  obtain ⟨-, -, h⟩ := hq
  exact congrArg TreePath.toList h.symm

/-! ### The leaves with their addresses -/

/-- `positionedLeaves t` lists the leaves of `t` from left to right, each with its address. -/
def positionedLeaves : RoseTree α → List (TreePath × α) :=
  fold fun a ps ↦ match ps with
    | [] => [(⊥, a)]
    | ps => ps.zipIdx.flatMap fun (qs, i) ↦ qs.map fun x ↦ (⟨i :: x.1.toList⟩, x.2)

@[simp] theorem positionedLeaves_leaf (a : α) : positionedLeaves (node a []) = [(⊥, a)] := by
  simp only [positionedLeaves, fold_node, List.map_nil]

theorem positionedLeaves_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    positionedLeaves (node a cs) = cs.zipIdx.flatMap fun (c, i) ↦
      c.positionedLeaves.map fun x ↦ (⟨i :: x.1.toList⟩, x.2) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [positionedLeaves, fold_node, List.map_cons]
  simp only [← List.map_cons, List.zipIdx_map, List.flatMap_map]
  rfl

private theorem fst_mem_of_mem_zipIdx {l : List (RoseTree α)} {x : RoseTree α × ℕ}
    (h : x ∈ l.zipIdx) : x.1 ∈ l := by
  rw [List.fst_eq_of_mem_zipIdx h]
  exact List.getElem_mem _

private theorem pairwise_snd_lt_zipIdx :
    ∀ (l : List (RoseTree α)) (k : ℕ), (l.zipIdx k).Pairwise fun a b ↦ a.2 < b.2
  | [], _ => .nil
  | _ :: l, k => List.pairwise_cons.mpr
    ⟨fun _ hb ↦ List.le_snd_of_mem_zipIdx hb, pairwise_snd_lt_zipIdx l (k + 1)⟩

/-- Forgetting the addresses leaves the frontier. -/
theorem map_snd_positionedLeaves (t : RoseTree α) :
    t.positionedLeaves.map Prod.snd = t.leafList := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    rw [positionedLeaves_node_of_ne_nil a hcs, leafList_node_of_ne_nil a hcs, List.map_flatMap]
    conv_rhs => rw [← List.zipIdx_map_fst 0 cs, List.map_map, ← List.flatMap_def]
    refine List.flatMap_congr fun x hx ↦ ?_
    rw [List.map_map, Function.comp_apply, ← ih x.1 (fst_mem_of_mem_zipIdx hx)]
    rfl

/-- Each listed address holds its leaf. -/
theorem subtreeAt_of_mem_positionedLeaves {t : RoseTree α} {x : TreePath × α}
    (h : x ∈ t.positionedLeaves) : subtreeAt t x.1.toList = some (node x.2 []) := by
  induction t generalizing x with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · obtain rfl := List.mem_singleton.mp (by simpa using h)
      rfl
    simp only [positionedLeaves_node_of_ne_nil a hcs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨c, i⟩, hc, y, hy, rfl⟩ := h
    simp [List.mem_zipIdx_iff_getElem?.mp hc, ih c (fst_mem_of_mem_zipIdx hc) hy]

/-- Every leaf address is listed. -/
theorem mem_positionedLeaves_of_subtreeAt {t : RoseTree α} {p : List ℕ} {a : α}
    (h : subtreeAt t p = some (node a [])) : (⟨p⟩, a) ∈ t.positionedLeaves := by
  induction t generalizing p with
  | node b cs ih =>
    rcases p with _ | ⟨i, p⟩
    · cases h
      exact List.mem_singleton.mpr rfl
    simp only [subtreeAt_cons, children_node, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    rw [positionedLeaves_node_of_ne_nil b (List.ne_nil_of_mem (List.mem_of_getElem? hc))]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨(c, i), List.mem_zipIdx_iff_getElem?.mpr hc, _, ih c (List.mem_of_getElem? hc) h, rfl⟩

/-- The leaf addresses, in the order of the frontier, ascend in precedence. -/
theorem pairwise_precedes_positionedLeaves (t : RoseTree α) :
    t.positionedLeaves.Pairwise fun x y ↦ x.1.Precedes y.1 := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    rw [positionedLeaves_node_of_ne_nil a hcs, List.pairwise_flatMap]
    refine ⟨fun ⟨c, i⟩ hc ↦ ?_, (pairwise_snd_lt_zipIdx cs 0).imp fun hij x hx y hy ↦ ?_⟩
    · rw [List.pairwise_map]
      exact (ih c (fst_mem_of_mem_zipIdx hc)).imp fun h ↦ h.cons i
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hy
      exact TreePath.precedes_cons_of_lt hij _ _

/-! ### Replacement at an address -/

/-- Replace the subtree at a Gorn address; an address outside the tree leaves it unchanged. -/
def replaceAt : RoseTree α → List ℕ → RoseTree α → RoseTree α
  | _, [], new => new
  | node a cs, i :: p, new => node a (cs.modify i (·.replaceAt p new))

@[simp] theorem replaceAt_nil (t new : RoseTree α) : t.replaceAt [] new = new := by
  cases t; rfl

theorem replaceAt_cons (a : α) (cs : List (RoseTree α)) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (node a cs).replaceAt (i :: p) new = node a (cs.modify i (·.replaceAt p new)) := rfl

/-- Replacing below the root replaces inside one child. -/
@[simp] theorem children_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (t.replaceAt (i :: p) new).children = t.children.modify i (·.replaceAt p new) := by
  cases t; rfl

@[simp] theorem value_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ) (new : RoseTree α) :
    (t.replaceAt (i :: p) new).value = t.value := by
  cases t; rfl

/-- Replacing a subtree by one with the same root value keeps the root value. -/
theorem value_replaceAt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s)
    {new : RoseTree α} (hv : new.value = s.value) : (t.replaceAt p new).value = t.value := by
  cases p with
  | nil => rw [replaceAt_nil, hv, Option.some.inj h]
  | cons i p => exact value_replaceAt_cons t i p new

theorem replaceAt_cons_of_getElem? {t c : RoseTree α} {i : ℕ} (hc : t.children[i]? = some c)
    (p : List ℕ) (new : RoseTree α) :
    t.replaceAt (i :: p) new = node t.value (t.children.set i (c.replaceAt p new)) := by
  cases t with
  | node a cs =>
    have : Inhabited (RoseTree α) := ⟨c⟩
    rw [children_node] at hc
    rw [replaceAt_cons, List.modify_eq_set, hc, Option.getD_some, value_node, children_node]

private theorem eq_take_append_cons_drop {cs : List (RoseTree α)} {i : ℕ} {c : RoseTree α}
    (hc : cs[i]? = some c) : cs = cs.take i ++ c :: cs.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

private theorem set_eq_take_append_cons_drop {cs : List (RoseTree α)} {i : ℕ} {c : RoseTree α}
    (hc : cs[i]? = some c) (x : RoseTree α) : cs.set i x = cs.take i ++ x :: cs.drop (i + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left (List.getElem?_eq_some_iff.mp hc).1]

/-- Away from the replaced address, at an address neither above nor below it, the subtree is
unchanged. -/
theorem subtreeAt_replaceAt_of_not_prefix {t new : RoseTree α} {p q : List ℕ} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : (t.replaceAt p new).subtreeAt q = t.subtreeAt q := by
  induction p generalizing t q with
  | nil => exact absurd List.nil_prefix hpq
  | cons i p ih =>
    obtain _ | ⟨j, q⟩ := q
    · exact absurd List.nil_prefix hqp
    obtain ⟨a, cs⟩ := t
    obtain rfl | hij := eq_or_ne i j
    · have h (t : RoseTree α) : (t.replaceAt p new).subtreeAt q = t.subtreeAt q :=
        ih (fun h ↦ hpq (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
          (fun h ↦ hqp (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
      cases hc : cs[i]? <;> simp [replaceAt_cons, hc, h]
    · simp [replaceAt_cons, hij]

/-- At an address above the replaced one, the subtree has the replacement inside it. -/
theorem subtreeAt_replaceAt_of_prefix {t new : RoseTree α} {p q : List ℕ} (hqp : q <+: p) :
    (t.replaceAt p new).subtreeAt q = (t.subtreeAt q).map (·.replaceAt (p.drop q.length) new) := by
  induction q generalizing t p with
  | nil => simp
  | cons j q ih =>
    obtain _ | ⟨i, p⟩ := p
    · exact absurd hqp (by simp)
    obtain ⟨rfl, h⟩ := List.cons_prefix_cons.mp hqp
    obtain ⟨a, cs⟩ := t
    cases hc : cs[j]? <;> simp [replaceAt_cons, hc, ih h]

/-- At an address below the replaced one, the subtree is that of the replacement. -/
theorem subtreeAt_replaceAt_append {t new : RoseTree α} {p : List ℕ} (hp : (t.subtreeAt p).isSome)
    (q : List ℕ) : (t.replaceAt p new).subtreeAt (p ++ q) = new.subtreeAt q := by
  rw [subtreeAt_append, subtreeAt_replaceAt_of_prefix (List.prefix_refl p)]
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
  simp [hs]

/-- Replacing a subtree by a strictly smaller one shrinks the tree. -/
theorem numNodes_replaceAt_lt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s)
    {new : RoseTree α} (hlt : new.numNodes < s.numNodes) :
    (t.replaceAt p new).numNodes < t.numNodes := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil, Option.some.inj h]; exact hlt
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    cases t with
    | node a cs =>
      rw [children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node,
        set_eq_take_append_cons_drop hc, numNodes_node]
      conv_rhs => rw [eq_take_append_cons_drop hc, numNodes_node]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      have := ih hcs
      omega

end RoseTree
