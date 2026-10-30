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

A Gorn address is the list of child indices on the way down from the root, and a rose tree is
indexed by addresses: `t[p]?` is the subtree reached by following `p` down from the root, and an
address given as a `TreePath` is read through its list. The addresses inside
a tree are its positions (`RoseTree.validPaths`), a prefix-closed set of `TreePath`s. The trees
found at them are its subtrees (`RoseTree.IsSubtree`), which `RoseTree.subtrees` lists in preorder.
`RoseTree.vertices` lists the addresses themselves in preorder, which is lexicographic order, and
`RoseTree.positionedLeaves` lists the leaf addresses in the order of the frontier, which is
precedence. `RoseTree.replaceAt` replaces the subtree at an address; its effect on the frontier is
in `RoseTree/Span.lean`.

## Main definitions

* `RoseTree.subtreeAt`: the subtree at an address, written `t[p]?`.
* `RoseTree.validPaths`: the addresses inside a tree.
* `RoseTree.IsSubtree`: the subtree relation.
* `RoseTree.vertices`: the addresses in preorder.
* `RoseTree.replaceAt`: replacement at an address.

## Main statements

* `RoseTree.isSubtree_iff_exists_getElem?`: the subtrees are the trees found at addresses.
* `RoseTree.mem_vertices`: `vertices` lists exactly the addresses inside the tree.
* `RoseTree.pairwise_lt_vertices`: the addresses in preorder increase lexicographically.
* `RoseTree.pairwise_precedes_positionedLeaves`: the leaf addresses ascend in precedence.
* `RoseTree.numNodes_replaceAt`: replacement trades the nodes of the old subtree for the new.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*}

/-! ### Navigation by address -/

/-- The subtree at a Gorn address, `none` if the address leaves the tree. It is written `t[p]?`. -/
def subtreeAt (t : RoseTree α) : List ℕ → Option (RoseTree α)
  | [] => some t
  | i :: rest => t.children[i]?.bind fun c ↦ c.subtreeAt rest

/-- The positions of `t` are the addresses inside it. Node identity is the position, never the
subtree, since identical subtrees occur at several positions, so orders and graphs live on
positions. -/
def validPaths (t : RoseTree α) : Set TreePath := {p | (t.subtreeAt p.toList).isSome}

instance (t : RoseTree α) : DecidablePred (· ∈ t.validPaths) :=
  fun p ↦ inferInstanceAs (Decidable ((t.subtreeAt p.toList).isSome = true))

/-- A tree is indexed by Gorn addresses: `t[p]?` is the subtree at `p`, and `t[p]` the subtree at
an address inside `t`. -/
instance : GetElem? (RoseTree α) (List ℕ) (RoseTree α) fun t p ↦ ⟨p⟩ ∈ t.validPaths where
  getElem t p h := (t.subtreeAt p).get h
  getElem? t p := t.subtreeAt p

instance : LawfulGetElem (RoseTree α) (List ℕ) (RoseTree α) fun t p ↦ ⟨p⟩ ∈ t.validPaths where
  getElem?_def t p _ := by
    change t.subtreeAt p = _
    split_ifs with h
    · exact (Option.some_get h).symm
    · exact Option.not_isSome_iff_eq_none.mp h

/-- A tree is indexed by positions, through their addresses. -/
instance : GetElem? (RoseTree α) TreePath (RoseTree α) fun t p ↦ p ∈ t.validPaths where
  getElem t p h := t[p.toList]'h
  getElem? t p := t[p.toList]?

instance : LawfulGetElem (RoseTree α) TreePath (RoseTree α) fun t p ↦ p ∈ t.validPaths where
  getElem?_def t p _ := getElem?_def t p.toList
  getElem!_def t p := getElem!_def t p.toList

@[simp] theorem getElem?_treePath (t : RoseTree α) (p : TreePath) : t[p]? = t[p.toList]? := rfl

@[simp] theorem getElem_treePath (t : RoseTree α) (p : TreePath) (h : p ∈ t.validPaths) :
    t[p] = t[p.toList]'h := rfl

theorem mem_validPaths_iff_isSome {t : RoseTree α} {p : TreePath} :
    p ∈ t.validPaths ↔ t[p]?.isSome := Iff.rfl

@[simp] theorem getElem?_nil (t : RoseTree α) : t[([] : List ℕ)]? = some t := rfl

@[simp] theorem getElem?_cons (t : RoseTree α) (i : ℕ) (rest : List ℕ) :
    t[i :: rest]? = t.children[i]?.bind (·[rest]?) := rfl

theorem getElem?_append (t : RoseTree α) (p q : List ℕ) :
    t[p ++ q]? = t[p]?.bind (·[q]?) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    rw [List.cons_append, getElem?_cons, getElem?_cons]
    rcases t.children[i]? with _ | c
    · rfl
    · exact ih c

theorem getElem?_cons_eq_some_iff {t s : RoseTree α} {i : ℕ} {p : List ℕ} :
    t[i :: p]? = some s ↔ ∃ c, t.children[i]? = some c ∧ c[p]? = some s := by
  simp [Option.bind_eq_some_iff]

theorem getElem?_take_isSome {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s) (k : ℕ) :
    t[p.take k]?.isSome := by
  rw [← List.take_append_drop k p, getElem?_append] at h
  exact Option.isSome_of_isSome_bind (by rw [h]; rfl)

/-- Relabelling commutes with subtree access. -/
theorem getElem?_map {β : Type*} (f : α → β) (t : RoseTree α) (p : List ℕ) :
    (map f t)[p]? = t[p]?.map (map f) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    obtain ⟨a, cs⟩ := t
    simp only [map_node, getElem?_cons, children_node, List.getElem?_map]
    cases cs[i]? with
    | none => rfl
    | some c => exact ih c

/-! ### Positions -/

@[simp] theorem validPaths_map {β : Type*} (f : α → β) (t : RoseTree α) :
    (map f t).validPaths = t.validPaths := by
  ext p
  simp only [mem_validPaths_iff_isSome, getElem?_treePath, getElem?_map, Option.isSome_map]

theorem bot_mem_validPaths (t : RoseTree α) : (⊥ : TreePath) ∈ t.validPaths := rfl

theorem mem_validPaths_cons {t : RoseTree α} {i : ℕ} {rest : List ℕ} :
    (⟨i :: rest⟩ : TreePath) ∈ t.validPaths ↔
      ∃ c, t.children[i]? = some c ∧ (⟨rest⟩ : TreePath) ∈ c.validPaths := by
  simp only [mem_validPaths_iff_isSome, getElem?_treePath, getElem?_cons]
  rcases t.children[i]? with _ | c <;> simp

/-- Positions are closed under prefixes, so they inherit the rooted-tree order of `TreePath`. -/
theorem validPaths_prefix_closed {t : RoseTree α} {p q : TreePath} (hq : q ∈ t.validPaths)
    (hpq : p ≤ q) : p ∈ t.validPaths := by
  obtain ⟨s, hs⟩ := hpq
  rw [mem_validPaths_iff_isSome, getElem?_treePath, ← hs, getElem?_append] at hq
  exact Option.isSome_of_isSome_bind hq

theorem isLowerSet_validPaths (t : RoseTree α) : IsLowerSet t.validPaths :=
  fun _ _ hpq hq ↦ validPaths_prefix_closed hq hpq

theorem mem_validPaths_append_singleton_iff {t : RoseTree α} {p : List ℕ} {i : ℕ} :
    (⟨p ++ [i]⟩ : TreePath) ∈ t.validPaths ↔ ∃ s, t[p]? = some s ∧ i < s.children.length := by
  simp only [mem_validPaths_iff_isSome, getElem?_treePath, getElem?_append, getElem?_cons,
    getElem?_nil]
  cases t[p]? with
  | none => simp
  | some s => simp

/-! ### Height and size along addresses -/

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
theorem exists_getElem?_height_sub (t : RoseTree α) (k : ℕ) (hk : k < t.height) :
    ∃ p : List ℕ, p.length = k ∧
      ∀ i ≤ k, ∃ s, t[p.take i]? = some s ∧ s.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    exact ⟨[], rfl, fun i hi ↦ by obtain rfl := Nat.le_zero.mp hi; exact ⟨t, rfl, by simp⟩⟩
  | succ k ih =>
    obtain ⟨c, hc, hch⟩ := exists_mem_children_height_add_one (t := t) (by omega)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨p, hp, hsub⟩ := ih c (by omega)
    refine ⟨j :: p, by simp [hp], fun i hi ↦ ?_⟩
    cases i with
    | zero => exact ⟨t, rfl, by simp⟩
    | succ i =>
      obtain ⟨s, hs, hsh⟩ := hsub i (Nat.le_of_succ_le_succ hi)
      exact ⟨s, by simp only [List.take_succ_cons, getElem?_cons, hj,
        Option.bind_some, hs], by omega⟩

theorem numNodes_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.numNodes < t.numNodes := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [numNodes_node]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := numNodes) h)
    omega

theorem numNodes_le_of_getElem? {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s) :
    s.numNodes ≤ t.numNodes := by
  induction p generalizing t with
  | nil => exact (Option.some.inj h).symm ▸ Nat.le_refl _
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    exact Nat.le_trans (ih hcs) (Nat.le_of_lt (numNodes_lt_of_mem (List.mem_of_getElem? hc)))

theorem numNodes_lt_of_getElem?_cons {t s : RoseTree α} {i : ℕ} {p : List ℕ}
    (h : t[i :: p]? = some s) : s.numNodes < t.numNodes := by
  obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
  exact Nat.lt_of_le_of_lt (numNodes_le_of_getElem? hcs)
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

/-- Relabelling preserves the subtree relation. -/
theorem IsSubtree.map {β : Type*} {s t : RoseTree α} (f : α → β) (h : IsSubtree s t) :
    IsSubtree (s.map f) (t.map f) :=
  Relation.ReflTransGen.lift (RoseTree.map f) (fun c ⟨a, cs⟩ hc ↦ by
    simp only [Function.onFun, map_node, children_node]
    exact List.mem_map_of_mem hc) _ _ h

/-- The subtrees of `t` are exactly the trees found at addresses inside `t`. -/
theorem isSubtree_iff_exists_getElem? {s t : RoseTree α} :
    IsSubtree s t ↔ ∃ p : List ℕ, t[p]? = some s := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hc _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
      exact ⟨p ++ [i], by simp [getElem?_append, hp, hi]⟩
  · rintro ⟨p, hp⟩
    induction p generalizing t with
    | nil => cases hp; exact .refl _
    | cons i p ih =>
      obtain ⟨c, hc, hp⟩ := getElem?_cons_eq_some_iff.1 hp
      exact (ih hp).tail (List.mem_of_getElem? hc)

theorem isSubtree_node_iff {s : RoseTree α} {a : α} {cs : List (RoseTree α)} :
    IsSubtree s (node a cs) ↔ s = node a cs ∨ ∃ c ∈ cs, IsSubtree s c := by
  rw [IsSubtree, Relation.ReflTransGen.cases_tail_iff]
  simp only [children_node, eq_comm (a := node a cs)]
  exact or_congr_right ⟨fun ⟨c, h, hc⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, h, hc⟩⟩

@[simp] theorem isSubtree_leaf_iff {s : RoseTree α} {a : α} :
    IsSubtree s (leaf a) ↔ s = leaf a := by
  simp [isSubtree_node_iff]

theorem IsSubtree.numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) : s.numNodes ≤ t.numNodes :=
  let ⟨_, hp⟩ := isSubtree_iff_exists_getElem?.1 h; numNodes_le_of_getElem? hp

theorem IsSubtree.eq_of_numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) (hn : t.numNodes ≤ s.numNodes) : s = t := by
  obtain ⟨_ | ⟨i, p⟩, hp⟩ := isSubtree_iff_exists_getElem?.1 h
  · exact (Option.some.inj hp).symm
  · exact absurd hn (not_le.2 (numNodes_lt_of_getElem?_cons hp))

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

theorem subtrees_map {β : Type*} (f : α → β) (t : RoseTree α) :
    (map f t).subtrees = t.subtrees.map (map f) := by
  induction t with
  | node a cs ih =>
    rw [map_node, subtrees_node, subtrees_node, List.map_cons, ← map_node, List.flatMap_map,
      List.map_flatMap]
    exact congrArg _ (List.flatMap_congr fun c hc ↦ ih c hc)

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
    p ∈ t.vertices ↔ (t[p]?).isSome := by
  induction t generalizing p with
  | node a cs ih =>
    rcases p with _ | ⟨j, q⟩
    · simp
    · simp only [vertices_node, List.mem_cons, reduceCtorEq, false_or, mem_verticesList,
        List.cons.injEq, getElem?_cons, children_node]
      constructor
      · rintro ⟨_, _, c, ⟨rfl, rfl⟩, hc, hq⟩
        rw [hc, Option.bind_some]
        exact (ih c (List.mem_of_getElem? hc)).mp hq
      · intro h
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
        rw [hc, Option.bind_some] at h
        exact ⟨j, q, c, ⟨rfl, rfl⟩, hc, (ih c (List.mem_of_getElem? hc)).mpr h⟩

/-- The subtrees at the listed addresses are the listed subtrees. -/
theorem filterMap_getElem?_vertices (t : RoseTree α) :
    t.vertices.filterMap (t[·]?) = t.subtrees := by
  induction t with
  | node a cs ih =>
    rw [vertices_node, List.filterMap_cons_some (getElem?_nil _), subtrees_node]
    congr 1
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      rw [verticesList_cons, List.filterMap_append, List.filterMap_map, List.filterMap_map,
        List.flatMap_cons, ← ih c List.mem_cons_self,
        ← ihcs fun d hd ↦ ih d (List.mem_cons_of_mem _ hd)]
      congr 1
      refine List.filterMap_congr fun p hp ↦ ?_
      obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hp
      rfl

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

mutual
/-- The addresses in preorder increase lexicographically. -/
theorem pairwise_lt_vertices : ∀ t : RoseTree α, t.vertices.Pairwise (· < ·)
  | node _ cs => by
    rw [vertices_node, List.pairwise_cons]
    refine ⟨fun p hp ↦ ?_, pairwise_lt_verticesList cs⟩
    obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hp
    exact List.nil_lt_cons _ _
theorem pairwise_lt_verticesList : ∀ cs : List (RoseTree α), (verticesList cs).Pairwise (· < ·)
  | [] => List.Pairwise.nil
  | c :: cs => by
    rw [verticesList_cons, List.pairwise_append, List.pairwise_map, List.pairwise_map]
    refine ⟨(pairwise_lt_vertices c).imp fun h ↦ List.cons_lt_cons_iff.2 (.inr ⟨rfl, h⟩),
      (pairwise_lt_verticesList cs).imp_of_mem fun hp hq h ↦ ?_, ?_⟩
    · obtain ⟨_, _, rfl⟩ := exists_cons_of_mem_verticesList hp
      obtain ⟨_, _, rfl⟩ := exists_cons_of_mem_verticesList hq
      simpa [List.cons_lt_cons_iff] using h
    · simp only [List.mem_map]
      rintro _ ⟨p, -, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hq
      exact List.cons_lt_cons_iff.2 (.inl (Nat.succ_pos j))
end

theorem nodup_vertices (t : RoseTree α) : t.vertices.Nodup :=
  (pairwise_lt_vertices t).nodup

/-- The subtrees of `t` with their positions, in preorder. -/
def positionedSubtrees (t : RoseTree α) : List (TreePath × RoseTree α) :=
  t.vertices.filterMap fun p ↦ (t[p]?).map (⟨p⟩, ·)

theorem mem_positionedSubtrees {t s : RoseTree α} {p : TreePath} :
    (p, s) ∈ t.positionedSubtrees ↔ t[p.toList]? = some s := by
  simp only [positionedSubtrees, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  refine ⟨fun ⟨_, _, _, hs, rfl, rfl⟩ ↦ hs, fun hs ↦ ?_⟩
  exact ⟨p.toList, mem_vertices.mpr (by rw [hs]; rfl), s, hs, rfl, rfl⟩

theorem pairwise_lt_positionedSubtrees (t : RoseTree α) :
    t.positionedSubtrees.Pairwise fun x y ↦ x.1.toList < y.1.toList :=
  (pairwise_lt_vertices t).filterMap _ fun p q h x hx y hy ↦ by
    simp only [Option.map_eq_some_iff] at hx hy
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, rfl⟩ := hy
    exact h

theorem nodup_map_fst_positionedSubtrees (t : RoseTree α) :
    (t.positionedSubtrees.map Prod.fst).Nodup :=
  List.pairwise_map.mpr ((pairwise_lt_positionedSubtrees t).imp fun h he ↦ (he ▸ h).false)

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
    rw [List.map_map, Function.comp_apply, ← ih x.1 (List.fst_mem_of_mem_zipIdx hx)]
    rfl

/-- The listed addresses are exactly the addresses of the leaves. -/
theorem mem_positionedLeaves {t : RoseTree α} {p : TreePath} {a : α} :
    (p, a) ∈ t.positionedLeaves ↔ t[p.toList]? = some (leaf a) := by
  obtain ⟨p⟩ := p
  induction t generalizing p with
  | node b cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · rcases p with _ | ⟨i, p⟩ <;> simp [TreePath.ext_iff, eq_comm]
    rcases p with _ | ⟨i, p⟩
    · simp [positionedLeaves_node_of_ne_nil b hcs, hcs]
    simp only [positionedLeaves_node_of_ne_nil b hcs, List.mem_flatMap, List.mem_map,
      getElem?_cons, children_node, Option.bind_eq_some_iff, Prod.mk.injEq, TreePath.mk.injEq,
      List.cons.injEq]
    constructor
    · rintro ⟨⟨c, j⟩, hc, ⟨⟨q⟩, x⟩, hx, ⟨rfl, rfl⟩, rfl⟩
      have hc := List.mem_zipIdx_iff_getElem?.mp hc
      exact ⟨c, hc, (ih c (List.mem_of_getElem? hc) _).mp hx⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨(c, i), List.mem_zipIdx_iff_getElem?.mpr hc, (⟨p⟩, a),
        (ih c (List.mem_of_getElem? hc) p).mpr h, ⟨rfl, rfl⟩, rfl⟩

/-- The leaf addresses, in the order of the frontier, ascend in precedence. -/
theorem pairwise_precedes_positionedLeaves (t : RoseTree α) :
    t.positionedLeaves.Pairwise fun x y ↦ x.1.Precedes y.1 := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    have hlt : (cs.zipIdx 0).Pairwise fun x y ↦ x.2 < y.2 := by
      have := List.pairwise_lt_range' (s := 0) (n := cs.length)
      rwa [← List.zipIdx_map_snd, List.pairwise_map] at this
    rw [positionedLeaves_node_of_ne_nil a hcs, List.pairwise_flatMap]
    refine ⟨fun ⟨c, i⟩ hc ↦ ?_, hlt.imp fun hij x hx y hy ↦ ?_⟩
    · rw [List.pairwise_map]
      exact (ih c (List.fst_mem_of_mem_zipIdx hc)).imp fun h ↦ h.cons i
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

@[simp] theorem children_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (t.replaceAt (i :: p) new).children = t.children.modify i (·.replaceAt p new) := by
  cases t; rfl

@[simp] theorem value_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ) (new : RoseTree α) :
    (t.replaceAt (i :: p) new).value = t.value := by
  cases t; rfl

theorem value_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
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

/-- Away from the replaced address, at an address neither above nor below it, the subtree is
unchanged. -/
theorem getElem?_replaceAt_of_not_prefix {t new : RoseTree α} {p q : List ℕ} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : (t.replaceAt p new)[q]? = t[q]? := by
  induction p generalizing t q with
  | nil => exact absurd List.nil_prefix hpq
  | cons i p ih =>
    obtain _ | ⟨j, q⟩ := q
    · exact absurd List.nil_prefix hqp
    obtain ⟨a, cs⟩ := t
    obtain rfl | hij := eq_or_ne i j
    · have h (t : RoseTree α) : (t.replaceAt p new)[q]? = t[q]? :=
        ih (fun h ↦ hpq (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
          (fun h ↦ hqp (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
      cases hc : cs[i]? <;> simp [replaceAt_cons, hc, h]
    · simp [replaceAt_cons, hij]

/-- At an address above the replaced one, the subtree has the replacement inside it. -/
theorem getElem?_replaceAt_of_prefix {t new : RoseTree α} {p q : List ℕ} (hqp : q <+: p) :
    (t.replaceAt p new)[q]? = (t[q]?).map (·.replaceAt (p.drop q.length) new) := by
  induction q generalizing t p with
  | nil => simp
  | cons j q ih =>
    obtain _ | ⟨i, p⟩ := p
    · exact absurd hqp (by simp)
    obtain ⟨rfl, h⟩ := List.cons_prefix_cons.mp hqp
    obtain ⟨a, cs⟩ := t
    cases hc : cs[j]? <;> simp [replaceAt_cons, hc, ih h]

theorem getElem?_replaceAt_append {t new : RoseTree α} {p : List ℕ} (hp : (t[p]?).isSome)
    (q : List ℕ) : (t.replaceAt p new)[p ++ q]? = new[q]? := by
  rw [getElem?_append, getElem?_replaceAt_of_prefix (List.prefix_refl p)]
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
  simp [hs]

/-- Replacing the subtree `s` at an address by `new` trades the nodes of `s` for those of `new`. -/
theorem numNodes_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
    (new : RoseTree α) :
    (t.replaceAt p new).numNodes + s.numNodes = t.numNodes + new.numNodes := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil, Option.some.inj h, Nat.add_comm]
  | cons i p ih =>
    obtain ⟨a, cs⟩ := t
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    rw [children_node] at hc
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have := ih hcs
    rw [replaceAt_cons, List.modify_eq_take_cons_drop hi]
    conv_rhs => rw [← List.take_append_drop i cs, List.drop_eq_getElem_cons hi]
    simp only [numNodes_node, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega

/-- Replacing a subtree by a strictly smaller one shrinks the tree. -/
theorem numNodes_replaceAt_lt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
    {new : RoseTree α} (hlt : new.numNodes < s.numNodes) :
    (t.replaceAt p new).numNodes < t.numNodes := by
  have := numNodes_replaceAt h new
  omega

end RoseTree
