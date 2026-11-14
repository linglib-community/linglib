/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Subtree
public import Linglib.Core.Order.TreePath

/-!
# Rose trees under Gorn addresses

A Gorn address is the list of child indices on the way down from the root, and a rose tree is
indexed by addresses: `t[p]?` is the subtree reached by following `p` down from the root, and an
address given as a `TreePath` is read through its list. The addresses inside a tree are its
positions, [`RoseTree.validPaths`](##RoseTree.validPaths), a
[prefix-closed](##RoseTree.isLowerSet_validPaths) set of `TreePath`s, and the trees found at them
[are its subtrees](##RoseTree.isSubtree_iff_exists_getElem?). `RoseTree/Positions.lean` lists the
positions and orders them, and `RoseTree/ReplaceAt.lean` replaces the subtree at one.
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

theorem height_le_of_getElem? {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s) :
    s.height ≤ t.height := by
  induction p generalizing t with
  | nil => exact (Option.some.inj h).symm ▸ Nat.le_refl _
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    exact (ih hcs).trans (height_lt_of_mem (List.mem_of_getElem? hc)).le

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
/-! ### Subtrees at addresses -/

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
end RoseTree
