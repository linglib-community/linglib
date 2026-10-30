/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get

/-!
# Spans of subtrees in the frontier

The frontier of a subtree is a slice of the frontier of the tree. `RoseTree.leafIndex t p` is
where the slice for the subtree at the address `p` begins, the number of leaves of `t` to its
left, and the slice has as many entries as the subtree has leaves. These are the lemmas
`List.take_sum_flatten`, `List.drop_sum_flatten` and `List.drop_take_succ_flatten_eq_getElem`
of mathlib one level up: a list of lists is a tree of height two, and the index of its `i`th
member in the flattened list is the sum of the lengths before it.

Dominance and precedence of positions become containment and order of spans. A position below
another begins no earlier and ends no later, a position that precedes another ends before the
other begins, and two positions are left-aligned (`TreePath.LeftAligned`) exactly when they
begin at the same leaf.

## Main definitions

* `RoseTree.leafIndex`: the number of leaves left of the subtree at an address.
* `RoseTree.spans`: the slices of the frontier that the subtrees satisfying a predicate cover.

## Main results

* `RoseTree.drop_take_leafList`: the frontier of a subtree is the slice of the frontier that
  begins at its index.
* `RoseTree.leafList_replaceAt`: replacing a subtree replaces its slice.
* `RoseTree.leafIndex_add_numLeaves_le_of_precedes`: a subtree ends before one it precedes begins.
* `RoseTree.leftAligned_iff_leafIndex_eq`: left-aligned positions are those with one index.
* `RoseTree.mem_spans`: the spans are the slices of the subtrees satisfying the predicate.
* `RoseTree.spans_node`: the spans of a node are its own and those of its children, each shifted
  past the leaves of the children before it.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*} {t s : RoseTree α} {p q : List ℕ}

/-! ### The index of a subtree -/

/-- `t.leafIndex p` is the number of leaves of `t` to the left of the subtree at the address `p`,
the index in the frontier at which the frontier of that subtree begins. -/
def leafIndex : RoseTree α → List ℕ → ℕ
  | _, [] => 0
  | node _ cs, i :: p => ((cs.take i).map numLeaves).sum + (cs[i]?.elim 0 (·.leafIndex p))

@[simp] theorem leafIndex_nil (t : RoseTree α) : t.leafIndex [] = 0 := by cases t; rfl

theorem leafIndex_cons (t : RoseTree α) (i : ℕ) (p : List ℕ) :
    t.leafIndex (i :: p) =
      ((t.children.take i).map numLeaves).sum + (t.children[i]?.elim 0 (·.leafIndex p)) := by
  cases t; rfl

theorem leafIndex_cons_of_getElem? {c : RoseTree α} {i : ℕ} (hc : t.children[i]? = some c)
    (p : List ℕ) :
    t.leafIndex (i :: p) = ((t.children.take i).map numLeaves).sum + c.leafIndex p := by
  rw [leafIndex_cons, hc, Option.elim_some]

theorem leafIndex_append (h : t[p]? = some s) (q : List ℕ) :
    t.leafIndex (p ++ q) = t.leafIndex p + s.leafIndex q := by
  induction p generalizing t with
  | nil => obtain rfl := Option.some.inj h; simp
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    rw [List.cons_append, leafIndex_cons_of_getElem? hc, leafIndex_cons_of_getElem? hc, ih hcs,
      Nat.add_assoc]

/-! ### The slice of a subtree -/

private theorem exists_leafList_eq (h : t[p]? = some s) :
    ∃ pre post : List α, pre.length = t.leafIndex p ∧ t.leafList = pre ++ s.leafList ++ post ∧
      ∀ new : RoseTree α, (t.replaceAt p new).leafList = pre ++ new.leafList ++ post := by
  induction p generalizing t with
  | nil => exact ⟨[], [], by simp, by simp [Option.some.inj h], fun new ↦ by simp⟩
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    obtain ⟨pre, post, hlen, hy, hy'⟩ := ih hcs
    obtain ⟨a, cs⟩ := t
    rw [children_node] at hc
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have hcs' : cs = cs.take i ++ cs[i] :: cs.drop (i + 1) := by
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    refine ⟨((cs.take i).map leafList).flatten ++ pre,
      post ++ ((cs.drop (i + 1)).map leafList).flatten, ?_, ?_, fun new ↦ ?_⟩
    · rw [leafIndex_cons_of_getElem? (t := node a cs) (List.getElem?_eq_getElem hi),
        List.length_append, hlen, List.length_flatten, List.map_map, children_node]
      exact congrArg (· + _) (congrArg List.sum (List.map_congr_left fun c _ ↦ length_leafList c))
    · conv_lhs => rw [hcs']
      rw [leafList_node_of_ne_nil _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
        List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, hy]
      simp only [List.append_assoc]
    · rw [replaceAt_cons_of_getElem? (t := node a cs) (List.getElem?_eq_getElem hi), value_node,
        children_node, List.set_eq_take_append_cons_drop, ite_eq_left hi,
        leafList_node_of_ne_nil _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
        List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, hy']
      simp only [List.append_assoc]

private theorem take_drop_leafList (h : t[p]? = some s) :
    t.leafList.take (t.leafIndex p) ++ s.leafList ++
        t.leafList.drop (t.leafIndex p + s.numLeaves) = t.leafList ∧
      ∀ new : RoseTree α, (t.replaceAt p new).leafList =
        t.leafList.take (t.leafIndex p) ++ new.leafList ++
          t.leafList.drop (t.leafIndex p + s.numLeaves) := by
  obtain ⟨pre, post, hlen, hy, hy'⟩ := exists_leafList_eq h
  have h₁ : t.leafList.take (t.leafIndex p) = pre := by
    rw [hy, List.append_assoc, ← hlen, List.take_left]
  have h₂ : t.leafList.drop (t.leafIndex p + s.numLeaves) = post := by
    rw [hy, ← hlen, ← length_leafList, ← List.length_append, List.drop_left]
  exact ⟨by rw [h₁, h₂, ← hy], fun new ↦ by rw [h₁, h₂, hy']⟩

theorem leafIndex_add_numLeaves_le (h : t[p]? = some s) :
    t.leafIndex p + s.numLeaves ≤ t.numLeaves := by
  obtain ⟨pre, post, hlen, hy, -⟩ := exists_leafList_eq h
  have := congrArg List.length hy
  simp only [List.length_append, length_leafList, hlen] at this
  omega

theorem take_append_leafList_append_drop (h : t[p]? = some s) :
    t.leafList.take (t.leafIndex p) ++ s.leafList ++
      t.leafList.drop (t.leafIndex p + s.numLeaves) = t.leafList :=
  (take_drop_leafList h).1

/-- The frontier of the subtree at `p` is the slice of the frontier of the tree that begins at
`t.leafIndex p`. -/
theorem drop_take_leafList (h : t[p]? = some s) :
    (t.leafList.take (t.leafIndex p + s.numLeaves)).drop (t.leafIndex p) = s.leafList := by
  obtain ⟨pre, post, hlen, hy, -⟩ := exists_leafList_eq h
  rw [hy, ← hlen, ← length_leafList, ← List.length_append, List.take_left, List.drop_left]

/-- Replacing the subtree at `p` replaces its slice of the frontier. -/
theorem leafList_replaceAt (h : t[p]? = some s) (new : RoseTree α) :
    (t.replaceAt p new).leafList = t.leafList.take (t.leafIndex p) ++ new.leafList ++
      t.leafList.drop (t.leafIndex p + s.numLeaves) :=
  (take_drop_leafList h).2 new

theorem getElem?_leafList_leafIndex {a : α} (h : t[p]? = some (leaf a)) :
    t.leafList[t.leafIndex p]? = some a := by
  obtain ⟨pre, post, hlen, hy, -⟩ := exists_leafList_eq h
  simp [hy, ← hlen]

theorem IsSubtree.leafList_isInfix (h : IsSubtree s t) : s.leafList <:+: t.leafList :=
  let ⟨_, hp⟩ := isSubtree_iff_exists_getElem?.1 h
  let ⟨pre, post, _, hy, _⟩ := exists_leafList_eq hp
  ⟨pre, post, hy.symm⟩

@[simp] theorem leafIndex_map {β : Type*} (f : α → β) (t : RoseTree α) (p : List ℕ) :
    (t.map f).leafIndex p = t.leafIndex p := by
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    obtain ⟨a, cs⟩ := t
    simp only [map_node, leafIndex_cons, children_node, ← List.map_take, List.map_map,
      List.getElem?_map]
    congr 1
    · exact congrArg List.sum (List.map_congr_left fun c _ ↦ numLeaves_map f c)
    · cases cs[i]? with
      | none => rfl
      | some c => exact ih c

/-! ### Dominance and precedence -/

theorem leafIndex_le_leafIndex_append (h : t[p]? = some s) (q : List ℕ) :
    t.leafIndex p ≤ t.leafIndex (p ++ q) :=
  leafIndex_append h q ▸ Nat.le_add_right _ _

theorem leafIndex_append_add_numLeaves_le {u : RoseTree α} (h : t[p]? = some s)
    (hu : s[q]? = some u) :
    t.leafIndex (p ++ q) + u.numLeaves ≤ t.leafIndex p + s.numLeaves := by
  rw [leafIndex_append h, Nat.add_assoc]
  exact Nat.add_le_add_left (leafIndex_add_numLeaves_le hu) _

private theorem sum_take_add_numLeaves_le {cs : List (RoseTree α)} {i j : ℕ} {c : RoseTree α}
    (hc : cs[i]? = some c) (hij : i < j) :
    ((cs.take i).map numLeaves).sum + c.numLeaves ≤ ((cs.take j).map numLeaves).sum := by
  have h : ((cs.take (i + 1)).map numLeaves).sum =
      ((cs.take i).map numLeaves).sum + c.numLeaves := by
    rw [List.take_add_one, hc]; simp
  rw [← h]
  exact ((List.take_sublist_take_left (Nat.succ_le_of_lt hij)).map numLeaves).sum_le_sum
    fun _ _ ↦ Nat.zero_le _

/-- The frontier of a subtree ends before the frontier of any subtree it precedes begins. -/
theorem leafIndex_add_numLeaves_le_of_precedes {p q : TreePath} (hpq : p.Precedes q)
    (hp : t[p.toList]? = some s) (hq : (t[q.toList]?).isSome) :
    t.leafIndex p.toList + s.numLeaves ≤ t.leafIndex q.toList := by
  obtain ⟨r, i, j, hij, ⟨p', hp'⟩, ⟨q', hq'⟩⟩ := hpq
  rw [List.append_assoc, List.singleton_append] at hp' hq'
  rw [← hp', getElem?_append] at hp
  rw [← hq', getElem?_append] at hq
  obtain ⟨u, hu, hs⟩ := Option.bind_eq_some_iff.mp hp
  rw [hu, Option.bind_some] at hq
  obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp hs
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
  obtain ⟨d, hd, -⟩ := getElem?_cons_eq_some_iff.mp hv
  rw [← hp', ← hq', leafIndex_append hu, leafIndex_append hu, leafIndex_cons_of_getElem? hc,
    leafIndex_cons_of_getElem? hd]
  have h₁ := leafIndex_add_numLeaves_le hcs
  have h₂ := sum_take_add_numLeaves_le hc hij
  omega

/-! ### Left-alignment -/

theorem leafIndex_replicate_zero (t : RoseTree α) (k : ℕ) :
    t.leafIndex (List.replicate k 0) = 0 := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, leafIndex_cons]
    cases t.children[0]? with
    | none => rfl
    | some c => simpa using ih c

theorem leafIndex_eq_zero_iff (h : (t[p]?).isSome) :
    t.leafIndex p = 0 ↔ ∀ i ∈ p, i = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ List.eq_replicate_iff.2 ⟨rfl, h0⟩ ▸ leafIndex_replicate_zero t _⟩
  induction p generalizing t with
  | nil => simp
  | cons i p ih =>
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp hs
    rw [leafIndex_cons_of_getElem? hc, Nat.add_eq_zero_iff] at h0
    have hi : i ≤ ((t.children.take i).map numLeaves).sum := by
      have := List.length_le_sum_of_one_le ((t.children.take i).map numLeaves) fun n hn ↦ by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hn
        exact numLeaves_pos c
      rwa [List.length_map, List.length_take_of_le (List.getElem?_eq_some_iff.mp hc).1.le] at this
    exact List.forall_mem_cons.2 ⟨by omega, ih (by rw [hcs]; rfl) h0.2⟩

/-- Two positions of a tree are left-aligned exactly when their frontiers begin at the same
leaf. -/
theorem leftAligned_iff_leafIndex_eq {p q : TreePath} (hp : (t[p.toList]?).isSome)
    (hq : (t[q.toList]?).isSome) :
    p.LeftAligned q ↔ t.leafIndex p.toList = t.leafIndex q.toList := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hq
  constructor
  · intro h
    obtain ⟨j, k, h⟩ := TreePath.leftAligned_iff_exists.1 h
    have := congrArg t.leafIndex h
    rwa [leafIndex_append hs, leafIndex_append hu, leafIndex_replicate_zero,
      leafIndex_replicate_zero] at this
  · intro h
    have key : ∀ {p q : TreePath} {s : RoseTree α}, t[p.toList]? = some s →
        (t[q.toList]?).isSome → t.leafIndex p.toList = t.leafIndex q.toList → p ≤ q →
        p.LeftAligned q := by
      rintro p q s hs hq h ⟨r, hr⟩
      rw [← hr, leafIndex_append hs] at h
      rw [← hr, getElem?_append, hs, Option.bind_some] at hq
      have hr0 : r = List.replicate r.length 0 :=
        List.eq_replicate_iff.2 ⟨rfl, (leafIndex_eq_zero_iff hq).1 (by omega)⟩
      exact TreePath.leftAligned_iff_exists.2
        ⟨r.length, 0, by rw [← hr, List.replicate_zero, List.append_nil, ← hr0]⟩
    rcases TreePath.Precedes.trichotomy p q with hpq | hqp | hpq | hqp
    · exact key hs hq h hpq
    · exact (key hu hp h.symm hqp).symm
    · have := leafIndex_add_numLeaves_le_of_precedes hpq hs hq
      have := numLeaves_pos s
      omega
    · have := leafIndex_add_numLeaves_le_of_precedes hqp hu hp
      have := numLeaves_pos u
      omega

/-! ### Spans -/

section Spans

variable (P : RoseTree α → Prop) [DecidablePred P] (t) {x : ℕ × ℕ}

/-- The spans of the subtrees of `t` satisfying `P`, in preorder: for the subtree at an address,
the index in the frontier at which its slice begins and the index at which it ends. -/
def spans : List (ℕ × ℕ) :=
  t.vertices.filterMap fun p ↦ (t[p]?).bind fun s ↦
    if P s then some (t.leafIndex p, t.leafIndex p + s.numLeaves) else none

variable {P t}

theorem mem_spans : x ∈ t.spans P ↔
    ∃ p s, t[p]? = some s ∧ P s ∧ (t.leafIndex p, t.leafIndex p + s.numLeaves) = x := by
  simp only [spans, List.mem_filterMap, mem_vertices, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq]
  exact ⟨fun ⟨p, _, s, hs, hP, hx⟩ ↦ ⟨p, s, hs, hP, hx⟩,
    fun ⟨p, s, hs, hP, hx⟩ ↦ ⟨p, by simp [hs], s, hs, hP, hx⟩⟩

variable (P) in
/-- The spans of a forest, each tree's shifted past the leaves of the trees before it. -/
def spansList : List (RoseTree α) → List (ℕ × ℕ)
  | [] => []
  | c :: cs => c.spans P ++ (spansList cs).map fun x ↦ (c.numLeaves + x.1, c.numLeaves + x.2)

@[simp] theorem spansList_nil : spansList P ([] : List (RoseTree α)) = [] := rfl

@[simp] theorem spansList_cons (c : RoseTree α) (cs : List (RoseTree α)) :
    spansList P (c :: cs) =
      c.spans P ++ (spansList P cs).map fun x ↦ (c.numLeaves + x.1, c.numLeaves + x.2) :=
  rfl

private theorem filterMap_verticesList (a : α) (cs : List (RoseTree α)) :
    (verticesList cs).filterMap (fun p ↦ ((node a cs)[p]?).bind fun s ↦
      if P s then some ((node a cs).leafIndex p, (node a cs).leafIndex p + s.numLeaves)
      else none) = spansList P cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesList_cons, List.filterMap_append, List.filterMap_map, List.filterMap_map,
      spansList_cons, ← ih, List.map_filterMap]
    congr 1
    · exact List.filterMap_congr fun p _ ↦ by simp [leafIndex_cons]
    refine List.filterMap_congr fun p hp ↦ ?_
    obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hp
    simp only [Function.comp_apply, List.modifyHead_cons, getElem?_cons, children_node,
      List.getElem?_cons_succ, leafIndex_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
    cases cs[j]?.bind (·[q]?) with
    | none => rfl
    | some s => by_cases hP : P s <;> simp [hP, Nat.add_assoc]

/-- The spans of a node are its own, if it satisfies `P`, and those of its forest of
children. -/
@[simp] theorem spans_node (a : α) (cs : List (RoseTree α)) :
    (node a cs).spans P =
      (if P (node a cs) then [(0, (node a cs).numLeaves)] else []) ++ spansList P cs := by
  rw [spans, vertices_node, List.filterMap_cons, filterMap_verticesList]
  by_cases hP : P (node a cs) <;> simp [hP]

theorem spansList_append (l₁ l₂ : List (RoseTree α)) :
    spansList P (l₁ ++ l₂) = spansList P l₁ ++ (spansList P l₂).map
      fun x ↦ ((l₁.map numLeaves).sum + x.1, (l₁.map numLeaves).sum + x.2) := by
  induction l₁ with
  | nil => simp
  | cons c l ih => simp [ih, Nat.add_assoc]

theorem spansList_replicate (n : ℕ) (h : t.spans P = []) : spansList P (.replicate n t) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, h, ih]

end Spans

end RoseTree
