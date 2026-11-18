/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Structure
public import Mathlib.Order.Atoms

/-!
# Tree-shaped structures are trees

A finite tree-shaped prosodic structure [is the structure of a
tree](##Prosody.Structure.IsTree.exists_iso_ofTree), so that with
`Prosody.Structure.nonempty_iso_ofTree_iff` the ordered trees are, up to isomorphism, exactly
the finite tree-shaped structures. The tree is built from the root: the daughters of a node are
the nodes covering it, listed in their order of precedence, and an address is followed through
those lists to the node it names.
-/

@[expose] public section

namespace Prosody.Structure
open RoseTree

universe v

variable {α : Type v}

namespace IsTree

variable {X : Structure.{0} α} (h : X.IsTree)
include h

/-- In a tree-shaped structure, distinct nodes covering a node are related by precedence. -/
theorem precedes_or_precedes_of_covBy {a c c' : X.Node} (hc : a ⋖ c) (hc' : a ⋖ c')
    (hne : c ≠ c') : X.Precedes c c' ∨ X.Precedes c' c := by
  rcases h.le_or_precedes c c' with hle | hle | hp | hp
  · exact absurd (lt_of_le_of_ne hle hne) (hc'.2 hc.1)
  · exact absurd (lt_of_le_of_ne hle hne.symm) (hc.2 hc'.1)
  · exact .inl hp
  · exact .inr hp

variable [Finite X.Node]

/-- The nodes covering a node can be listed in order of precedence. -/
theorem exists_list_covBy (a : X.Node) :
    ∃ l : List X.Node, (∀ c, c ∈ l ↔ a ⋖ c) ∧ l.Pairwise X.Precedes := by
  classical
  obtain ⟨l, hnd, hl⟩ := Finite.exists_univ_list {c : X.Node // a ⋖ c}
  let le : {c : X.Node // a ⋖ c} → {c : X.Node // a ⋖ c} → Bool :=
    fun x y ↦ decide (x = y ∨ X.Precedes x.1 y.1)
  have htrans : ∀ x y z, le x y = true → le y z = true → le x z = true := by
    simp only [le, decide_eq_true_eq]
    rintro x y z (rfl | hxy) (rfl | hyz)
    · exact .inl rfl
    · exact .inr hyz
    · exact .inr hxy
    · exact .inr (h.trans hxy hyz)
  have htotal : ∀ x y, (le x y || le y x) = true := by
    intro x y
    simp only [le, Bool.or_eq_true, decide_eq_true_eq]
    by_cases hxy : x = y
    · exact .inl (.inl hxy)
    rcases h.precedes_or_precedes_of_covBy x.2 y.2 (fun e ↦ hxy (Subtype.ext e)) with hp | hp
    · exact .inl (.inr hp)
    · exact .inr (.inr hp)
  refine ⟨(l.mergeSort le).map Subtype.val, fun c ↦ ?_, ?_⟩
  · simp only [List.mem_map, List.mem_mergeSort]
    exact ⟨fun ⟨x, _, hx⟩ ↦ hx ▸ x.2, fun hc ↦ ⟨⟨c, hc⟩, hl _, rfl⟩⟩
  · have hnd' : (l.mergeSort le).Nodup := (List.mergeSort_perm l le).nodup_iff.2 hnd
    rw [List.pairwise_map]
    refine ((List.pairwise_mergeSort htrans htotal l).and hnd').imp fun ⟨hle, hne⟩ ↦ ?_
    simp only [le, decide_eq_true_eq] at hle
    exact hle.resolve_left hne

/-- The daughters of a node, the nodes covering it, in order of precedence. -/
noncomputable def daughters (a : X.Node) : List X.Node :=
  (h.exists_list_covBy a).choose

theorem mem_daughters {a c : X.Node} : c ∈ h.daughters a ↔ a ⋖ c :=
  (h.exists_list_covBy a).choose_spec.1 c

theorem pairwise_daughters (a : X.Node) : (h.daughters a).Pairwise X.Precedes :=
  (h.exists_list_covBy a).choose_spec.2

/-- The tree of a node: its label over the trees of its daughters, in order of precedence. -/
noncomputable def toTree : X.Node → RoseTree α :=
  wellFounded_gt.fix fun a ih ↦
    node (X.label a) ((h.daughters a).attach.map fun c ↦ ih c.1 (h.mem_daughters.1 c.2).lt)

theorem toTree_eq (a : X.Node) :
    h.toTree a = node (X.label a) ((h.daughters a).map h.toTree) := by
  rw [toTree, WellFounded.fix_eq]
  exact congrArg _ List.attach_map_val

/-- The node reached from `a` by following an address through the daughters. -/
noncomputable def walk : X.Node → List ℕ → Option X.Node
  | a, [] => some a
  | a, i :: p => (h.daughters a)[i]?.bind fun c ↦ walk c p

@[simp] theorem walk_nil (a : X.Node) : h.walk a [] = some a := rfl

@[simp] theorem walk_cons (a : X.Node) (i : ℕ) (p : List ℕ) :
    h.walk a (i :: p) = (h.daughters a)[i]?.bind (h.walk · p) := rfl

theorem walk_append (a : X.Node) (p q : List ℕ) :
    h.walk a (p ++ q) = (h.walk a p).bind (h.walk · q) := by
  induction p generalizing a with
  | nil => rfl
  | cons i p ih => simp only [List.cons_append, walk_cons, ih, Option.bind_assoc]

theorem walk_append_eq_some {a b : X.Node} {p q : List ℕ} :
    h.walk a (p ++ q) = some b ↔ ∃ c, h.walk a p = some c ∧ h.walk c q = some b := by
  rw [walk_append, Option.bind_eq_some_iff]

theorem walk_singleton (a : X.Node) (i : ℕ) : h.walk a [i] = (h.daughters a)[i]? := by
  simp

theorem le_of_walk {a b : X.Node} {p : List ℕ} (hp : h.walk a p = some b) : a ≤ b := by
  induction p generalizing a with
  | nil => exact (Option.some.inj hp).le
  | cons i p ih =>
    rw [walk_cons, Option.bind_eq_some_iff] at hp
    obtain ⟨c, hc, hcb⟩ := hp
    exact (h.mem_daughters.1 (List.mem_of_getElem? hc)).le.trans (ih hcb)

theorem lt_of_walk_cons {a b : X.Node} {i : ℕ} {p : List ℕ} (hp : h.walk a (i :: p) = some b) :
    a < b := by
  rw [walk_cons, Option.bind_eq_some_iff] at hp
  obtain ⟨c, hc, hcb⟩ := hp
  exact (h.mem_daughters.1 (List.mem_of_getElem? hc)).lt.trans_le (h.le_of_walk hcb)

theorem eq_nil_of_walk_eq_some_self {a : X.Node} {p : List ℕ} (hp : h.walk a p = some a) :
    p = [] := by
  cases p with
  | nil => rfl
  | cons i p => exact absurd (h.lt_of_walk_cons hp) (lt_irrefl a)

theorem exists_walk_eq_some {a b : X.Node} (hab : a ≤ b) : ∃ p, h.walk a p = some b := by
  induction a using WellFoundedGT.induction with
  | _ a ih =>
    rcases hab.eq_or_lt with rfl | hlt
    · exact ⟨[], rfl⟩
    obtain ⟨c, hac, hcb⟩ := exists_covBy_le_of_lt hlt
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (h.mem_daughters.2 hac)
    obtain ⟨p, hp⟩ := ih c hac.lt hcb
    exact ⟨i :: p, by rw [walk_cons, hi, Option.bind_some, hp]⟩

theorem getElem?_toTree (a : X.Node) (p : List ℕ) :
    (h.toTree a)[p]? = (h.walk a p).map h.toTree := by
  induction p generalizing a with
  | nil => rfl
  | cons i p ih =>
    rw [getElem?_cons, h.toTree_eq a, children_node, List.getElem?_map, walk_cons,
      Option.bind_map, Option.map_bind]
    exact congrArg _ (funext ih)

theorem walk_isSome {a : X.Node} {p : GornAddress} (hp : p ∈ (h.toTree a).validPaths) :
    (h.walk a p.toList).isSome := by
  rwa [mem_validPaths_iff_isSome, getElem?_gornAddress, getElem?_toTree, Option.isSome_map] at hp

theorem le_of_walk_of_le {a x y : X.Node} {p q : GornAddress} (hx : h.walk a p.toList = some x)
    (hy : h.walk a q.toList = some y) (hpq : p ≤ q) : x ≤ y := by
  obtain ⟨s, hs⟩ := hpq
  rw [← hs, walk_append_eq_some] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rw [hx, Option.some.injEq] at hz
  subst hz
  exact h.le_of_walk hzy

theorem precedes_of_walk {a x y : X.Node} {p q : GornAddress} (hx : h.walk a p.toList = some x)
    (hy : h.walk a q.toList = some y) (hpq : p.Precedes q) : X.Precedes x y := by
  obtain ⟨r, i, j, hij, ⟨s, hs⟩, ⟨s', hs'⟩⟩ := hpq
  simp only [← hs, ← hs', GornAddress.toList_mul, GornAddress.toList_of,
    walk_append_eq_some] at hx hy
  obtain ⟨u, ⟨w, hw, hwu⟩, hux⟩ := hx
  obtain ⟨v, ⟨w', hw', hw'v⟩, hvy⟩ := hy
  rw [hw, Option.some.injEq] at hw'
  subst hw'
  rw [walk_singleton] at hwu hw'v
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hwu
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hw'v
  exact h.mono (List.pairwise_iff_getElem.1 (h.pairwise_daughters w) i j hi hj hij)
    (h.le_of_walk hux) (h.le_of_walk hvy)

theorem le_of_walk_of_le_node {a x y : X.Node} {p q : GornAddress}
    (hx : h.walk a p.toList = some x) (hy : h.walk a q.toList = some y) (hxy : x ≤ y) :
    p ≤ q := by
  rcases GornAddress.Precedes.trichotomy p q with hpq | hqp | hpq | hqp
  · exact hpq
  · obtain ⟨s, hs⟩ := hqp
    rw [← hs, walk_append_eq_some] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    rw [hy, Option.some.injEq] at hz
    subst hz
    rw [hxy.antisymm (h.le_of_walk hzx)] at hzx
    rw [h.eq_nil_of_walk_eq_some_self hzx, List.append_nil] at hs
    exact (GornAddress.ext hs).ge
  · exact absurd hxy (h.not_le (h.precedes_of_walk hx hy hpq))
  · exact absurd hxy (h.not_ge (h.precedes_of_walk hy hx hqp))

theorem precedes_of_walk_of_precedes {a x y : X.Node} {p q : GornAddress}
    (hx : h.walk a p.toList = some x) (hy : h.walk a q.toList = some y)
    (hxy : X.Precedes x y) : p.Precedes q := by
  rcases GornAddress.Precedes.trichotomy p q with hpq | hqp | hpq | hqp
  · exact absurd (h.le_of_walk_of_le hx hy hpq) (h.not_le hxy)
  · exact absurd (h.le_of_walk_of_le hy hx hqp) (h.not_ge hxy)
  · exact hpq
  · exact absurd (h.trans hxy (h.precedes_of_walk hy hx hqp)) (h.irrefl x)

/-- The node at a position of the tree of `a`. -/
noncomputable def nodeAt (a : X.Node) (p : (h.toTree a).Positions) : X.Node :=
  (h.walk a p.1.toList).get (h.walk_isSome p.2)

theorem walk_nodeAt (a : X.Node) (p : (h.toTree a).Positions) :
    h.walk a p.1.toList = some (h.nodeAt a p) :=
  Option.eq_some_of_isSome _

theorem value_subtree (a : X.Node) (p : (h.toTree a).Positions) :
    p.subtree.value = X.label (h.nodeAt a p) := by
  rw [Positions.subtree_eq_iff.2 (by rw [getElem?_toTree, h.walk_nodeAt]; rfl), h.toTree_eq]
  rfl

end IsTree

/-- A finite tree-shaped structure is the structure of a tree. -/
theorem IsTree.exists_iso_ofTree {X : Structure.{0} α} (h : X.IsTree) [Finite X.Node] :
    ∃ t : RoseTree α, Nonempty (Iso (ofTree t) X) := by
  obtain ⟨r, hr⟩ := h.exists_isBot
  refine ⟨h.toTree r, ⟨?_⟩⟩
  let f : (h.toTree r).Positions ↪o X.Node := OrderEmbedding.ofMapLEIff (h.nodeAt r) fun p q ↦
    ⟨h.le_of_walk_of_le_node (h.walk_nodeAt r p) (h.walk_nodeAt r q),
      h.le_of_walk_of_le (h.walk_nodeAt r p) (h.walk_nodeAt r q)⟩
  have hf : Function.Surjective f := fun b ↦ by
    obtain ⟨p, hp⟩ := h.exists_walk_eq_some (hr b)
    have hv : (⟨p⟩ : GornAddress) ∈ (h.toTree r).validPaths := by
      rw [mem_validPaths_iff_isSome, getElem?_gornAddress, getElem?_toTree, hp]
      rfl
    exact ⟨⟨⟨p⟩, hv⟩,
      Option.some.inj ((h.walk_nodeAt r ⟨⟨p⟩, hv⟩).symm.trans hp)⟩
  exact
    { toOrderIso := RelIso.ofSurjective f hf
      precedes_iff := fun p q ↦
        ⟨h.precedes_of_walk_of_precedes (h.walk_nodeAt r p) (h.walk_nodeAt r q),
          h.precedes_of_walk (h.walk_nodeAt r p) (h.walk_nodeAt r q)⟩
      label_comp := fun p ↦ (h.value_subtree r p).symm }

end Prosody.Structure
