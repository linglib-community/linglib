/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Data.Multiset.MapFold

/-!
# Licensed trees

A relation `R a ks` says that a node labelled `a` may have daughters labelled `ks`, in order: it
is a set of local trees, each a node's label with its daughters' labels. `R` licenses a tree when
every subtree of the tree satisfies it at its root, and the trees `R` licenses form a local tree
language. The derivation trees of a context-free grammar are the trees its rules license, and any
well-formedness condition on a node and its daughters' labels takes the same form; a condition on
the root alone is a separate conjunct, and a condition that reads the daughters' subtrees is not
of this form. A tree is licensed exactly when each of its local trees is
(`licensed_iff_forall_mem_localTrees`), which decides licensing.

## Main definitions

* `RoseTree.Licensed R t`: every subtree of `t` satisfies `R` at its root.

## Main results

* `RoseTree.licensed_node_iff`: a tree is licensed when its root's local tree satisfies `R` and
  its children are licensed; `RoseTree.Licensed.induction` is the induction principle.
* `RoseTree.Licensed.of_getElem?`: licensing passes to subtrees.
* `RoseTree.Licensed.replaceAt`: replacing a subtree by a licensed tree with the same root value
  keeps the tree licensed.
* `RoseTree.licensed_of_perm`: a relation that ignores the order of the children licenses
  permuted trees alike, so it licenses unordered trees.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*} {R : α → List α → Prop}

/-- `R` licenses `t` when every subtree of `t` satisfies it at its root, `R a ks` reading "a node
labelled `a` may have daughters labelled `ks`, in order". -/
def Licensed (R : α → List α → Prop) (t : RoseTree α) : Prop :=
  ∀ s, IsSubtree s t → R s.value (s.children.map value)

theorem licensed_node_iff {a : α} {cs : List (RoseTree α)} :
    (node a cs).Licensed R ↔ R a (cs.map value) ∧ ∀ c ∈ cs, c.Licensed R := by
  simp only [Licensed, isSubtree_node_iff, or_imp, forall_and, forall_eq, value_node,
    children_node, forall_exists_index, and_imp]
  exact and_congr_right fun _ ↦ ⟨fun h c hc s hs ↦ h s c hc hs, fun h s c hc hs ↦ h c hc s hs⟩

@[simp] theorem licensed_leaf_iff {a : α} : (leaf a).Licensed R ↔ R a [] := by
  simp [leaf, licensed_node_iff]

theorem licensed_iff_forall_mem_localTrees {t : RoseTree α} :
    t.Licensed R ↔ ∀ e ∈ t.localTrees, R e.1 e.2 := by
  induction t with
  | node a cs ih =>
    simp only [licensed_node_iff, localTrees_node, List.mem_cons, forall_eq_or_imp,
      List.mem_flatten, List.mem_map, forall_exists_index, and_imp]
    refine and_congr_right fun _ ↦ ⟨fun h e l c hc hl he ↦ ?_, fun h c hc ↦ ?_⟩
    · subst hl
      exact (ih c hc).mp (h c hc) e he
    · exact (ih c hc).mpr fun e he ↦ h e _ c hc rfl he

instance [∀ a ks, Decidable (R a ks)] (t : RoseTree α) : Decidable (t.Licensed R) :=
  decidable_of_iff _ licensed_iff_forall_mem_localTrees.symm

theorem Licensed.rel_root {a : α} {cs : List (RoseTree α)} (h : (node a cs).Licensed R) :
    R a (cs.map value) :=
  (licensed_node_iff.mp h).1

theorem Licensed.of_mem {a : α} {cs : List (RoseTree α)} (h : (node a cs).Licensed R)
    {c : RoseTree α} (hc : c ∈ cs) : c.Licensed R :=
  (licensed_node_iff.mp h).2 c hc

/-- Induction over the trees `R` licenses. -/
@[elab_as_elim]
theorem Licensed.induction {motive : (t : RoseTree α) → t.Licensed R → Prop}
    (node : ∀ a cs (hR : R a (cs.map value)) (hcs : ∀ c ∈ cs, c.Licensed R),
      (∀ c (hc : c ∈ cs), motive c (hcs c hc)) →
        motive (node a cs) (licensed_node_iff.mpr ⟨hR, hcs⟩))
    {t : RoseTree α} (ht : t.Licensed R) : motive t ht := by
  induction t with
  | node a cs ih => exact node a cs ht.rel_root (fun _ ↦ ht.of_mem) fun c hc ↦ ih c hc _

theorem Licensed.mono {R' : α → List α → Prop} (h : ∀ a ks, R a ks → R' a ks) {t : RoseTree α}
    (ht : t.Licensed R) : t.Licensed R' :=
  fun s hs ↦ h _ _ (ht s hs)

theorem Licensed.of_isSubtree {s t : RoseTree α} (ht : t.Licensed R) (hs : IsSubtree s t) :
    s.Licensed R :=
  fun r hr ↦ ht r (hr.trans hs)

theorem Licensed.of_getElem? {t s : RoseTree α} (ht : t.Licensed R) {p : List ℕ}
    (hs : t[p]? = some s) : s.Licensed R :=
  ht.of_isSubtree (isSubtree_iff_exists_getElem?.mpr ⟨p, hs⟩)

/-- Replacing a subtree by a licensed tree with the same root value keeps a tree licensed. -/
theorem Licensed.replaceAt {t s new : RoseTree α} (ht : t.Licensed R) {p : List ℕ}
    (hs : t[p]? = some s) (hnew : new.Licensed R) (hv : new.value = s.value) :
    (t.replaceAt p new).Licensed R := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil]; exact hnew
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp hs
    cases t with
    | node a cs =>
      rw [children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node]
      have hval : (c.replaceAt p new).value = c.value := by
        cases p with
        | nil => rw [replaceAt_nil, hv, Option.some.inj hcs]
        | cons j p => exact value_replaceAt_cons c j p new
      refine licensed_node_iff.mpr ⟨?_, fun d hd ↦ ?_⟩
      · obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
        have h := List.set_getElem_self (as := cs.map value) (i := i) (by simpa using hi)
        rw [List.getElem_map] at h
        rw [List.map_set, hval, h]
        exact ht.rel_root
      · rcases List.mem_or_eq_of_mem_set hd with hd | rfl
        · exact ht.of_mem hd
        · exact ih (ht.of_mem (List.mem_of_getElem? hc)) hcs

/-- A relation that ignores the order of the children licenses a tree exactly when it licenses
any permutation of it. -/
theorem licensed_of_perm (hR : ∀ a {ks ls : List α}, ks.Perm ls → (R a ks ↔ R a ls)) :
    ∀ {t s : RoseTree α}, t.Perm s → (t.Licensed R ↔ s.Licensed R) := by
  intro t
  induction t with
  | node a cs ih =>
    rintro ⟨b, ds⟩ h
    obtain ⟨rfl, hrel⟩ := perm_node_iff.mp h
    rw [licensed_node_iff, licensed_node_iff]
    have hval : (cs.map value).Perm (ds.map value) := by
      have := Multiset.rel_eq.1 (Multiset.rel_map.2 (hrel.mono fun c _ d _ hcd ↦ hcd.value_eq))
      rwa [Multiset.map_coe, Multiset.map_coe, Multiset.coe_eq_coe] at this
    refine and_congr (hR a hval) ⟨fun hc d hd ↦ ?_, fun hd c hc ↦ ?_⟩
    · obtain ⟨c, hc', hcd⟩ :=
        Multiset.exists_mem_of_rel_of_mem (Multiset.rel_flip.mpr hrel) (Multiset.mem_coe.mpr hd)
      exact (ih c (Multiset.mem_coe.mp hc') hcd).mp (hc c (Multiset.mem_coe.mp hc'))
    · obtain ⟨d, hd', hcd⟩ := Multiset.exists_mem_of_rel_of_mem hrel (Multiset.mem_coe.mpr hc)
      exact (ih c hc hcd).mpr (hd d (Multiset.mem_coe.mp hd'))

theorem licensed_map_iff {β : Type*} {f : α → β} {R' : β → List β → Prop}
    (h : ∀ a ks, R' (f a) (ks.map f) ↔ R a ks) {t : RoseTree α} :
    (map f t).Licensed R' ↔ t.Licensed R := by
  induction t with
  | node a cs ih =>
    rw [map_node, licensed_node_iff, licensed_node_iff, List.map_map,
      show value ∘ map f = f ∘ value from funext fun c ↦ value_map f c, ← List.map_map, h,
      List.forall_mem_map]
    exact and_congr_right fun _ ↦ forall₂_congr fun c hc ↦ ih c hc

end RoseTree
