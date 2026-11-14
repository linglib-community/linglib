/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.ReplaceAt
public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Data.Multiset.MapFold

/-!
# Licensed trees

A relation `R a ks` says that a node labelled `a` may have daughters labelled `ks`, in order: it
is a set of local trees, each a node's label with its daughters' labels. `R`
[licenses](##RoseTree.Licensed) a tree when every subtree satisfies it at its root, which is when
[the root does and `R` licenses each child](##RoseTree.licensed_node_iff), and when [each local
tree of the tree is in `R`](##RoseTree.licensed_iff_forall_mem_localTrees), which decides
licensing. The trees `R` licenses form a local tree language: the derivation trees of a
context-free grammar are the trees its rules license. Licensing
[passes to subtrees](##RoseTree.Licensed.of_isSubtree), and a relation that ignores the order of
the daughters [licenses the permutations of a tree alike](##RoseTree.Perm.licensed_iff).

## Implementation notes

A condition on the root alone is a separate conjunct beside `Licensed`, and a condition that reads
the daughters' subtrees and not only their labels is not of this form.
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

theorem licensed_iff_forall_mem_subtrees {t : RoseTree α} :
    t.Licensed R ↔ ∀ s ∈ t.subtrees, R s.value (s.children.map value) :=
  forall_congr' fun _ ↦ imp_congr_left mem_subtrees.symm

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

/-- A tree whose nodes have at most `b` children has at most `b ^ (height - 1)` leaves. -/
theorem Licensed.numLeaves_le_pow_height_sub_one {b : ℕ} {t : RoseTree α}
    (ht : t.Licensed fun _ ks ↦ ks.length ≤ b) : t.numLeaves ≤ b ^ (t.height - 1) := by
  induction ht using Licensed.induction with
  | node a cs hb _ ih =>
    rcases eq_or_ne cs [] with rfl | hne
    · simp
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hne
    have hlt d (hd : d ∈ cs) : d.height < (node a cs).height := height_lt_of_mem (t := node a cs) hd
    have hb : cs.length ≤ b := by simpa using hb
    have hd d (hd : d ∈ cs) : d.numLeaves ≤ b ^ ((node a cs).height - 2) :=
      (ih d hd).trans (Nat.pow_le_pow_right ((List.length_pos_of_mem hc).trans_le hb)
        (by have := hlt d hd; omega))
    have := hlt c hc
    have := height_pos c
    rw [numLeaves_node_of_ne_nil a hne]
    calc (cs.map numLeaves).sum ≤ cs.length * b ^ ((node a cs).height - 2) := by
          simpa using List.sum_le_length_nsmul _ _ (List.forall_mem_map.2 hd)
      _ ≤ b * b ^ ((node a cs).height - 2) := Nat.mul_le_mul_right _ hb
      _ = b ^ ((node a cs).height - 1) := by rw [← Nat.pow_succ']; congr 1; omega

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
      have hval : (c.replaceAt p new).value = c.value := value_replaceAt hcs hv
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
theorem Perm.licensed_iff (hR : ∀ a {ks ls : List α}, ks.Perm ls → (R a ks ↔ R a ls))
    {t s : RoseTree α} (h : t.Perm s) : t.Licensed R ↔ s.Licensed R := by
  induction t generalizing s with
  | node a cs ih =>
    obtain ⟨b, ds⟩ := s
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

/-- A relation licenses a relabelled tree when its pullback along the relabelling licenses the
tree. -/
@[simp] theorem licensed_map {β : Type*} {f : α → β} {R : β → List β → Prop} {t : RoseTree α} :
    (map f t).Licensed R ↔ t.Licensed fun a ks ↦ R (f a) (ks.map f) := by
  induction t with
  | node a cs ih =>
    rw [map_node, licensed_node_iff, licensed_node_iff, List.map_map,
      show value ∘ map f = f ∘ value from funext fun c ↦ value_map f c, ← List.map_map,
      List.forall_mem_map]
    exact and_congr_right fun _ ↦ forall₂_congr fun c hc ↦ ih c hc

end RoseTree
