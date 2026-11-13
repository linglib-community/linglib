/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.UnorderedTree.Licensed
public import Linglib.Core.Data.UnorderedTree.Prune

/-!
# Pruning the trunk of an admissible cut

Let `b` label exactly the vertices of a tree that have children. An admissible cut that removes
every child of a vertex leaves it childless in the trunk, a vertex labelled `b` that is not a leaf
of the tree. Pruning the trunk to the vertices above one not labelled `b` removes those, and then
the leaves of the tree are
[those of the crown and of the pruned trunk](##admissibleCuts_leaves_prune).
In a tree whose vertices have no child or two, a cut that extracts at most one tree
[leaves nothing to prune](##admissibleCuts_prune_eq_some).

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*} [DecidableEq α] (b : α)

private theorem rootCuts_leaveNothing_leaves_prune (t : RoseTree α)
    (ht : t.Licensed fun a ks ↦ (a = b ↔ (ks : Multiset α) ≠ 0)) :
    ∀ p ∈ rootCuts leaveNothing t, t.leaves =
      (p.1.map RoseTree.leaves).sum + ((p.2.prune (· ≠ b)).elim 0 RoseTree.leaves) := fun p hp ↦ by
  have h := rootCuts_induction leaveNothing
    (P := fun cs q ↦ (∀ c ∈ cs, c.Licensed fun a ks ↦ (a = b ↔ (ks : Multiset α) ≠ 0)) →
      (cs.map RoseTree.leaves).sum = (q.1.map RoseTree.leaves).sum +
        ((q.2.filterMap (RoseTree.prune (· ≠ b))).map RoseTree.leaves).sum)
    (fun _ ↦ by simp)
    (fun _ _ h _ ↦ by cases h; simp)
    (fun a cs ⟨crown, rest⟩ hq hP hL ↦ by
      have ht := hL _ (List.mem_singleton_self _)
      have ih := hP fun _ hc ↦ ht.of_mem hc
      have hroot : a = b ↔ cs ≠ [] := by simpa using ht.rel_root
      rcases eq_or_ne cs [] with rfl | hcs
      · rw [childrenCuts_nil, Multiset.mem_singleton] at hq
        cases hq
        have hab : a ≠ b := fun h ↦ (hroot.1 h) rfl
        simp [RoseTree.prune_node, hab]
      · obtain rfl := hroot.2 hcs
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          RoseTree.leaves_node_of_ne_nil _ hcs] at ih ⊢
        rcases eq_or_ne (rest.filterMap (RoseTree.prune (· ≠ a))) [] with hr | hr
        · simp [RoseTree.prune_node, hr] at ih ⊢
          exact ih
        · simp [RoseTree.prune_node, hr, RoseTree.leaves_node_of_ne_nil _ hr]
          exact ih)
    (fun _ _ _ _ _ _ ha hb hL ↦ by
      have h₁ := ha fun c hc ↦ hL c (List.mem_cons.mpr (.inl (List.mem_singleton.mp hc)))
      have h₂ := hb fun c hc ↦ hL c (List.mem_cons_of_mem _ hc)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Multiset.map_add, Multiset.sum_add, List.filterMap_append, List.map_append,
        List.sum_append] at h₁ h₂ ⊢
      rw [h₁, h₂]
      exact add_add_add_comm _ _ _ _)
    t p hp (by simpa using ht)
  cases hpr : p.2.prune (· ≠ b) <;> simpa [hpr] using h

/-- When `b` labels exactly the vertices with children, the leaves of a tree are those of the
crown of an admissible cut and of its trunk pruned to the vertices above one not labelled `b`. -/
theorem admissibleCuts_leaves_prune {T : UnorderedTree α}
    (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0))
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ admissibleCuts T) :
    T.leaves = (p.1.map UnorderedTree.leaves).sum +
      ((p.2.prune (· ≠ b)).elim 0 UnorderedTree.leaves) := by
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, admissibleCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := rootCuts_leaveNothing_leaves_prune b t hT q hq
    cases hpr : q.2.prune (· ≠ b) <;>
      simpa [projCut, hpr, Multiset.map_map, Function.comp_def] using h

omit [DecidableEq α] in
private theorem mem_sum_map_leaves {x : α} :
    ∀ {l : List (RoseTree α)}, x ∈ (l.map RoseTree.leaves).sum → ∃ c ∈ l, x ∈ c.leaves
  | [], h => by simp at h
  | c :: l, h => by
    rw [List.map_cons, List.sum_cons, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨d, hd, hx⟩ := mem_sum_map_leaves h
      exact ⟨d, List.mem_cons_of_mem _ hd, hx⟩

omit [DecidableEq α] in
/-- When `b` labels exactly the vertices with children, no leaf is labelled `b`. -/
theorem ne_of_mem_leaves {T : UnorderedTree α} (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0)) :
    ∀ x ∈ T.leaves, x ≠ b := by
  induction T using Quotient.inductionOn with
  | h t =>
    change t.Licensed fun a ks ↦ (a = b ↔ (ks : Multiset α) ≠ 0) at hT
    change ∀ x ∈ t.leaves, x ≠ b
    induction hT using RoseTree.Licensed.induction with
    | node a cs hR _ ih =>
      intro x hx
      rcases cs with _ | ⟨c, cs⟩
      · obtain rfl : x = a := by simpa using hx
        exact fun h ↦ (hR.1 h) (by simp)
      · rw [RoseTree.leaves_node_cons] at hx
        obtain ⟨d, hd, hxd⟩ := mem_sum_map_leaves hx
        exact ih d hd x hxd

omit [DecidableEq α] in
private theorem rootCuts_leaveNothing_leaves_ne (t : RoseTree α)
    (ht : t.Licensed fun a ks ↦ (a = b ↔ (ks : Multiset α) ≠ 0) ∧
      (Multiset.card (ks : Multiset α) = 0 ∨ Multiset.card (ks : Multiset α) = 2)) :
    ∀ p ∈ rootCuts leaveNothing t, Multiset.card p.1 ≤ 1 → ∀ x ∈ p.2.leaves, x ≠ b :=
  fun p hp hcard ↦ by
  have h := rootCuts_induction leaveNothing
    (P := fun cs q ↦ (∀ c ∈ cs, c.Licensed fun a ks ↦ (a = b ↔ (ks : Multiset α) ≠ 0) ∧
        (Multiset.card (ks : Multiset α) = 0 ∨ Multiset.card (ks : Multiset α) = 2)) →
      Multiset.card q.1 ≤ 1 →
        (∀ c ∈ q.2, ∀ x ∈ c.leaves, x ≠ b) ∧ cs.length ≤ q.2.length + Multiset.card q.1)
    (fun _ _ ↦ ⟨by simp, by simp⟩)
    (fun _ _ h _ _ ↦ by cases h; exact ⟨by simp, by simp⟩)
    (fun a cs ⟨crown, rest⟩ hq hP hL hk ↦ by
      have ht := hL _ (List.mem_singleton_self _)
      obtain ⟨ih₁, ih₂⟩ := hP (fun _ hc ↦ ht.of_mem hc) hk
      obtain ⟨hroot, hbin⟩ := ht.rel_root
      refine ⟨fun c hc x hx ↦ ?_, by simp⟩
      obtain rfl := List.mem_singleton.mp hc
      rcases eq_or_ne cs [] with rfl | hcs
      · rw [childrenCuts_nil, Multiset.mem_singleton] at hq
        cases hq
        obtain rfl : x = a := by simpa using hx
        exact fun h ↦ (hroot.1 h) (by simp)
      · have hlen : cs.length = 2 := by
          rcases hbin with h | h
          · exact absurd (List.length_eq_zero_iff.mp (by simpa using h)) hcs
          · simpa using h
        have hcrown : Multiset.card crown ≤ 1 := hk
        have hrest : rest ≠ [] := fun h ↦ by
          simp only [h, List.length_nil, zero_add] at ih₂
          omega
        rw [RoseTree.leaves_node_of_ne_nil _ hrest] at hx
        obtain ⟨c, hc, hxc⟩ := mem_sum_map_leaves hx
        exact ih₁ c hc x hxc)
    (fun _ _ _ _ _ _ ha hb hL hc ↦ by
      rw [Multiset.card_add] at hc
      obtain ⟨a₁, a₂⟩ := ha (fun c hc ↦ hL c (List.mem_cons.mpr (.inl (List.mem_singleton.mp hc))))
        (by omega)
      obtain ⟨b₁, b₂⟩ := hb (fun c hc ↦ hL c (List.mem_cons_of_mem _ hc)) (by omega)
      refine ⟨fun c hc ↦ (List.mem_append.mp hc).elim (a₁ c) (b₁ c), ?_⟩
      simp only [List.length_cons, List.length_nil, List.length_append, Multiset.card_add] at *
      omega)
    t p hp (by simpa using ht) hcard
  exact h.1 p.2 (List.mem_singleton_self _)

/-- In a tree whose vertices have no child or two, with `b` labelling those with two, an
admissible cut that extracts at most one tree leaves a trunk with nothing to prune. -/
theorem admissibleCuts_prune_eq_some {T : UnorderedTree α}
    (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0) ∧
      (Multiset.card ks = 0 ∨ Multiset.card ks = 2))
    {p : Multiset (UnorderedTree α) × UnorderedTree α} (hp : p ∈ admissibleCuts T)
    (h : Multiset.card p.1 ≤ 1) : p.2.prune (· ≠ b) = some p.2 := by
  refine UnorderedTree.prune_eq_some_self _ ?_
  induction T using Quotient.inductionOn with
  | h t =>
    rw [UnorderedTree.quot_mk_eq_mk, admissibleCuts_mk] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact rootCuts_leaveNothing_leaves_ne b t hT q hq (by simpa [projCut] using h)

end ConnesKreimer
