/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Core.Data.UnorderedTree.Subtree

/-!
# Crowns of cuts

A cut removes subtrees hanging below the root, so every crown component of a cut of `T` is a
proper subtree of `T`, and one at which the policy allows a cut. For a policy that allows a cut at
every subtree the converse holds, since any one subtree below the root is removed by the cut at
its own edge. Hence, for the pruning cuts, `X` is not a subtree of `T` exactly when `T ≠ X` and no
cut of `T` has `X` in its crown.

## Main results

* `ConnesKreimer.mk_mem_of_mem_crown_cutSummandsG`: crown components are proper subtrees.
* `ConnesKreimer.isSome_of_mem_crown_cutSummandsG`: crown components are cut where the policy
  allows.
* `ConnesKreimer.exists_mem_crown_cutSummandsN_iff`: the crown components of the pruning cuts are
  exactly the proper subtrees.
* `ConnesKreimer.not_mem_subtrees_iff`: `X ∉ T.subtrees ↔ T ≠ X ∧ ∀ p ∈ cutSummandsN T, X ∉ p.1`.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {α : Type*} (extract : RoseTree α → Option (List (RoseTree α)))

/-! ### Crown components are proper subtrees -/

/-- Every crown component of a cut of a list of children is a subtree of one of them. -/
theorem mk_mem_of_mem_crown_cutListSummandsG :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsG extract cs, ∀ x ∈ q.1,
      UnorderedTree.mk x ∈ unorderedSubtreesList cs :=
  cutListSummandsG_induction extract
    (P := fun cs q ↦ ∀ x ∈ q.1, UnorderedTree.mk x ∈ unorderedSubtreesList cs) (by simp)
    (fun t _ _ x hx ↦ by
      obtain ⟨_, _⟩ := t
      simp_all [unorderedSubtreesList, unorderedSubtrees])
    (fun _ _ _ _ h x hx ↦ by
      simp only [unorderedSubtreesList, unorderedSubtrees, Multiset.mem_add, Multiset.mem_cons]
      exact .inl (.inr (h x hx)))
    (fun _ _ _ _ _ _ ha hb x hx ↦ by
      rw [unorderedSubtreesList, Multiset.mem_add]
      exact (Multiset.mem_add.mp hx).imp (by simpa [unorderedSubtreesList] using ha x) (hb x))

theorem mk_mem_of_mem_crown_augActionG (t : RoseTree α) :
    ∀ a ∈ augActionG extract t, ∀ x ∈ a.1, UnorderedTree.mk x ∈ unorderedSubtrees t := by
  simpa [unorderedSubtreesList] using mk_mem_of_mem_crown_cutListSummandsG extract [t]

/-- Every crown component of a cut of `t` is a subtree of a child of `t`. -/
theorem mk_mem_of_mem_crown_cutSummandsG :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsG extract t, ∀ x ∈ p.1,
      UnorderedTree.mk x ∈ unorderedSubtreesList t.children
  | .node a cs, p, hp => by
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    exact mk_mem_of_mem_crown_cutListSummandsG extract cs q hq

/-- Every crown component of a cut is a subtree at which the policy allows a cut. -/
theorem isSome_of_mem_crown_cutSummandsG (t : RoseTree α) :
    ∀ p ∈ cutSummandsG extract t, ∀ x ∈ p.1, (extract x).isSome :=
  fun p hp ↦ cutSummandsG_induction extract (P := fun _ q ↦ ∀ x ∈ q.1, (extract x).isSome)
    (by simp) (fun _ _ h x hx ↦ by simp_all) (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ _ ha hb x hx ↦ (Multiset.mem_add.mp hx).elim (ha x) (hb x)) t p hp

/-! ### Every proper subtree is a crown component

This needs a policy that allows a cut at every subtree. -/

theorem zero_mem_cutSummandsG (t : RoseTree α) :
    ((0 : Multiset (RoseTree α)), t) ∈ cutSummandsG extract t :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((cutSummandsG_filter_empty extract t).symm ▸ Multiset.mem_singleton_self _)

theorem zero_mem_cutListSummandsG (cs : List (RoseTree α)) :
    ((0 : Multiset (RoseTree α)), cs) ∈ cutListSummandsG extract cs :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((cutListSummandsG_filter_empty extract cs).symm ▸ Multiset.mem_singleton_self _)

theorem zero_mem_augActionG (t : RoseTree α) :
    ((0 : Multiset (RoseTree α)), [t]) ∈ augActionG extract t :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1.card = 0)
    ((augActionG_filter_empty extract t).symm ▸ Multiset.mem_singleton_self _)

variable {extract}

mutual

theorem exists_mem_crown_cutSummandsG (hex : ∀ t, (extract t).isSome) :
    ∀ (t : RoseTree α) (s : UnorderedTree α), s ∈ unorderedSubtreesList t.children →
      ∃ p ∈ cutSummandsG extract t, ∃ x ∈ p.1, UnorderedTree.mk x = s
  | .node a cs => fun s hs ↦ by
    obtain ⟨q, hq, x, hx, rfl⟩ := exists_mem_crown_cutListSummandsG hex cs s hs
    exact ⟨(q.1, .node a q.2), by rw [cutSummandsG_node]; exact Multiset.mem_map_of_mem _ hq,
      x, hx, rfl⟩

theorem exists_mem_crown_cutListSummandsG (hex : ∀ t, (extract t).isSome) :
    ∀ (cs : List (RoseTree α)) (s : UnorderedTree α), s ∈ unorderedSubtreesList cs →
      ∃ q ∈ cutListSummandsG extract cs, ∃ x ∈ q.1, UnorderedTree.mk x = s
  | [] => fun s hs ↦ absurd hs (Multiset.notMem_zero s)
  | t :: ts => fun s hs ↦ by
    rw [unorderedSubtreesList, Multiset.mem_add] at hs
    rw [cutListSummandsG_cons]
    rcases hs with hs | hs
    · obtain ⟨a, ha, x, hx, rfl⟩ := exists_mem_crown_augActionG hex t s hs
      exact ⟨_, Multiset.mem_map_of_mem _ (a := (a, (0, ts)))
        (Multiset.mem_product.mpr ⟨ha, zero_mem_cutListSummandsG extract ts⟩),
        x, Multiset.mem_add.mpr (.inl hx), rfl⟩
    · obtain ⟨q, hq, x, hx, rfl⟩ := exists_mem_crown_cutListSummandsG hex ts s hs
      exact ⟨_, Multiset.mem_map_of_mem _ (a := ((0, [t]), q))
        (Multiset.mem_product.mpr ⟨zero_mem_augActionG extract t, hq⟩),
        x, Multiset.mem_add.mpr (.inr hx), rfl⟩

theorem exists_mem_crown_augActionG (hex : ∀ t, (extract t).isSome) :
    ∀ (t : RoseTree α) (s : UnorderedTree α), s ∈ unorderedSubtrees t →
      ∃ a ∈ augActionG extract t, ∃ x ∈ a.1, UnorderedTree.mk x = s
  | .node b cs => fun s hs ↦ by
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hex (.node b cs))
    rw [unorderedSubtrees, Multiset.mem_cons] at hs
    rw [augActionG_eq_some extract _ r hr]
    rcases hs with rfl | hs
    · exact ⟨_, Multiset.mem_cons_self _ _, _, Multiset.mem_singleton_self _, rfl⟩
    · obtain ⟨p, hp, x, hx, rfl⟩ := exists_mem_crown_cutSummandsG hex (.node b cs) s hs
      exact ⟨(p.1, [p.2]), Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hp), x, hx, rfl⟩

end

/-- The crown components of the pruning cuts of `T` are exactly its proper subtrees. -/
theorem exists_mem_crown_cutSummandsN_iff {T X : UnorderedTree α} :
    (∃ p ∈ cutSummandsN T, X ∈ p.1) ↔ X ∈ T.subtrees ∧ X ≠ T := by
  induction T using Quotient.inductionOn with
  | h t =>
    obtain ⟨a, cs⟩ := t
    rw [quot_mk_eq_mk, subtrees_mk, unorderedSubtrees, Multiset.mem_cons]
    constructor
    · rintro ⟨p, hp, hX⟩
      refine ⟨.inr ?_, fun h ↦ cutSummandsN_self_not_mem_crown _ p hp (h ▸ hX)⟩
      rw [cutSummandsN_mk] at hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hX
      simpa using mk_mem_of_mem_crown_cutSummandsG pruning _ q hq x hx
    · rintro ⟨hX | hX, hne⟩
      · exact absurd hX hne
      · obtain ⟨p, hp, x, hx, rfl⟩ :=
          exists_mem_crown_cutSummandsG (extract := pruning) (fun _ ↦ rfl) (.node a cs) _ hX
        exact ⟨projSummand p, by rw [cutSummandsN_mk]; exact Multiset.mem_map_of_mem _ hp,
          Multiset.mem_map_of_mem _ hx⟩

/-- `X` is not a subtree of `T` exactly when `T ≠ X` and no pruning cut of `T` has `X` in its
crown. -/
theorem not_mem_subtrees_iff {T X : UnorderedTree α} :
    X ∉ T.subtrees ↔ T ≠ X ∧ ∀ p ∈ cutSummandsN T, X ∉ p.1 := by
  constructor
  · intro h
    refine ⟨fun hTX ↦ h (hTX ▸ T.self_mem_subtrees), fun p hp hX ↦ h ?_⟩
    exact (exists_mem_crown_cutSummandsN_iff.mp ⟨p, hp, hX⟩).1
  · rintro ⟨hne, hcut⟩ hX
    by_cases hXT : X = T
    · exact hne hXT.symm
    · obtain ⟨p, hp, hXp⟩ := exists_mem_crown_cutSummandsN_iff.mpr ⟨hX, hXT⟩
      exact hcut p hp hXp

end ConnesKreimer
