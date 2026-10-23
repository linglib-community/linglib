/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Crown
public import Linglib.Core.Data.Multiset.Bind
public import Linglib.Core.Data.UnorderedTree.Replace
public import Linglib.Core.Data.UnorderedTree.Subtree

/-!
# Single cuts as substitution

Under an extraction policy that replaces every copy of a subtree `M` by one tree of class `R`,
the cuts of `t` with crown `{M}` match the occurrences of `M` below the root. When `M` occurs
exactly once there, there is exactly one such cut, and its trunk is `t` with `M` replaced by `R`.

## Main results

* `ConnesKreimer.map_trunk_filter_cutSummandsG`: the single cut extracting a subtree that occurs
  once, with trunk the substitution.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

variable {γ : Type*}

/-! ### Substitution of a subtree that does not occur -/

section Replace

variable [DecidableEq γ] {M R : UnorderedTree γ}

mutual

theorem unorderedReplace_of_count_eq_zero :
    ∀ (t : RoseTree γ), (unorderedSubtrees t).count M = 0 →
      unorderedReplace M R t = UnorderedTree.mk t
  | .node a cs, h => by
    rw [unorderedSubtrees, Multiset.count_cons, Nat.add_eq_zero_iff] at h
    rw [unorderedReplace, ite_eq_right (by rintro rfl; simp at h),
      unorderedReplaceList_of_count_eq_zero cs h.1, node_mk_tree_list]

theorem unorderedReplaceList_of_count_eq_zero :
    ∀ (cs : List (RoseTree γ)), (unorderedSubtreesList cs).count M = 0 →
      unorderedReplaceList M R cs = (cs.map UnorderedTree.mk : Multiset (UnorderedTree γ))
  | [], _ => rfl
  | c :: cs, h => by
    rw [unorderedSubtreesList, Multiset.count_add, Nat.add_eq_zero_iff] at h
    rw [unorderedReplaceList, unorderedReplace_of_count_eq_zero c h.1,
      unorderedReplaceList_of_count_eq_zero cs h.2, List.map_cons, Multiset.cons_coe]

end

end Replace

/-! ### The single cut extracting a subtree that occurs once -/

section Single

variable [DecidableEq γ] (E : RoseTree γ → Option (List (RoseTree γ))) {M R : UnorderedTree γ}

private theorem add_eq_singleton_iff {δ : Type*} {s t : Multiset δ} {a : δ} :
    s + t = {a} ↔ s = {a} ∧ t = 0 ∨ s = 0 ∧ t = {a} := by
  constructor
  · intro h
    have hc := congrArg Multiset.card h
    rw [Multiset.card_add, Multiset.card_singleton] at hc
    rcases Nat.add_eq_one_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [Multiset.card_eq_zero] at h1
      subst h1
      exact .inr ⟨rfl, by simpa using h⟩
    · rw [Multiset.card_eq_zero] at h2
      subst h2
      exact .inl ⟨by simpa using h, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem crown_ne_of_mem_cutListSummandsG {cs : List (RoseTree γ)}
    (h : (unorderedSubtreesList cs).count M = 0) {q : Multiset (RoseTree γ) × List (RoseTree γ)}
    (hq : q ∈ cutListSummandsG E cs) : q.1.map UnorderedTree.mk ≠ {M} := fun hc ↦ by
  obtain ⟨x, hx, hxM⟩ := Multiset.mem_map.mp (hc ▸ Multiset.mem_singleton_self M)
  exact Multiset.count_eq_zero.mp h (hxM ▸ mk_mem_of_mem_crown_cutListSummandsG E cs q hq x hx)

theorem crown_ne_of_mem_augActionG {t : RoseTree γ} (h : (unorderedSubtrees t).count M = 0)
    {a : Multiset (RoseTree γ) × List (RoseTree γ)} (ha : a ∈ augActionG E t) :
    a.1.map UnorderedTree.mk ≠ {M} := fun hc ↦ by
  obtain ⟨x, hx, hxM⟩ := Multiset.mem_map.mp (hc ▸ Multiset.mem_singleton_self M)
  exact Multiset.count_eq_zero.mp h (hxM ▸ mk_mem_of_mem_crown_augActionG E t a ha x hx)

theorem crown_ne_of_mem_cutSummandsG {t : RoseTree γ}
    (h : (unorderedSubtreesList t.children).count M = 0)
    {p : Multiset (RoseTree γ) × RoseTree γ} (hp : p ∈ cutSummandsG E t) :
    p.1.map UnorderedTree.mk ≠ {M} := fun hc ↦ by
  obtain ⟨x, hx, hxM⟩ := Multiset.mem_map.mp (hc ▸ Multiset.mem_singleton_self M)
  exact Multiset.count_eq_zero.mp h (hxM ▸ mk_mem_of_mem_crown_cutSummandsG E t p hp x hx)

mutual

/-- When `M` occurs exactly once below the root of `t`, one cut of `t` has crown `{M}`, and its
    trunk is `t` with `M` replaced by `R`. -/
theorem map_trunk_filter_cutSummandsG
    (hE : ∀ s, UnorderedTree.mk s = M → ∃ ρ, E s = some [ρ] ∧ UnorderedTree.mk ρ = R) :
    ∀ (t : RoseTree γ), (unorderedSubtreesList t.children).count M = 1 →
      UnorderedTree.mk t ≠ M →
      ((cutSummandsG E t).filter (fun p ↦ p.1.map UnorderedTree.mk = {M})).map
          (fun p ↦ UnorderedTree.mk p.2) = {unorderedReplace M R t}
  | .node a cs, h, hne => by
    rw [cutSummandsG_node, Multiset.filter_map, Multiset.map_map, unorderedReplace,
      ite_eq_right hne, ← Multiset.map_singleton (UnorderedTree.node a),
      ← map_trunk_filter_cutListSummandsG hE cs h, Multiset.map_map]
    exact Multiset.map_congr (Multiset.filter_congr fun _ _ ↦ Iff.rfl)
      fun q _ ↦ (node_mk_tree_list a q.2).symm

theorem map_trunk_filter_cutListSummandsG
    (hE : ∀ s, UnorderedTree.mk s = M → ∃ ρ, E s = some [ρ] ∧ UnorderedTree.mk ρ = R) :
    ∀ (cs : List (RoseTree γ)), (unorderedSubtreesList cs).count M = 1 →
      ((cutListSummandsG E cs).filter (fun q ↦ q.1.map UnorderedTree.mk = {M})).map
          (fun q ↦ (q.2.map UnorderedTree.mk : Multiset (UnorderedTree γ)))
        = {unorderedReplaceList M R cs}
  | [], h => by simp [unorderedSubtreesList] at h
  | c :: cs, h => by
    rw [unorderedSubtreesList, Multiset.count_add] at h
    rw [cutListSummandsG_cons, Multiset.filter_map, Multiset.map_map, unorderedReplaceList]
    simp only [Function.comp_def, Multiset.map_add]
    rcases Nat.add_eq_one_iff.mp h with ⟨hc, hcs⟩ | ⟨hc, hcs⟩
    · -- `M` occurs in the tail, and the head is kept whole.
      rw [Multiset.filter_congr
          (q := fun pr ↦ pr.1.1.card = 0 ∧ pr.2.1.map UnorderedTree.mk = {M}) ?_,
        Multiset.filter_product
          (fun q : Multiset (RoseTree γ) × List (RoseTree γ) ↦ q.1.card = 0)
          (fun q : Multiset (RoseTree γ) × List (RoseTree γ) ↦ q.1.map UnorderedTree.mk = {M}),
        augActionG_filter_empty, ← Multiset.cons_zero ((0 : Multiset (RoseTree γ)), [c]),
        Multiset.cons_product, Multiset.zero_product, add_zero, Multiset.map_map,
        unorderedReplace_of_count_eq_zero c hc,
        ← Multiset.map_singleton (fun s ↦ UnorderedTree.mk c ::ₘ s),
        ← map_trunk_filter_cutListSummandsG hE cs hcs, Multiset.map_map]
      · exact Multiset.map_congr rfl fun q _ ↦ by simp
      · intro pr hpr
        have hx := crown_ne_of_mem_augActionG E hc (Multiset.mem_product.mp hpr).1
        simp only [add_eq_singleton_iff, Multiset.map_eq_zero, Multiset.card_eq_zero]
        exact ⟨fun h ↦ h.resolve_left fun h' ↦ hx h'.1, .inr⟩
    · -- `M` occurs in the head, and the tail is kept whole.
      rw [Multiset.filter_congr
          (q := fun pr ↦ pr.1.1.map UnorderedTree.mk = {M} ∧ pr.2.1.card = 0) ?_,
        Multiset.filter_product
          (fun q : Multiset (RoseTree γ) × List (RoseTree γ) ↦ q.1.map UnorderedTree.mk = {M})
          (fun q : Multiset (RoseTree γ) × List (RoseTree γ) ↦ q.1.card = 0),
        cutListSummandsG_filter_empty, ← Multiset.cons_zero ((0 : Multiset (RoseTree γ)), cs),
        Multiset.product_cons, Multiset.product_zero, add_zero, Multiset.map_map,
        unorderedReplaceList_of_count_eq_zero cs hcs, ← Multiset.singleton_add,
        ← Multiset.map_singleton
          (fun s : Multiset (UnorderedTree γ) ↦ s + ↑(cs.map UnorderedTree.mk)),
        ← map_trunk_filter_augActionG hE c hc, Multiset.map_map]
      · exact Multiset.map_congr rfl fun q _ ↦ by simp
      · intro pr hpr
        have hx := crown_ne_of_mem_cutListSummandsG E hcs (Multiset.mem_product.mp hpr).2
        simp only [add_eq_singleton_iff, Multiset.map_eq_zero, Multiset.card_eq_zero]
        exact ⟨fun h ↦ h.resolve_right fun h' ↦ hx h'.2, .inl⟩

theorem map_trunk_filter_augActionG
    (hE : ∀ s, UnorderedTree.mk s = M → ∃ ρ, E s = some [ρ] ∧ UnorderedTree.mk ρ = R) :
    ∀ (t : RoseTree γ), (unorderedSubtrees t).count M = 1 →
      ((augActionG E t).filter (fun q ↦ q.1.map UnorderedTree.mk = {M})).map
          (fun q ↦ (q.2.map UnorderedTree.mk : Multiset (UnorderedTree γ)))
        = {{unorderedReplace M R t}}
  | .node b cs, h => by
    rw [unorderedSubtrees, Multiset.count_cons] at h
    rw [augActionG_eq, Multiset.filter_add, Multiset.map_add, Multiset.filter_map,
      Multiset.map_map]
    simp only [Function.comp_def]
    by_cases hM : UnorderedTree.mk (RoseTree.node b cs) = M
    · -- The extraction of `t` itself.
      rw [ite_eq_left hM.symm] at h
      obtain ⟨ρ, hρ, hρR⟩ := hE _ hM
      have h0 : (unorderedSubtreesList cs).count M = 0 := by omega
      rw [Multiset.filter_eq_nil.mpr fun p hp ↦
          crown_ne_of_mem_cutSummandsG E (t := .node b cs) h0 hp,
        Multiset.map_zero, add_zero, unorderedReplace, ite_eq_left hM]
      simp only [hρ]
      rw [Multiset.filter_singleton, ite_eq_left (by rw [Multiset.map_singleton, hM]),
        Multiset.map_singleton]
      simp [hρR]
    · -- A cut below the root of `t`.
      rw [ite_eq_right (Ne.symm hM), add_zero] at h
      rw [Multiset.filter_eq_nil.mpr, Multiset.map_zero, zero_add,
        ← Multiset.map_singleton (fun x ↦ ({x} : Multiset (UnorderedTree γ))),
        ← map_trunk_filter_cutSummandsG hE (.node b cs) h hM, Multiset.map_map]
      · rfl
      · intro q hq
        cases hEt : E (.node b cs) with
        | none => rw [hEt] at hq; exact absurd hq (Multiset.notMem_zero q)
        | some r =>
          rw [hEt] at hq
          obtain rfl := Multiset.mem_singleton.mp hq
          simpa using hM

end

end Single

end ConnesKreimer
