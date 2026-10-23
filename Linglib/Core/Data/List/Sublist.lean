/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Nodup

/-!
# Sublists across a block of one symbol, and pair sublists as positional order

Two additions to the `List.Sublist` API.

* Stripping an unmatched edge. A list whose head is not `a` is a sublist of `a :: r` exactly when
  it is a sublist of `r` (`List.sublist_cons_iff_of_head?_ne`, the `Iff` form of
  `List.Sublist.of_cons_of_ne`), hence also across a left block `replicate m a` or a right block
  `replicate n b` (`List.sublist_replicate_append_iff_of_head?_ne`,
  `List.sublist_append_replicate_iff_of_getLast?_ne`). [UPSTREAM] candidates beside
  `List.sublist_cons_iff`.
* Pair sublists as positional order. On a `Nodup` list, `[a, b] <+ l` says exactly that `a` and
  `b` are members with `a` at a strictly earlier index (`List.pair_sublist_iff_idxOf_lt`): the
  pair-sublist relation is the strict linear order a duplicate-free list carries. It is
  transitive (`List.Nodup.pair_sublist_trans`), so it is a strict order on the whole type
  (`List.Nodup.isStrictOrder_pair_sublist`) in which elements off the list are related to
  nothing; two distinct members are ordered one way or the other
  (`List.pair_sublist_or_pair_sublist`), and a duplicate-free list whose members lie in another,
  each pair in the same order there, is a sublist of it (`List.sublist_of_forall_pair_sublist`).
-/

@[expose] public section

namespace List

variable {α : Type*} {a b : α} {l p q : List α}

section Replicate

variable {r : List α} {m n : ℕ}

theorem sublist_cons_iff_of_head?_ne (h : l.head? ≠ some a) : l <+ a :: r ↔ l <+ r := by
  rw [sublist_cons_iff]
  exact ⟨fun h' ↦ h'.resolve_right fun ⟨t, ht, _⟩ ↦ h (by simp [ht]), Or.inl⟩

theorem sublist_replicate_append_iff_of_head?_ne (h : l.head? ≠ some a) :
    l <+ replicate m a ++ r ↔ l <+ r := by
  induction m with
  | zero => simp
  | succ m ih => rw [replicate_succ, cons_append, sublist_cons_iff_of_head?_ne h, ih]

theorem sublist_append_replicate_iff_of_getLast?_ne (h : l.getLast? ≠ some b) :
    l <+ r ++ replicate n b ↔ l <+ r := by
  rw [← reverse_sublist, reverse_append, reverse_replicate,
    sublist_replicate_append_iff_of_head?_ne (by simpa), reverse_sublist]

end Replicate

theorem Nodup.pair_sublist_trans {c : α} (hl : l.Nodup) (hab : [a, b] <+ l)
    (hbc : [b, c] <+ l) : [a, c] <+ l := by
  induction l with
  | nil => simp at hab
  | cons x t ih =>
    rw [nodup_cons] at hl
    rcases cons_sublist_cons'.1 hab with hab' | ⟨rfl, hb⟩ <;>
      rcases cons_sublist_cons'.1 hbc with hbc' | ⟨rfl, hc⟩
    · exact (ih hl.2 hab' hbc').cons x
    · exact absurd (hab'.subset (by simp)) hl.1
    · exact (singleton_sublist.2 (hbc'.subset (by simp))).cons_cons a
    · exact absurd (hb.subset (by simp)) hl.1

theorem Nodup.isStrictOrder_pair_sublist (hl : l.Nodup) :
    IsStrictOrder α fun a b ↦ [a, b] <+ l where
  irrefl a := nodup_iff_sublist.1 hl a
  trans _ _ _ := hl.pair_sublist_trans

theorem sublist_of_forall_pair_sublist (hp : p.Nodup) (hq : q.Nodup) (hpq : p ⊆ q)
    (h : ∀ a b, [a, b] <+ p → [a, b] <+ q) : p <+ q := by
  induction q generalizing p with
  | nil => simp [eq_nil_of_subset_nil hpq]
  | cons x q ih =>
    rw [nodup_cons] at hq
    have hpair : ∀ a b, a ≠ x → [a, b] <+ x :: q → [a, b] <+ q := fun a b hax hab ↦
      (sublist_cons_iff_of_head?_ne (by simpa using hax)).1 hab
    by_cases hx : x ∈ p
    · obtain _ | ⟨y, p⟩ := p
      · simp at hx
      obtain rfl : y = x := by
        by_contra hyx
        have hxp : x ∈ p := (mem_cons.1 hx).resolve_left (Ne.symm hyx)
        exact hq.1 ((hpair y x hyx (h y x ((singleton_sublist.2 hxp).cons_cons y))).subset
          (by simp))
      rw [nodup_cons] at hp
      refine (ih hp.2 hq.2 (fun a ha ↦ ?_) fun a b hab ↦ ?_).cons_cons y
      · exact (mem_cons.1 (hpq (mem_cons_of_mem y ha))).resolve_left fun e ↦ hp.1 (e ▸ ha)
      · exact hpair a b (fun e ↦ hp.1 (e ▸ hab.subset (by simp))) (h a b (hab.cons y))
    · refine (ih hp hq.2 (fun a ha ↦ ?_) fun a b hab ↦ ?_).cons x
      · exact (mem_cons.1 (hpq ha)).resolve_left fun e ↦ hx (e ▸ ha)
      · exact hpair a b (fun e ↦ hx (e ▸ hab.subset (by simp))) (h a b hab)

variable [DecidableEq α]

theorem pair_sublist_of_idxOf_lt (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a < l.idxOf b) : [a, b] <+ l := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    by_cases hax : a = x
    · subst hax
      rcases mem_cons.mp hb with rfl | hb'
      · exact absurd h (Nat.lt_irrefl _)
      · exact (singleton_sublist.mpr hb').cons_cons a
    · have ha' : a ∈ xs := (mem_cons.mp ha).resolve_left hax
      have hbx : b ≠ x := by
        rintro rfl
        rw [idxOf_cons_self] at h
        exact Nat.not_lt_zero _ h
      have hb' : b ∈ xs := (mem_cons.mp hb).resolve_left hbx
      refine (ih ha' hb' ?_).cons x
      rw [idxOf_cons_ne _ (Ne.symm hax), idxOf_cons_ne _ (Ne.symm hbx)] at h
      exact Nat.lt_of_succ_lt_succ h

theorem idxOf_lt_of_pair_sublist (hnd : l.Nodup) (h : [a, b] <+ l) :
    l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [nodup_cons] at hnd
    obtain ⟨hx, hnd'⟩ := hnd
    cases h with
    | cons _ h' =>
      have ha : a ∈ xs := h'.subset (by simp)
      have hb : b ∈ xs := h'.subset (by simp)
      have hax : x ≠ a := by rintro rfl; exact hx ha
      have hbx : x ≠ b := by rintro rfl; exact hx hb
      rw [idxOf_cons_ne _ hax, idxOf_cons_ne _ hbx]
      exact Nat.succ_lt_succ (ih hnd' h')
    | cons_cons _ h' =>
      have hb : b ∈ xs := singleton_sublist.mp h'
      have hba : a ≠ b := by rintro rfl; exact hx hb
      rw [idxOf_cons_self, idxOf_cons_ne _ hba]
      exact Nat.succ_pos _

theorem pair_sublist_iff_idxOf_lt (hnd : l.Nodup) :
    [a, b] <+ l ↔ a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b :=
  ⟨fun h => ⟨h.subset (by simp), h.subset (by simp), idxOf_lt_of_pair_sublist hnd h⟩,
   fun ⟨ha, hb, hlt⟩ => pair_sublist_of_idxOf_lt ha hb hlt⟩

theorem pair_sublist_or_pair_sublist (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    [a, b] <+ l ∨ [b, a] <+ l := by
  rcases Nat.lt_or_gt_of_ne (mt (idxOf_inj ha).mp hab) with h | h
  · exact .inl (pair_sublist_of_idxOf_lt ha hb h)
  · exact .inr (pair_sublist_of_idxOf_lt hb ha h)

theorem IsInfix.mem_of_idxOf_le_of_le {m : List α} {z : α} (hm : m <:+: l) (hnd : l.Nodup)
    (ha : a ∈ m) (hb : b ∈ m) (hz : z ∈ l) (haz : l.idxOf a ≤ l.idxOf z)
    (hzb : l.idxOf z ≤ l.idxOf b) : z ∈ m := by
  obtain ⟨s, t, rfl⟩ := hm
  rw [nodup_append, nodup_append] at hnd
  obtain ⟨⟨_, _, hsm⟩, _, hst⟩ := hnd
  have has : a ∉ s := λ h => hsm a h a ha rfl
  have hbs : b ∉ s := λ h => hsm b h b hb rfl
  rw [idxOf_append_of_mem (mem_append_right _ ha), idxOf_append_of_notMem has] at haz
  rw [idxOf_append_of_mem (mem_append_right _ hb), idxOf_append_of_notMem hbs] at hzb
  rcases mem_append.mp hz with hzsm | hzt
  · rcases mem_append.mp hzsm with hzs | hzm
    · have := idxOf_lt_length_iff.mpr hzs
      rw [idxOf_append_of_mem hzsm, idxOf_append_of_mem hzs] at haz
      omega
    · exact hzm
  · have hzsm : z ∉ s ++ m := λ h => hst z h z hzt rfl
    have := idxOf_lt_length_iff.mpr hb
    rw [idxOf_append_of_notMem hzsm, length_append] at hzb
    omega

end List
