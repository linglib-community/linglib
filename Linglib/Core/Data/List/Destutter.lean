/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Destutter

/-!
# `List.destutter` and `++`

`Mathlib/Data/List/Destutter.lean` has no lemma relating `destutter` to `++`. The primitive is
the append decomposition `List.destutter'_append`: destuttering `l ++ m` from `a` destutters `l`
from `a` and then `m` from the last element kept. Destuttering the left operand first changes
nothing for any relation. When the negation of the relation is an equivalence, as for `(· ≠ ·)`,
the same holds on the right, so `destutter` is a congruence for `++`. [UPSTREAM] candidates for
that file.

## Main statements

* `List.head?_destutter`: `destutter` preserves the head.
* `List.destutter'_append`: the append decomposition.
* `List.destutter_append_left`, `List.destutter_append_right`: absorbing a `destutter` of either
  operand, so `List.destutter_append_destutter` makes `destutter` a congruence for `++`.
* `List.destutter_replicate`: a constant run fuses to one element.
* `List.IsChain.destutter_ne_append`: two `(· ≠ ·)`-chains concatenated and destuttered merge
  only at the seam.
-/

@[expose] public section

namespace List
variable {α : Type*} {R : α → α → Prop} [DecidableRel R] {a b : α} {l m : List α}

theorem head?_destutter' (a : α) (l : List α) : (l.destutter' R a).head? = some a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => by_cases h : R a b <;> simp [h, ih]

@[simp]
theorem head?_destutter (l : List α) : (l.destutter R).head? = l.head? := by
  cases l <;> simp [destutter_cons', head?_destutter']

theorem destutter'_eq_cons (a : α) (l : List α) : ∃ t, l.destutter' R a = a :: t :=
  ⟨_, (cons_head?_tail (head?_destutter' a l)).symm⟩

theorem getLastD_destutter' (a : α) (l : List α) (x y : α) :
    (l.destutter' R a).getLastD x = (l.destutter' R a).getLastD y := by
  obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a l
  rw [ht, getLastD_cons, getLastD_cons]

/-- Destuttering `l ++ m` from `a` destutters `l` from `a`, then `m` from the last element
kept. -/
theorem destutter'_append (a : α) (l m : List α) :
    (l ++ m).destutter' R a =
      l.destutter' R a ++ (m.destutter' R ((l.destutter' R a).getLastD a)).tail := by
  induction l generalizing a with
  | nil =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a m
    simp [ht]
  | cons b l ih =>
    by_cases h : R a b
    · rw [cons_append, destutter'_cons_pos (h := h), destutter'_cons_pos (h := h), ih b,
        cons_append, getLastD_cons, getLastD_destutter' b l a b]
    · rw [cons_append, destutter'_cons_neg (h := h), destutter'_cons_neg (h := h), ih a]

@[simp]
theorem destutter_append_left (l m : List α) :
    (l.destutter R ++ m).destutter R = (l ++ m).destutter R := by
  cases l with
  | nil => simp
  | cons a l =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) a l
    have hc : (a :: t).IsChain R := ht ▸ isChain_destutter' R l a
    rw [destutter_cons', ht, cons_append, destutter_cons', cons_append, destutter_cons',
      destutter'_append, destutter'_append, ht, destutter'_of_isChain_cons _ _ hc]

theorem destutter'_replicate (h : ¬R a a) (n : ℕ) : (replicate n a).destutter' R a = [a] := by
  induction n with
  | zero => rfl
  | succ m ih => rw [replicate_succ, destutter'_cons_neg _ h, ih]

theorem destutter_replicate (h : ¬R a a) (n : ℕ) : (replicate (n + 1) a).destutter R = [a] := by
  rw [replicate_succ, destutter_cons', destutter'_replicate h]

section IsEquiv
variable [IsEquiv α Rᶜ]

theorem tail_destutter'_congr (hab : ¬R a b) (l : List α) :
    (l.destutter' R a).tail = (l.destutter' R b).tail := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : Rᶜ a c ↔ Rᶜ b c :=
      ⟨_root_.trans (symm hab : Rᶜ b a), _root_.trans (hab : Rᶜ a b)⟩
    by_cases h : R a c
    · rw [destutter'_cons_pos (h := h), destutter'_cons_pos (h := by_contra (hc.2 · h)),
        tail_cons, tail_cons]
    · rw [destutter'_cons_neg (h := h), destutter'_cons_neg (h := hc.1 h), ih]

theorem destutter'_destutter (a : α) (m : List α) :
    (m.destutter R).destutter' R a = m.destutter' R a := by
  cases m with
  | nil => simp
  | cons c m =>
    obtain ⟨t, ht⟩ := destutter'_eq_cons (R := R) c m
    have hc : (c :: t).IsChain R := ht ▸ isChain_destutter' R m c
    rw [destutter_cons', ht]
    by_cases h : R a c
    · rw [destutter'_cons_pos (h := h), destutter'_cons_pos (h := h),
        destutter'_of_isChain_cons _ _ hc, ht]
    · rw [destutter'_cons_neg (h := h), destutter'_cons_neg (h := h),
        ← cons_head?_tail (head?_destutter' (R := R) a t),
        ← cons_head?_tail (head?_destutter' (R := R) a m), tail_destutter'_congr h,
        tail_destutter'_congr h, destutter'_of_isChain_cons _ _ hc, ht]

@[simp]
theorem destutter_append_right (l m : List α) :
    (l ++ m.destutter R).destutter R = (l ++ m).destutter R := by
  cases l with
  | nil => simpa using destutter_idem m R
  | cons a l =>
    rw [cons_append, cons_append, destutter_cons', destutter_cons', destutter'_append,
      destutter'_append, destutter'_destutter]

theorem destutter_append_destutter (l m : List α) :
    (l.destutter R ++ m.destutter R).destutter R = (l ++ m).destutter R := by
  rw [destutter_append_left, destutter_append_right]

end IsEquiv

variable [DecidableEq α]

private theorem tail_destutter'_ne_of_isChain {z : α} (h : m.IsChain (· ≠ ·)) :
    (m.destutter' (· ≠ ·) z).tail = if some z = m.head? then m.tail else m := by
  cases m with
  | nil => simp
  | cons b m =>
    have hbm : m.destutter' (· ≠ ·) b = b :: m := destutter'_of_isChain_cons _ _ h
    by_cases hzb : z = b
    · subst hzb
      rw [destutter'_cons_neg (h := by simp), hbm]
      simp
    · rw [destutter'_cons_pos (h := hzb), hbm]
      simp [hzb]

/-- Destuttering two concatenated chains merges at most the seam, dropping the head of `m`
exactly when it repeats the last element of `l`. -/
theorem IsChain.destutter_ne_append (h1 : l.IsChain (· ≠ ·)) (h2 : m.IsChain (· ≠ ·)) :
    (l ++ m).destutter (· ≠ ·) = if l.getLast? = m.head? then l ++ m.tail else l ++ m := by
  cases l with
  | nil => cases m <;> simp [destutter_of_isChain _ _ h2]
  | cons a l =>
    rw [cons_append, destutter_cons', destutter'_append, destutter'_of_isChain_cons _ _ h1,
      tail_destutter'_ne_of_isChain h2, getLastD_eq_getLast?,
      getLast?_eq_some_getLast (cons_ne_nil a l), Option.getD_some]
    split_ifs <;> simp

end List
