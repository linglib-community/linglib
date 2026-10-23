/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.MinMax

/-!
# `List.argmax` under `filter` and `map`

`Mathlib/Data/List/MinMax.lean` characterizes `argmax` (`List.argmax_eq_some_iff`) but has no
lemma relating it to `filter` or `map`. The maximizer stays the maximizer of any filter that keeps
it, the choice-consistency property of selection by a score; `argmax` commutes with `map`; and it
depends only on how the scores order the list, and on a list sorted by decreasing score it is
the head. [UPSTREAM] candidates for that file.

## Main results

* `List.argmax_filter_of_mem`: the maximizer of `l` is the maximizer of any filter of `l` that
  keeps it.
* `List.argmax_map`: `argmax` commutes with `map`.
* `List.argmax_congr`: scores that order `l` the same way have the same maximizer.
* `List.argmax_eq_head?`: on a list sorted by decreasing score the maximizer is the head.
-/

@[expose] public section

namespace List

variable {α β γ : Type*} [LinearOrder β] [LinearOrder γ] {f : α → β} {l : List α} {m : α}

theorem argmax_filter_of_mem {p : α → Bool} (h : m ∈ argmax f l) (hp : p m) :
    m ∈ argmax f (l.filter p) := by
  induction l generalizing m with
  | nil => simp at h
  | cons a t ih =>
    rw [argmax_cons] at h
    rcases ht : argmax f t with - | c
    · obtain rfl : a = m := by simpa [ht] using h
      simp [argmax_eq_none.mp ht, hp]
    · simp only [ht] at h
      split_ifs at h with hac
      · obtain rfl := Option.some.inj h
        rw [filter_cons]
        split_ifs
        · simp [argmax_cons, Option.mem_def.mp (ih ht hp), hac]
        · exact ih ht hp
      · obtain rfl := Option.some.inj h
        rw [filter_cons_of_pos hp, argmax_cons]
        rcases hft : argmax f (t.filter p) with - | d
        · rfl
        · have hd := le_of_mem_argmax (mem_of_mem_filter (argmax_mem hft)) ht
          simp [not_lt.mpr (hd.trans (not_lt.mp hac))]

theorem argmax_map {δ : Type*} (g : δ → α) (l : List δ) :
    argmax f (l.map g) = (argmax (f ∘ g) l).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [map_cons, argmax_cons, argmax_cons, ih]
    rcases argmax (f ∘ g) t with - | c
    · rfl
    · simp only [Option.map_some, Function.comp]
      split_ifs <;> rfl

theorem argmax_congr {g : α → γ} (h : ∀ a ∈ l, ∀ b ∈ l, f a ≤ f b ↔ g a ≤ g b) :
    argmax f l = argmax g l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [argmax_cons, argmax_cons,
      ih fun x hx y hy ↦ h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)]
    rcases hc : argmax g t with - | c
    · rfl
    · simp only [← not_le, h c (mem_cons_of_mem _ (argmax_mem hc)) a mem_cons_self]

theorem argmax_eq_head? (h : l.Pairwise fun a b ↦ f b ≤ f a) : argmax f l = l.head? := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [argmax_cons, ih (pairwise_cons.mp h).2]
    rcases t with - | ⟨b, t⟩
    · rfl
    · simp [not_lt.mpr ((pairwise_cons.mp h).1 b mem_cons_self)]

end List
