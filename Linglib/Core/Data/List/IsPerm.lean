/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Perm.Basic

/-!
# A permutation test relative to a comparison

`List.isPermBy r l₁ l₂` is `List.isPerm` with a comparison `r : α → β → Bool` in place of `==`:
it pairs each member of `l₁` with the first member of `l₂` still unpaired that `r` relates to it.
Such greedy pairing is sound when `r` compares invariants, `r a b ↔ f a = g b`, and then it decides
that the invariants of the two lists agree up to permutation (`List.isPermBy_iff`). The hypothesis
is asked only of the members of the two lists, so the test applies inside a recursion over a nested
inductive type, where `r` is known to be correct only on the subterms.

## Implementation notes

The match is found with `findIdx?` and removed with `eraseIdx`, so `r` is evaluated once per
comparison; the `contains`-then-`erase` shape of `List.isPerm` would evaluate it twice.
-/

@[expose] public section

namespace List

variable {α β γ δ : Type*}

/-- `isPermBy r l₁ l₂` pairs each member of `l₁` with the first member of `l₂` still unpaired that
`r` relates to it, and tests that every member of both lists is paired. -/
def isPermBy (r : α → β → Bool) : List α → List β → Bool
  | [], l₂ => l₂.isEmpty
  | a :: l₁, l₂ =>
    match l₂.findIdx? (r a) with
    | some i => isPermBy r l₁ (l₂.eraseIdx i)
    | none => false

theorem isPermBy_map_left (r : α → β → Bool) (f : δ → α) :
    ∀ (l₁ : List δ) (l₂ : List β), isPermBy r (l₁.map f) l₂ = isPermBy (fun d ↦ r (f d)) l₁ l₂
  | [], _ => rfl
  | d :: l₁, l₂ => by
    simp only [map_cons, isPermBy]
    split <;> simp only [isPermBy_map_left r f l₁]

/-- When `r` compares the invariants `f` and `g` on the members of the two lists, `isPermBy r`
decides that the lists have the same invariants up to permutation. -/
theorem isPermBy_iff {r : α → β → Bool} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, (∀ a ∈ l₁, ∀ b ∈ l₂, r a b ↔ f a = g b) →
      (isPermBy r l₁ l₂ ↔ (l₁.map f).Perm (l₂.map g))
  | [], l₂, _ => by simp [isPermBy]
  | a :: l₁, l₂, h => by
    rw [isPermBy]
    split
    · next i hi =>
      obtain ⟨hil, hai, -⟩ := findIdx?_eq_some_iff_getElem.1 hi
      have := (getElem_cons_eraseIdx_perm hil).map g
      rw [map_cons, ← (h a mem_cons_self _ (getElem_mem hil)).1 hai] at this
      rw [isPermBy_iff fun x hx y hy ↦
        h x (mem_cons_of_mem _ hx) y ((eraseIdx_sublist _ _).subset hy), map_cons,
        ← rel_congr_right this, perm_cons]
    · next hi =>
      refine iff_of_false Bool.false_ne_true fun hp ↦ ?_
      obtain ⟨b, hb, hab⟩ := mem_map.1 (hp.subset mem_cons_self)
      simpa [(h a mem_cons_self b hb).2 hab.symm] using findIdx?_eq_none_iff.1 hi b hb

end List
