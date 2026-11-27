/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Order.Basic

/-!
# Transitivity, antisymmetry and decidability of `List.Forall₂`

`List.Forall₂ R` relates two lists of the same length whose entries are related by `R` position by
position. It is transitive when `R` is and antisymmetric when `R` is. For `R := (· ≤ ·)` it is the
pointwise order on lists of a fixed length, and the lexicographic order `<` on lists extends its
strict part.

## Main results

* `List.Forall₂.trans`, `List.Forall₂.antisymm`: `Forall₂ R` is transitive and antisymmetric when
  `R` is.
* `List.Forall₂.not_gt`, `List.Forall₂.lt_of_ne`: if `l₁` is pointwise at most `l₂` then `l₂` is
  not lexicographically below `l₁`, and `l₁` is lexicographically below `l₂` unless they are equal.
* `List.decidableForall₂`, `List.decidableSublistForall₂`: `Decidable` instances for `Forall₂ R`
  and `SublistForall₂ R` that `decide` can evaluate, the second by greedy matching.

## Implementation notes

The lexicographic lemmas are stated for `<`, which is `List.Lex (· < ·)` under both the `LT`
instance of core Lean and mathlib's linear order on lists. The two `≤` differ: core's `l₁ ≤ l₂`
unfolds to `¬ l₂ < l₁`, and mathlib's, on a linear order, is reached with `not_lt`.

Batteries decides `Forall₂` through `List.all₂`, whose body it stopped exposing to other modules
in batteries#2006, so `decide` gets stuck on it. `List.decidableForall₂` takes priority over that
instance and is equal to it only propositionally; remove it once Batteries exposes `List.all₂`
again.

[UPSTREAM] candidates for `Mathlib/Data/List/Forall2.lean` and `Mathlib/Data/List/Lex.lean`.
-/

@[expose] public section

namespace List

variable {α β : Type*} {R : α → β → Prop} {r : α → α → Prop}

theorem Forall₂.trans [IsTrans α r] :
    ∀ {l₁ l₂ l₃ : List α}, Forall₂ r l₁ l₂ → Forall₂ r l₂ l₃ → Forall₂ r l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (_root_.trans h₁ h₂) (t₁.trans t₂)

theorem Forall₂.antisymm [Std.Antisymm r] :
    ∀ {l₁ l₂ : List α}, Forall₂ r l₁ l₂ → Forall₂ r l₂ l₁ → l₁ = l₂
  | _, _, .nil, .nil => rfl
  | _, _, .cons h₁ t₁, .cons h₂ t₂ => by rw [_root_.antisymm h₁ h₂, t₁.antisymm t₂]

/-! ### Decidability -/

/-- `Forall₂ R` decided by structural recursion on both lists, so that `decide` evaluates it
outside this module. -/
instance (priority := high) decidableForall₂ [∀ a b, Decidable (R a b)] :
    ∀ l₁ l₂, Decidable (Forall₂ R l₁ l₂)
  | [], [] => isTrue .nil
  | [], _ :: _ | _ :: _, [] => isFalse nofun
  | a :: l₁, b :: l₂ =>
    haveI := decidableForall₂ l₁ l₂
    decidable_of_iff (R a b ∧ Forall₂ R l₁ l₂) forall₂_cons.symm

/-- Dropping the head of the first list preserves `SublistForall₂`. -/
theorem SublistForall₂.of_cons {a : α} {l₁ : List α} {l₂ : List β}
    (h : SublistForall₂ R (a :: l₁) l₂) : SublistForall₂ R l₁ l₂ := by
  generalize hl : a :: l₁ = l at h
  induction h generalizing a l₁ with
  | nil => cases hl
  | cons _ t _ => cases hl; exact .cons_right t
  | cons_right _ ih => exact .cons_right (ih hl)

/-- When the heads are related, a `SublistForall₂` may as well relate them. -/
theorem sublistForall₂_cons_cons_iff_of_rel {a : α} {b : β} {l₁ : List α} {l₂ : List β}
    (h : R a b) : SublistForall₂ R (a :: l₁) (b :: l₂) ↔ SublistForall₂ R l₁ l₂ :=
  ⟨fun | .cons _ t => t | .cons_right t => t.of_cons, .cons h⟩

/-- When the heads are not related, a `SublistForall₂` skips the head of the second list. -/
theorem sublistForall₂_cons_cons_iff_of_not_rel {a : α} {b : β} {l₁ : List α} {l₂ : List β}
    (h : ¬ R a b) : SublistForall₂ R (a :: l₁) (b :: l₂) ↔ SublistForall₂ R (a :: l₁) l₂ :=
  ⟨fun | .cons h' _ => absurd h' h | .cons_right t => t, .cons_right⟩

/-- `SublistForall₂ R` decided by matching each entry of the first list to the first entry of the
second that it is related to, in time linear in the second list. -/
instance decidableSublistForall₂ [∀ a b, Decidable (R a b)] :
    ∀ l₁ l₂, Decidable (SublistForall₂ R l₁ l₂)
  | [], _ => isTrue .nil
  | _ :: _, [] => isFalse nofun
  | a :: l₁, b :: l₂ =>
    if h : R a b then
      haveI := decidableSublistForall₂ l₁ l₂
      decidable_of_iff _ (sublistForall₂_cons_cons_iff_of_rel h).symm
    else
      haveI := decidableSublistForall₂ (a :: l₁) l₂
      decidable_of_iff _ (sublistForall₂_cons_cons_iff_of_not_rel h).symm

/-! ### The lexicographic order extends the pointwise order -/

/-- If `l₁` is pointwise at most `l₂`, then `l₂` is not lexicographically below `l₁`. -/
theorem Forall₂.not_gt [Preorder α] {l₁ l₂ : List α} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    ¬ l₂ < l₁ := by
  induction h with
  | nil => exact nofun
  | cons hab _ ih =>
    rintro (_ | hlt | hlt)
    exacts [hab.not_gt hlt, ih hlt]

/-- If `l₁` is pointwise at most `l₂` and differs from it, then `l₁` is lexicographically below
`l₂`, as `Pi.toLex_strictMono` says of functions. -/
theorem Forall₂.lt_of_ne [PartialOrder α] {l₁ l₂ : List α} (h : Forall₂ (· ≤ ·) l₁ l₂)
    (hne : l₁ ≠ l₂) : l₁ < l₂ := by
  induction h with
  | nil => exact absurd rfl hne
  | cons hab _ ih =>
    rcases hab.lt_or_eq with hab | rfl
    · exact .rel hab
    · exact .cons (ih fun h ↦ hne (h ▸ rfl))

end List
