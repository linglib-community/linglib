/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Monotone.Monovary
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Finset.Defs

/-!
# `MonovaryOn` on `singleton`, `union`, `insert`, and `image`

`[UPSTREAM]` mathlib's `MonovaryOn` API (`Mathlib/Order/Monotone/Monovary.lean`)
has `empty` / `subset` / `comp_right` / `comp_monotone_left`, but lacks the
structural set-building lemmas that `Set.Pairwise` enjoys
(`Set.pairwise_singleton` / `pairwise_union` / `pairwise_insert`). This file fills
the gap, modelled on the `Set.Pairwise` family lemma-for-lemma, plus the `image`
companion of `MonovaryOn.comp_right` (which is the preimage form). Each pairs with
its `AntivaryOn` twin, as every lemma in the mathlib file does.

Upstream home: `section Preorder` of `Mathlib/Order/Monotone/Monovary.lean`,
beside `MonovaryOn.empty` and `MonovaryOn.comp_right`.

## Main results

* `monovaryOn_singleton`, `monovaryOn_union`, `monovaryOn_insert`: the `Set.pairwise_*`
  analogues, with `antivaryOn_*` twins.
* `monovaryOn_image`: `MonovaryOn f g (k '' u) ↔ MonovaryOn (f ∘ k) (g ∘ k) u`, the image
  companion of `MonovaryOn.comp_right`, with an `antivaryOn_image` twin.
* `MonovaryOn` and `AntivaryOn` on a finset are decidable, so `decide` checks them on finite
  data.
-/

@[expose] public section

variable {ι ι' α β : Type*} [Preorder α] [Preorder β] {f : ι → α} {g : ι → β}
  {s t : Set ι}

/-! ### Monovary -/

/-- Any two functions monovary on a singleton. -/
@[simp] theorem monovaryOn_singleton (a : ι) : MonovaryOn f g {a} := by
  simp [MonovaryOn]

/-- Two functions monovary on a union iff they monovary on each part and neither part inverts
the order against the other. The `Monovary` analogue of `Set.pairwise_union`. -/
theorem monovaryOn_union : MonovaryOn f g (s ∪ t) ↔ MonovaryOn f g s ∧ MonovaryOn f g t ∧
    ∀ a ∈ s, ∀ b ∈ t, (g a < g b → f a ≤ f b) ∧ (g b < g a → f b ≤ f a) := by
  grind [MonovaryOn]

/-- The `Monovary` analogue of `Set.pairwise_insert`. -/
theorem monovaryOn_insert {a : ι} :
    MonovaryOn f g (insert a s) ↔
      MonovaryOn f g s ∧ ∀ b ∈ s, (g a < g b → f a ≤ f b) ∧ (g b < g a → f b ≤ f a) := by
  grind [MonovaryOn]

/-- `f` and `g` monovary on `k '' u` iff `f ∘ k` and `g ∘ k` monovary on `u`. The image
companion of `MonovaryOn.comp_right`. -/
theorem monovaryOn_image (k : ι' → ι) (u : Set ι') :
    MonovaryOn f g (k '' u) ↔ MonovaryOn (f ∘ k) (g ∘ k) u := by
  grind [MonovaryOn]

/-! ### Antivary -/

/-- Any two functions antivary on a singleton. -/
@[simp] theorem antivaryOn_singleton (a : ι) : AntivaryOn f g {a} := by
  simp [AntivaryOn]

/-- The `Antivary` analogue of `Set.pairwise_union`. -/
theorem antivaryOn_union : AntivaryOn f g (s ∪ t) ↔ AntivaryOn f g s ∧ AntivaryOn f g t ∧
    ∀ a ∈ s, ∀ b ∈ t, (g a < g b → f b ≤ f a) ∧ (g b < g a → f a ≤ f b) := by
  grind [AntivaryOn]

/-- The `Antivary` analogue of `Set.pairwise_insert`. -/
theorem antivaryOn_insert {a : ι} :
    AntivaryOn f g (insert a s) ↔
      AntivaryOn f g s ∧ ∀ b ∈ s, (g a < g b → f b ≤ f a) ∧ (g b < g a → f a ≤ f b) := by
  grind [AntivaryOn]

/-- `f` and `g` antivary on `k '' u` iff `f ∘ k` and `g ∘ k` antivary on `u`. The image
companion of `AntivaryOn.comp_right`. -/
theorem antivaryOn_image (k : ι' → ι) (u : Set ι') :
    AntivaryOn f g (k '' u) ↔ AntivaryOn (f ∘ k) (g ∘ k) u := by
  grind [AntivaryOn]

/-! ### Decidability -/

instance [DecidableLT β] [DecidableLE α] {t : Finset ι} : Decidable (MonovaryOn f g t) :=
  inferInstanceAs (Decidable (∀ i ∈ t, ∀ j ∈ t, g i < g j → f i ≤ f j))

instance [DecidableLT β] [DecidableLE α] {t : Finset ι} : Decidable (AntivaryOn f g t) :=
  inferInstanceAs (Decidable (∀ i ∈ t, ∀ j ∈ t, g i < g j → f j ≤ f i))
