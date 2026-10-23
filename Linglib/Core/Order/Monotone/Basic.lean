/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Monotone.Basic

/-!
# Strictly monotone maps out of total preorders  `[UPSTREAM]`

A strictly monotone map out of a total preorder reflects `≤`. On a linear order this is half of
mathlib's `StrictMono.le_iff_le`; on a total preorder only the reflection survives, since tied
elements may be mapped apart.

Upstream home: `Mathlib/Order/Monotone/Basic.lean`, beside `Monotone.reflect_lt`.

## Main statements

* `StrictMono.reflect_le`: a strictly monotone map out of a total preorder reflects `≤`.
-/

@[expose] public section

/-- A strictly monotone map out of a total preorder reflects `≤`. -/
theorem StrictMono.reflect_le {α β : Type*} [Preorder α] [@Std.Total α (· ≤ ·)] [Preorder β]
    {f : α → β} (hf : StrictMono f) {a b : α} (h : f a ≤ f b) : a ≤ b :=
  (total_of (· ≤ ·) a b).elim id fun hba ↦
    by_contra fun hab ↦ (hf (lt_of_le_not_ge hba hab)).not_ge h
