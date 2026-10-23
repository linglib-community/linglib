/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Locally finite linear orders embed in the integers

`[UPSTREAM]` candidate for `Mathlib/Order/SuccPred/LinearLocallyFinite.lean`. A locally finite
linear order embeds in `ℤ` by numbering its elements from a base point, `toZ`, once it is given
the successor and predecessor structure of a locally finite order.
-/

@[expose] public section

theorem nonempty_orderEmbedding_int (ι : Type*) [LinearOrder ι] [LocallyFiniteOrder ι] :
    Nonempty (ι ↪o ℤ) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨OrderEmbedding.ofIsEmpty⟩
  | inr hι =>
    let := LinearLocallyFiniteOrder.succOrder ι
    let := LinearLocallyFiniteOrder.predOrder ι
    exact ⟨OrderEmbedding.ofStrictMono (toZ hι.some) toZ_strictMono⟩
