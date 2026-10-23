/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Image

/-!
# Singleton images under an injective function

Mirror of `Mathlib/Data/Set/Image.lean`: the image of a set under an injective function is a
singleton iff the set is, the singleton rung beside `Function.Injective.subsingleton_image_iff`.
[UPSTREAM]
-/

@[expose] public section

namespace Function.Injective

open Set

variable {α β : Type*} {f : α → β}

theorem exists_image_eq_singleton_iff (hf : Injective f) {s : Set α} :
    (∃ b, f '' s = {b}) ↔ ∃ a, s = {a} := by
  simp only [exists_eq_singleton_iff_nonempty_subsingleton, image_nonempty,
    hf.subsingleton_image_iff]

end Function.Injective
