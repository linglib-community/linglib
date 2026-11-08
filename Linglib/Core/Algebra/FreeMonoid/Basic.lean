/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.FreeMonoid.Basic`, next to `FreeMonoid.map`.
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Filtering the letters of a free monoid

This file defines `FreeMonoid.filter p`, the endomorphism of `FreeMonoid α` that keeps the
letters satisfying `p` and erases the others, induced by `List.filter`. Where `FreeMonoid.map f`
sends each letter to a letter, `FreeMonoid.filter p` sends each letter to itself or to `1`: in
Pin's classification of morphisms between free monoids it is length-decreasing rather than
length-preserving, so it can send a nonempty word to `1`.

## Main definitions

* `FreeMonoid.filter`: the endomorphism keeping the letters that satisfy `p`.

## References

* [pin-mfa]
-/

@[expose] public section

namespace FreeMonoid

variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- The endomorphism of the free monoid keeping the letters that satisfy `p`. -/
def filter : FreeMonoid α →* FreeMonoid α where
  toFun w := ofList (w.toList.filter p)
  map_one' := rfl
  map_mul' x y := List.filter_append x.toList y.toList

@[simp] theorem toList_filter (w : FreeMonoid α) : (filter p w).toList = w.toList.filter p := rfl

@[simp] theorem filter_of (x : α) : filter p (of x) = if p x then of x else 1 := by
  by_cases h : p x <;> simp [filter, h]

end FreeMonoid
