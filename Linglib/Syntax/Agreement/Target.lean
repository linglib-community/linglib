/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.DependsOn
public import Linglib.Syntax.Feature.Bundle
public import Linglib.Syntax.Agreement.Hierarchy

/-!
# Agreement targets

An agreement target is an element whose form agreement determines. This file records a target
by the positions of the Agreement Hierarchy at which it occurs, its form in each cell of a
paradigm, and the dimensions it inflects for. A cell gives each dimension a value a language
distinguishes, and the target inflects for a dimension when changing that value alone changes the
form somewhere. What a target agrees in is thus read off its forms, and the targets of one
language may differ in it, as the two tenses of the Russian verb do.

## Implementation notes

The inflection is a finset, certified against the form by `mem_inflection`, so that it can be
computed with, as the support of a `Finsupp` is certified by `Finsupp.mem_support_toFun`. It
carries no information: a target [is its positions and its form](##Agreement.Target.ext).

## References

* [corbett-1998]
* [corbett-2006]
-/

@[expose] public section

open Function

namespace Agreement

/-- An agreement target over the values `V d` of each dimension `d` records the positions of the
Agreement Hierarchy at which it occurs, its form in each cell, and the dimensions it inflects
for. -/
structure Target (V : Dimension → Type*) (F : Type*) where
  /-- The positions of the Agreement Hierarchy at which the target occurs. -/
  positions : Finset Position
  /-- The form of the target in each cell. -/
  form : (Π d, V d) → F
  /-- The dimensions the target inflects for. -/
  inflection : Finset Dimension
  /-- The target inflects for a dimension exactly when two cells differing there alone take
  different forms. -/
  mem_inflection : ∀ d, d ∈ inflection ↔ ∃ x a, form (update x d a) ≠ form x

namespace Target

variable {V : Dimension → Type*} {F : Type*}

/-- The target with the given positions and form that inflects for `s`, given that the form
depends on `s` and that each dimension of `s` changes it somewhere. -/
def ofDependsOn (positions : Finset Position) (form : (Π d, V d) → F) (s : Finset Dimension)
    (h : DependsOn form s) (hs : ∀ d ∈ s, ∃ x a, form (update x d a) ≠ form x) :
    Target V F where
  positions := positions
  form := form
  inflection := s
  mem_inflection d := ⟨hs d, fun ⟨_, _, hx⟩ ↦ by_contra fun hd ↦
    hx (h fun _ hj ↦ update_of_ne (ne_of_mem_of_not_mem hj hd) ..)⟩

/-- A target is its positions and its form. -/
@[ext]
theorem ext {t u : Target V F} (hp : t.positions = u.positions) (hf : t.form = u.form) :
    t = u := by
  obtain ⟨p, f, s, hs⟩ := t
  obtain ⟨p', f', s', hs'⟩ := u
  obtain rfl : p = p' := hp
  obtain rfl : f = f' := hf
  obtain rfl : s = s' := Finset.ext fun d ↦ (hs d).trans (hs' d).symm
  rfl

end Target

end Agreement
