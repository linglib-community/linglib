/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Composing a function with `![…]`

`[UPSTREAM]` candidate for `Mathlib/Data/Fin/VecNotation.lean`. This file restates
`Fin.comp_cons` for `Matrix.vecCons`, so that `f ∘ ![a, b]` rewrites to `![f a, f b]`.
`Matrix.vecCons` is a `def` rather than a reducible alias of `Fin.cons`, so
`Fin.comp_cons` does not fire on a vector literal, and mathlib has no `vecCons` form.

The primed lemmas state the same equations on the lambda `fun i => f (![a, b] i)`.
`simp` does not identify `f ∘ v` with `fun i => f (v i)`, and the lambda is the form
that structural recursion through a `Fin n → α` argument produces (a substitution's
`fun i => (ts i).subst σ`), whereas `∘` is the form mathlib's `Equiv.map_rel` and
`Fin.comp_cons` produce; a rewrite set that pushes `f` into a literal needs both.

## Main statements

* `Matrix.comp_vecCons`, `Matrix.comp_vecEmpty`: `f ∘ ![…]` pushes `f` into the literal.
* `Matrix.comp_vecCons'`, `Matrix.comp_vecEmpty'`: the same for `fun i => f (![…] i)`.
* `Matrix.comp_vec2'`: the two-element case, which `simp` cannot reach from `comp_vecCons'` because
  `cons_val_fin_one` first turns the tail into a constant function.
-/

@[expose] public section

namespace Matrix

variable {α β : Type*} {n : ℕ}

theorem comp_vecCons (f : α → β) (a : α) (v : Fin n → α) :
    f ∘ vecCons a v = vecCons (f a) (f ∘ v) :=
  Fin.comp_cons f a v

theorem comp_vecEmpty (f : α → β) : f ∘ ![] = (![] : Fin 0 → β) :=
  empty_eq _

theorem comp_vecCons' (f : α → β) (a : α) (v : Fin n → α) :
    (fun i => f (vecCons a v i)) = vecCons (f a) fun i => f (v i) :=
  Fin.comp_cons f a v

theorem comp_vecEmpty' (f : α → β) : (fun i => f (![] i)) = (![] : Fin 0 → β) :=
  empty_eq _

theorem comp_vec2' (f : α → β) (a b : α) : (fun i => f (![a, b] i)) = ![f a, f b] := by
  ext i; match i with | 0 | 1 => rfl

end Matrix
