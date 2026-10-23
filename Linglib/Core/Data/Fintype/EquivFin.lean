/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Permutations from equal fibre cardinalities

Mirror of `Mathlib/Data/Fintype/EquivFin.lean`: two maps on a finite type whose fibres have
equal cardinalities differ by a permutation of the domain, the fibrewise equivalences of
`Fintype.equivOfCardEq` glued by `Equiv.ofFiberEquiv`. [UPSTREAM]
-/

@[expose] public section

namespace Equiv

theorem exists_comp_eq_of_card_fiber_eq {α β : Type*} [Finite α] {f g : α → β}
    (h : ∀ b, Nat.card {x // g x = b} = Nat.card {x // f x = b}) : ∃ e : α ≃ α, f ∘ e = g := by
  have := Fintype.ofFinite α
  classical
  let e (b) : {x // g x = b} ≃ {x // f x = b} :=
    Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using h b)
  exact ⟨ofFiberEquiv e, funext (ofFiberEquiv_map e)⟩

end Equiv
