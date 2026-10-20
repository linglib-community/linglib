/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Lists of bounded length are finite

Over a finite type, the lists of length at most `n` form a finite type: fibred by `length`, they
are the vectors of each length `m ≤ n`. The set form is `List.finite_length_le`.
-/

@[expose] public section

namespace List

variable {α : Type*}

instance finite_subtype_length_le [Finite α] (n : ℕ) : Finite {l : List α // l.length ≤ n} :=
  .of_equiv (Σ m : Set.Iic n, List.Vector α m)
    (Equiv.sigmaSubtypeFiberEquivSubtype length fun _ ↦ .rfl)

instance fintypeSubtypeLengthLE [Fintype α] (n : ℕ) : Fintype {l : List α // l.length ≤ n} :=
  fast_instance% .ofEquiv (Σ m : Set.Iic n, List.Vector α m)
    (Equiv.sigmaSubtypeFiberEquivSubtype length fun _ ↦ .rfl)

end List
