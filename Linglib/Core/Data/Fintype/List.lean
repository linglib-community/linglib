/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector

/-!
# Lists of bounded length are finite

Over a finite type, the lists of length at most `n` form a finite type, being equivalent to
vectors of some length `m ≤ n`. The set form is `List.finite_length_le`.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- A list of length at most `n` is a vector of some length `m ≤ n`. -/
def subtypeLengthLEEquivSigmaVector (n : ℕ) :
    {l : List α // l.length ≤ n} ≃ Σ m : Fin (n + 1), List.Vector α m where
  toFun l := ⟨⟨l.1.length, Nat.lt_succ_of_le l.2⟩, ⟨l.1, rfl⟩⟩
  invFun s := ⟨s.2.toList, s.2.toList_length.trans_le (Nat.le_of_lt_succ s.1.2)⟩
  left_inv _ := rfl
  right_inv s := Sigma.subtype_ext (Fin.ext s.2.2) rfl

instance finite_subtype_length_le [Finite α] (n : ℕ) : Finite {l : List α // l.length ≤ n} :=
  .of_equiv _ (subtypeLengthLEEquivSigmaVector n).symm

instance fintypeSubtypeLengthLE [Fintype α] (n : ℕ) : Fintype {l : List α // l.length ≤ n} :=
  fast_instance% .ofEquiv _ (subtypeLengthLEEquivSigmaVector n).symm

end List
