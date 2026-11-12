/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Trajectories as finite sequences

A trajectory up to time `n`, a function on `Finset.Iic n`, is the sequence of its first `n + 1`
values, a function on `Fin (n + 1)`. `ProbabilityTheory.trajEquivFin` is this correspondence as a
measurable equivalence.
-/

@[expose] public section

open Finset

/-- The times `0, …, n` are the indices of the first `n + 1` draws. -/
def Nat.iicEquivFin (n : ℕ) : (Iic n : Finset ℕ) ≃ Fin (n + 1) where
  toFun i := ⟨i, Nat.lt_succ_of_le (mem_Iic.1 i.2)⟩
  invFun j := ⟨j, mem_Iic.2 (Nat.le_of_lt_succ j.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- A trajectory up to time `n` as the sequence of its first `n + 1` draws. -/
noncomputable def trajEquivFin (n : ℕ) : (Π _ : Iic n, α) ≃ᵐ (Fin (n + 1) → α) :=
  MeasurableEquiv.piCongrLeft (fun _ ↦ α) (Nat.iicEquivFin n)

@[simp] theorem trajEquivFin_apply (n : ℕ) (x : Π _ : Iic n, α) (j : Fin (n + 1)) :
    trajEquivFin n x j = x ⟨j, mem_Iic.2 (Nat.le_of_lt_succ j.2)⟩ := by
  simp [trajEquivFin, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

end ProbabilityTheory
