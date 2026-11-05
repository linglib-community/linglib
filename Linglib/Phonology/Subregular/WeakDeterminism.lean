/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ElgotMezei

/-!
# Weak determinism

A function on strings over one alphabet is weakly deterministic, in Heinz and Lai's sense, when it
is a right-subsequential function after a left-subsequential one that never lengthens its input.
The length bound keeps the first pass from marking up its output: [every regular function factors
into the two scans](##isBimachineComputable_iff_exists_comp), but through new symbols in between,
and over an alphabet of two or more letters new symbols can be coded as longer strings.
Subsequential functions that do not lengthen their input are weakly deterministic, and [a weakly
deterministic function is regular](##IsWeaklyDeterministic.isBimachineComputable).

## Implementation notes

Heinz and Lai's Corollary 1 places every subsequential function in the class. With the length
bound on the first pass the left-subsequential half is proved here only for functions that do not
lengthen their input.

## References

* [heinz-lai-2013]
* [elgot-mezei-1965]
-/

@[expose] public section

variable {α : Type*} {f : List α → List α}

/-- `f` is weakly deterministic when it is a right-subsequential function after a
left-subsequential one, over the alphabet of `f`, whose first pass never lengthens its input. -/
def IsWeaklyDeterministic (f : List α → List α) : Prop :=
  ∃ L R : List α → List α, IsLeftSubsequential L ∧ (∀ x, (L x).length ≤ x.length) ∧
    IsRightSubsequential R ∧ R ∘ L = f

/-- A right-subsequential function is weakly deterministic, after the identity. -/
theorem IsRightSubsequential.isWeaklyDeterministic (hf : IsRightSubsequential f) :
    IsWeaklyDeterministic f :=
  ⟨id, f, isLeftSubsequential_id, fun _ ↦ le_rfl, hf, rfl⟩

/-- A left-subsequential function that does not lengthen its input is weakly deterministic, before
the identity. -/
theorem IsLeftSubsequential.isWeaklyDeterministic (hf : IsLeftSubsequential f)
    (hlen : ∀ x, (f x).length ≤ x.length) : IsWeaklyDeterministic f :=
  ⟨f, id, hf, hlen, isRightSubsequential_id, rfl⟩

/-- A weakly deterministic function is computed by a bimachine. -/
theorem IsWeaklyDeterministic.isBimachineComputable (hf : IsWeaklyDeterministic f) :
    IsBimachineComputable f := by
  obtain ⟨L, R, hL, -, hR, rfl⟩ := hf
  exact hR.isBimachineComputable.comp hL.isBimachineComputable
