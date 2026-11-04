/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OCP

/-!
# Forbidden-pair constraints

This file defines the forbidden-pair constraints on strings, which carry genuine adjacency logic:
`Constraint.forbidPairs R`, with one violation for each adjacent pair `(a, b)` satisfying `R a b`,
and its identity and non-identity instances, the OCP of Goldsmith and McCarthy and AGREE. A
constraint on candidates of another type, or on a tier, is not a separate constructor but the
`Constraint.comap` of a string constraint along the candidate's string or along erasure of the
off-tier symbols. Pulled back along the output form of a correspondence candidate, a string
constraint is a markedness constraint (`Correspondence.isMarkedness_iff_exists_comap`). A string
satisfies the OCP exactly when it is `OCP.IsClean`.

## Main definitions

* `Constraint.forbidPairs`, `Constraint.ocp`, `Constraint.agree`: the forbidden-pair constraints
  on strings.

## Main results

* `Constraint.forbidPairs_eq_zero_iff`: a string satisfies `forbidPairs R` iff no two adjacent
  elements are `R`-related.
* `Constraint.ocp_eq_zero_iff`, `Constraint.agree_eq_zero_iff`: the strings that satisfy the OCP
  and AGREE.

## Implementation notes

`Constraint.ocp` and `Constraint.agree` compare whole symbols. Over segments, `ocp` is the
identity OCP rather than OCP-Place, and `agree` is AGREE[F] only after the string is projected
to the values of the feature `F`.

## References

* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace OptimalityTheory

variable {α : Type*}

/-- The forbidden-pair constraint on strings, with one violation for each adjacent pair `(a, b)`
satisfying `R a b`. -/
def Constraint.forbidPairs (R : α → α → Prop) [DecidableRel R] : Constraint (List α)
  | [] | [_] => 0
  | a :: b :: w => (if R a b then 1 else 0) + Constraint.forbidPairs R (b :: w)

/-- The OCP ([goldsmith-1976], [mccarthy-1986]), the forbidden-pair constraint against adjacent
identical elements, polymorphic over the feature type ([berent-2026]). -/
def Constraint.ocp [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· = ·)

/-- AGREE, the forbidden-pair constraint against adjacent distinct elements and the dual of
`Constraint.ocp`. -/
def Constraint.agree [DecidableEq α] : Constraint (List α) := Constraint.forbidPairs (· ≠ ·)

namespace Constraint

section forbidPairs

variable (R : α → α → Prop) [DecidableRel R]

@[simp] theorem forbidPairs_nil : forbidPairs R [] = 0 := rfl

@[simp] theorem forbidPairs_singleton (a : α) : forbidPairs R [a] = 0 := rfl

@[simp] theorem forbidPairs_cons_cons (a b : α) (w : List α) :
    forbidPairs R (a :: b :: w) = (if R a b then 1 else 0) + forbidPairs R (b :: w) := rfl

/-- A string satisfies the forbidden-pair constraint iff no two adjacent elements are
`R`-related. -/
theorem forbidPairs_eq_zero_iff (w : List α) :
    forbidPairs R w = 0 ↔ w.IsChain (fun a b ↦ ¬ R a b) := by
  induction w with
  | nil => simp
  | cons a rest ih => cases rest with
    | nil => simp
    | cons b rest' =>
      rw [List.isChain_cons_cons, ← ih]
      by_cases hab : R a b <;> simp [hab]

/-- The violations split at any element, as `List.isChain_split` splits a chain. -/
theorem forbidPairs_split (l₁ : List α) (c : α) (l₂ : List α) :
    forbidPairs R (l₁ ++ c :: l₂) = forbidPairs R (l₁ ++ [c]) + forbidPairs R (c :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih => cases t with
    | nil => simp
    | cons b t => simp only [List.cons_append, forbidPairs_cons_cons] at ih ⊢; omega

theorem forbidPairs_append_cons_cons (l₁ : List α) (b c : α) (l₂ : List α) :
    forbidPairs R (l₁ ++ b :: c :: l₂) =
      forbidPairs R (l₁ ++ [b]) + (if R b c then 1 else 0) + forbidPairs R (c :: l₂) := by
  rw [forbidPairs_split, forbidPairs_cons_cons, Nat.add_assoc]

/-- Two first elements related alike give a string the same violations. -/
theorem forbidPairs_congr_head {a b : α} (h : ∀ x, R a x ↔ R b x) (w : List α) :
    forbidPairs R (a :: w) = forbidPairs R (b :: w) := by
  cases w <;> simp [h]

/-- Two last elements related alike give a string the same violations. -/
theorem forbidPairs_congr_last {a b : α} (h : ∀ x, R x a ↔ R x b) (w : List α) :
    forbidPairs R (w ++ [a]) = forbidPairs R (w ++ [b]) := by
  induction w with
  | nil => simp
  | cons c t ih => cases t with
    | nil => simp [h]
    | cons d t => simpa using ih

end forbidPairs

section DecidableEq

variable [DecidableEq α]

@[simp] theorem ocp_nil : ocp ([] : List α) = 0 := rfl

@[simp] theorem ocp_singleton (a : α) : ocp [a] = 0 := rfl

@[simp] theorem ocp_cons_cons (a b : α) (w : List α) :
    ocp (a :: b :: w) = (if a = b then 1 else 0) + ocp (b :: w) := rfl

/-- A string satisfies the OCP iff no two adjacent elements are identical. -/
theorem ocp_eq_zero_iff {w : List α} : ocp w = 0 ↔ OCP.IsClean w :=
  forbidPairs_eq_zero_iff (· = ·) w

/-- A string satisfies AGREE iff its adjacent elements are equal, so that all its elements are
equal. -/
theorem agree_eq_zero_iff {w : List α} : agree w = 0 ↔ w.IsChain (· = ·) :=
  (forbidPairs_eq_zero_iff (· ≠ ·) w).trans (by simp only [ne_eq, not_not])

end DecidableEq

end Constraint

end OptimalityTheory
