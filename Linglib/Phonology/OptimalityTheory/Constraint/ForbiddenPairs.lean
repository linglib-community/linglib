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

The forbidden-pair constraint `Constraint.ofForbiddenPairs R` assigns a string one violation for
each adjacent pair `(a, b)` with `R a b`. A string satisfies it
[exactly when its adjacent elements form a chain of `¬ R`](##ofForbiddenPairs_eq_zero_iff), so the
constraint counts what `List.IsChain` decides, much as `List.countP` counts what a bounded
universal statement decides.

The Obligatory Contour Principle is the instance `R := (· = ·)`, `Constraint.ocp`. Leben proposed
it for tone melodies and Goldsmith gave it its name. McCarthy states it for any melody as a
prohibition on adjacent identical elements and applies it in segmental phonology, where it also
blocks syncope from creating clusters of identical consonants. A string satisfies the OCP exactly
when it is `OCP.IsClean`. Because the constraint is stated over any type of elements, it bans
$XX$ for a variable $X$, as Berent argues identity restrictions do, so
[no injective relabelling of the elements changes its violations](##ocp_map_of_injective) and the
ban extends to elements that a language lacks.

A constraint on candidates of another type, or on a tier, is the `Constraint.comap` of a string
constraint along the candidate's string, along a projection of its elements, or along the erasure
of off-tier symbols. Along a projection
[the forbidden relation is pulled back](##ofForbiddenPairs_map), and along the output string of a correspondence candidate the pullback is a markedness constraint
in the sense of `Correspondence.Coindexation.IsMarkedness`.

## Implementation notes

`Constraint.ocp` compares whole symbols, so over segments it is the identity OCP. OCP-Place and
the other OCP-Feature constraints are `ocp` pulled back along the feature's projection of the
relevant tier, which `ofForbiddenPairs_map` rewrites as the forbidden-pair constraint of agreement
in that feature.

## References

* [W. R. Leben, *Suprasegmental Phonology* (1973)][leben-1973]
* [J. A. Goldsmith, *Autosegmental Phonology* (1976)][goldsmith-1976]
* [J. J. McCarthy, *OCP Effects: Gemination and Antigemination* (1986)][mccarthy-1986]
* [I. Berent, *Three arguments for abstraction in phonology* (2026)][berent-2026]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

variable {α β : Type*}

/-- The forbidden-pair constraint on strings, with one violation for each adjacent pair `(a, b)`
satisfying `R a b`. -/
def ofForbiddenPairs (R : α → α → Prop) [DecidableRel R] : Constraint (List α)
  | [] | [_] => 0
  | a :: b :: w => (if R a b then 1 else 0) + ofForbiddenPairs R (b :: w)

/-- The Obligatory Contour Principle, the forbidden-pair constraint against adjacent identical
elements ((2) of [mccarthy-1986]). -/
def ocp [DecidableEq α] : Constraint (List α) := ofForbiddenPairs (· = ·)

section ofForbiddenPairs

variable (R : α → α → Prop) [DecidableRel R]

@[simp] theorem ofForbiddenPairs_nil : ofForbiddenPairs R [] = 0 := rfl

@[simp] theorem ofForbiddenPairs_singleton (a : α) : ofForbiddenPairs R [a] = 0 := rfl

@[simp] theorem ofForbiddenPairs_cons_cons (a b : α) (w : List α) :
    ofForbiddenPairs R (a :: b :: w) = (if R a b then 1 else 0) + ofForbiddenPairs R (b :: w) := rfl

/-- A string satisfies the forbidden-pair constraint iff no two adjacent elements are
`R`-related. -/
theorem ofForbiddenPairs_eq_zero_iff {R : α → α → Prop} [DecidableRel R] {w : List α} :
    ofForbiddenPairs R w = 0 ↔ w.IsChain (fun a b ↦ ¬ R a b) := by
  induction w using List.twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b w _ ih => by_cases hab : R a b <;> simp [hab, ih]

/-- The violations split at any element, as `List.isChain_split` splits a chain. -/
theorem ofForbiddenPairs_split (l₁ : List α) (c : α) (l₂ : List α) :
    ofForbiddenPairs R (l₁ ++ c :: l₂) =
      ofForbiddenPairs R (l₁ ++ [c]) + ofForbiddenPairs R (c :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih => cases t with
    | nil => simp
    | cons b t => simp only [List.cons_append, ofForbiddenPairs_cons_cons] at ih ⊢; omega

theorem ofForbiddenPairs_append_cons_cons (l₁ : List α) (b c : α) (l₂ : List α) :
    ofForbiddenPairs R (l₁ ++ b :: c :: l₂) =
      ofForbiddenPairs R (l₁ ++ [b]) + (if R b c then 1 else 0) + ofForbiddenPairs R (c :: l₂) := by
  rw [ofForbiddenPairs_split, ofForbiddenPairs_cons_cons, Nat.add_assoc]

/-- Mapping the elements of a string by `f` pulls the forbidden relation back along `f`, as in
`List.isChain_map`. -/
theorem ofForbiddenPairs_map (f : β → α) (w : List β) :
    ofForbiddenPairs R (w.map f) = ofForbiddenPairs (fun a b ↦ R (f a) (f b)) w := by
  induction w using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons a b w _ ih => simp only [List.map_cons, ofForbiddenPairs_cons_cons] at ih ⊢; rw [ih]

/-- Two first elements related alike give a string the same violations. -/
theorem ofForbiddenPairs_congr_head {a b : α} (h : ∀ x, R a x ↔ R b x) (w : List α) :
    ofForbiddenPairs R (a :: w) = ofForbiddenPairs R (b :: w) := by
  cases w <;> simp [h]

/-- Two last elements related alike give a string the same violations. -/
theorem ofForbiddenPairs_congr_last {a b : α} (h : ∀ x, R x a ↔ R x b) (w : List α) :
    ofForbiddenPairs R (w ++ [a]) = ofForbiddenPairs R (w ++ [b]) := by
  induction w with
  | nil => simp
  | cons c t ih => cases t with
    | nil => simp [h]
    | cons d t => simpa using ih

end ofForbiddenPairs

section ocp

variable [DecidableEq α]

@[simp] theorem ocp_nil : ocp ([] : List α) = 0 := rfl

@[simp] theorem ocp_singleton (a : α) : ocp [a] = 0 := rfl

@[simp] theorem ocp_cons_cons (a b : α) (w : List α) :
    ocp (a :: b :: w) = (if a = b then 1 else 0) + ocp (b :: w) := rfl

/-- A string satisfies the OCP iff no two adjacent elements are identical. -/
theorem ocp_eq_zero_iff {w : List α} : ocp w = 0 ↔ OCP.IsClean w :=
  ofForbiddenPairs_eq_zero_iff

/-- An injective relabelling of the elements preserves the OCP's violations, as
`List.map_destutter_ne` preserves the fusion of identical neighbours. -/
theorem ocp_map_of_injective [DecidableEq β] {f : β → α} (hf : Function.Injective f)
    (w : List β) : ocp (w.map f) = ocp w := by
  simp only [ocp, ofForbiddenPairs_map, hf.eq_iff]

end ocp

end OptimalityTheory.Constraint
