/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Constraints

This file defines the violable constraints of Optimality Theory ([prince-smolensky-1993]), which
Harmonic Grammar, MaxEnt and optimality-theoretic work in syntax and semantics adopt. A constraint
is a function `C → ℕ` that counts the violations of each candidate. It stores no name and no
faithfulness or markedness tag, since a constraint is its evaluation function. The
faithfulness–markedness distinction is a structural property of correspondence candidates
(`OptimalityTheory.Correspondence`), where markedness factors through the output and faithfulness
vanishes on the identity candidate, and a constraint over an opaque candidate type has no family.

## Main definitions

* `OptimalityTheory.Constraint C`: a violation-counting function `C → ℕ`.
* `Constraint.binary`: the indicator constraint of a decidable predicate.
* `Constraint.comap`, `ConstraintSet.comap`: the pullback of a constraint or constraint set along
  a candidate map.
* `ConstraintSet C ι`: a grammar's constraint set, CON, a family of constraints indexed by `ι`.
* `Constraint.joint`, `ConstraintSet.joint`: joint evaluation on output tuples by constraint
  summation.
* `ConstraintSystem I O ι`: a constraint system, each input's candidates (GEN) and a constraint
  set on input–output mappings (CON); `ConstraintSystem.joint` its single-input Minkowski sum.

The Harmonic Grammar scores of a constraint set are in `HarmonicGrammar/Harmony.lean`.

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative Grammar*
  (1993)][prince-smolensky-1993]
* [J. D. Alderete, *Dominance Effects as Trans-derivational Anti-faithfulness*
  (2001)][alderete-2001]
* [A. Prince, *One Tableau Suffices* (2015)][prince-2015]
* [G. Magri and B. Storme, *Constraint Summation in Phonological Theory* (2021)][magri-storme-2021]
-/

@[expose] public section

namespace OptimalityTheory

/-- An OT or Harmonic-Grammar **constraint** is a function counting the violations of each
candidate. Whether it is a faithfulness or a markedness constraint is a structural property (see
`OptimalityTheory.Correspondence`), not a stored tag. -/
abbrev Constraint (C : Type*) := C → ℕ

variable {C D : Type*}

/-- The **binary** constraint of a decidable predicate `P` assigns one violation when `P c`
holds and none otherwise. Every binary markedness or faithfulness constraint has this shape, and
which of the two it is follows from its structure, not from the constructor. -/
def Constraint.binary (P : C → Prop) [DecidablePred P] : Constraint C :=
  fun c => if P c then 1 else 0

@[simp] theorem Constraint.binary_apply (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c = if P c then 1 else 0 := rfl

/-- A binary constraint never assigns more than one violation. -/
theorem Constraint.binary_le_one (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c ≤ 1 := by
  simp only [Constraint.binary]; split <;> omega

/-- A binary constraint is satisfied exactly when its predicate fails. -/
theorem Constraint.binary_eq_zero_iff (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c = 0 ↔ ¬P c := by
  simp [Constraint.binary]

/-- A binary constraint is violated exactly when its predicate holds. -/
theorem Constraint.binary_eq_one_iff (P : C → Prop) [DecidablePred P] (c : C) :
    Constraint.binary P c = 1 ↔ P c := by
  simp [Constraint.binary]

/-- The anti-faithfulness constraint `¬F` of a constraint `F` ([alderete-2001]) is satisfied
exactly when `F` is violated at least once, so it demands one violation and no more. -/
def Constraint.antifaithful (F : Constraint C) : Constraint C := Constraint.binary (F · = 0)

theorem Constraint.antifaithful_eq_zero_iff (F : Constraint C) (c : C) :
    F.antifaithful c = 0 ↔ 0 < F c := by
  simp [Constraint.antifaithful, Constraint.binary, Nat.pos_iff_ne_zero]

theorem Constraint.antifaithful_eq_one_iff (F : Constraint C) (c : C) :
    F.antifaithful c = 1 ↔ F c = 0 := by
  simp [Constraint.antifaithful, Constraint.binary]

/-- The pullback of a `D`-constraint along `f : C → D` evaluates it on the image of each
candidate, so a specific candidate type can reuse a constraint defined on a more general one. -/
def Constraint.comap (f : C → D) (con : Constraint D) : Constraint C := con ∘ f

@[simp] theorem Constraint.comap_apply (f : C → D) (con : Constraint D) (c : C) :
    Constraint.comap f con c = con (f c) := rfl

/-! ### Joint evaluation

A **systemic** constraint — \*HOMOPHONY, a distinctiveness constraint — scores a
whole system of outputs, so its candidate is an output tuple `f : κ → O` assigning
each input `inputs i` its output. A per-mapping constraint on `I × O` is lifted to
output tuples by **constraint summation** ([prince-2015], [magri-storme-2021]), which
sums its violations on `f` over the mappings `(inputs i, f i)`. -/

variable {κ I O : Type*} [Fintype κ]

/-- The joint evaluation of a per-mapping constraint on an output tuple sums its violations
over the mappings `(inputs i, f i)`. -/
def Constraint.joint (inputs : κ → I) (con : Constraint (I × O)) : Constraint (κ → O) :=
  fun f => ∑ i, con (inputs i, f i)

@[simp] theorem Constraint.joint_apply (inputs : κ → I) (con : Constraint (I × O)) (f : κ → O) :
    con.joint inputs f = ∑ i, con (inputs i, f i) := rfl

/-- A grammar's **constraint set**, CON in [prince-smolensky-1993], is a family of constraints over
candidates `C` indexed by the constraint names `ι`. An OT grammar ranks it (a `Ranking ι n`), a
Harmonic Grammar weights its violations by a vector `ι → ℝ`, and MaxEnt takes the softmax of the
resulting harmonies. A constraint set written as a vector `![C₀, …]` is indexed by `Fin n`. -/
abbrev ConstraintSet (C : Type*) (ι : Type*) := ι → Constraint C

namespace ConstraintSet

variable {ι : Type*}

/-- The pullback of a constraint set along a candidate map pulls back each constraint. -/
def comap (f : C → D) (con : ConstraintSet D ι) : ConstraintSet C ι := fun i ↦ (con i).comap f

@[simp] theorem comap_apply (f : C → D) (con : ConstraintSet D ι) (i : ι) (c : C) :
    con.comap f i c = con i (f c) := rfl

/-- The joint evaluation of a constraint set evaluates each constraint jointly. -/
def joint (inputs : κ → I) (con : ConstraintSet (I × O) ι) : ConstraintSet (κ → O) ι :=
  fun j ↦ (con j).joint inputs

@[simp] theorem joint_apply (inputs : κ → I) (con : ConstraintSet (I × O) ι) (j : ι) :
    con.joint inputs j = (con j).joint inputs := rfl

end ConstraintSet

/-! ### Constraint systems -/

/-- A **constraint system** pairs each input's candidate outputs, GEN, with a constraint set on
input–output mappings, CON ([prince-smolensky-1993]). Optimality Theory ranks the constraints and
Harmonic Grammar weights them, and either way a grammar evaluates each input's candidates. -/
structure ConstraintSystem (I O ι : Type*) where
  /-- The candidate outputs of each input. -/
  gen : I → Finset O
  /-- The constraints, evaluated on input–output mappings. -/
  con : ConstraintSet (I × O) ι

/-- The constraints of a system at an input, evaluated on its outputs. -/
def ConstraintSystem.conAt {I O ι : Type*} (S : ConstraintSystem I O ι) (i : I) :
    ConstraintSet O ι :=
  S.con.comap (i, ·)

@[simp] theorem ConstraintSystem.conAt_apply {I O ι : Type*} (S : ConstraintSystem I O ι) (i : I)
    (j : ι) (o : O) : S.conAt i j o = S.con j (i, o) := rfl

/-- The **joint** system of a system with finitely many inputs has a single input, whose
candidates are the tuples choosing a candidate for every input; each constraint sums its
violations over the inputs. Its tableau is the Minkowski sum of the system's tableaux
([prince-2015]). -/
def ConstraintSystem.joint {I O ι : Type*} [Fintype I] [DecidableEq I]
    (S : ConstraintSystem I O ι) : ConstraintSystem Unit (I → O) ι where
  gen _ := Fintype.piFinset S.gen
  con := (S.con.joint id).comap Prod.snd

end OptimalityTheory
