/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Linglib.Core.LinearAlgebra.Matrix.DotProduct
public import Linglib.Core.Order.Argmax

/-!
# Harmony

A Harmonic Grammar gives each constraint of a constraint set a weight. The harmony of a candidate
`c` is the negated weighted sum of its violations, `harmonyScore con w c = -(w ⬝ᵥ C(c))`, and a
candidate of higher harmony is more grammatical. The weight vector plays the role of an OT
ranking. `harmony T w` is the same quantity for violation vectors `T c` that need not be counts.

The difference of two harmonies [is](##HarmonicGrammar.harmonyScore_sub) the weight vector against
the violation difference. Harmony [is additive](##HarmonicGrammar.harmonyScore_joint) over jointly
evaluated constraint sets, so that [one tableau
suffices](##OptimalityTheory.ConstraintSystem.hgLanguage_joint) for the grammar's language. With
non-negative weights, a candidate with no more violations than another on every constraint [has
at least its harmony](##HarmonicGrammar.harmonyScore_le_of_forall_le): harmonic bounding.

## Implementation notes

The weight ring is a parameter, so that a grammar with rational or integer weights keeps its
scores exactly computable.

## References

* [smolensky-legendre-2006]
* [prince-smolensky-1993]
* [magri-storme-2021]
* [magri-2015]
-/

@[expose] public section

namespace HarmonicGrammar

open OptimalityTheory

variable {C ι R : Type*} {n : ℕ}

/-- The violation vector `C(c)` of a candidate, its violations of each constraint, a row of a
tableau. -/
def _root_.OptimalityTheory.ConstraintSet.violations [Ring R] (con : ConstraintSet C ι) (c : C) :
    ι → R :=
  fun j ↦ (con j c : R)

@[simp] theorem _root_.OptimalityTheory.ConstraintSet.violations_apply [Ring R]
    (con : ConstraintSet C ι) (c : C) (j : ι) : con.violations c j = (con j c : R) := rfl

variable [Fintype ι]

/-! ### Harmony -/

/-- The harmony `-(w ⬝ᵥ T c)` of a candidate whose violations `T c` may be any elements of the
weight ring, as when a lexicon scales the violations of faithfulness constraints. -/
def harmony [Ring R] (T : C → ι → R) (w : ι → R) (c : C) : R :=
  -(w ⬝ᵥ T c)

/-- The **harmony** `H(c) = -(w ⬝ᵥ C(c))` of a candidate ([smolensky-legendre-2006]) is the
negated weighted sum of its violations under the weight vector `w`, and higher harmony is more
grammatical. It is `harmony` at the violation counts of a constraint set. -/
def harmonyScore [Ring R] (con : ConstraintSet C ι) (w : ι → R) (c : C) : R :=
  harmony con.violations w c

theorem harmonyScore_def [Ring R] (con : ConstraintSet C ι) (w : ι → R) (c : C) :
    harmonyScore con w c = -(w ⬝ᵥ fun j ↦ (con j c : R)) := rfl

theorem harmonyScore_eq_neg_sum [Ring R] (con : ConstraintSet C ι) (w : ι → R) (c : C) :
    harmonyScore con w c = -∑ j, w j * (con j c : R) := rfl

@[simp] theorem harmony_violations [Ring R] (con : ConstraintSet C ι) (w : ι → R) :
    harmony con.violations w = harmonyScore con w := rfl

theorem harmony_add [Ring R] (T : C → ι → R) (w w' : ι → R) :
    harmony T (w + w') = harmony T w + harmony T w' := by
  funext c
  simp only [harmony, Pi.add_apply, add_dotProduct, neg_add]

theorem harmony_smul [CommRing R] (T : C → ι → R) (r : R) (w : ι → R) :
    harmony T (r • w) = r • harmony T w := by
  funext c
  simp [harmony, smul_dotProduct]

theorem harmony_sum [Ring R] {κ D : Type*} [Fintype κ] (T : κ → D → ι → R) (w : ι → R)
    (f : κ → D) : harmony (fun f ↦ ∑ k, T k (f k)) w f = ∑ k, harmony (T k) w (f k) := by
  simp [harmony, dotProduct_sum]

/-- The violation difference `C(a) - C(b)` of two candidates, a row of a comparative
tableau. -/
def _root_.OptimalityTheory.ConstraintSet.violationDiff [Ring R] (con : ConstraintSet C ι)
    (a b : C) : ι → R :=
  fun j ↦ (con j a : R) - con j b

/-- The harmony difference of two candidates is the weight vector against their violation
difference. -/
theorem harmonyScore_sub [Ring R] (con : ConstraintSet C ι) (w : ι → R) (a b : C) :
    harmonyScore con w a - harmonyScore con w b = -(w ⬝ᵥ con.violationDiff a b) := by
  rw [show con.violationDiff a b = (fun j ↦ (con j a : R)) - fun j ↦ (con j b : R) from rfl,
    dotProduct_sub, neg_sub, harmonyScore_def, harmonyScore_def, neg_sub_neg]

/-- The candidate `a` harmonically dominates `b` when `H(a) > H(b)`. The relation is the
pullback of `>` along `harmonyScore con w` (`Order.Preimage`), so it inherits `IsStrictOrder`
from the weight ring. -/
def harmonyDominates [Ring R] [LT R] (con : ConstraintSet C ι) (w : ι → R) : C → C → Prop :=
  harmonyScore con w ⁻¹'o (· > ·)

@[simp] theorem harmonyDominates_iff [Ring R] [LT R] (con : ConstraintSet C ι) (w : ι → R)
    (a b : C) : harmonyDominates con w a b ↔ harmonyScore con w b < harmonyScore con w a :=
  Iff.rfl

@[simp] theorem harmonyScore_comap [Ring R] {D : Type*} (f : C → D) (con : ConstraintSet D ι)
    (w : ι → R) (c : C) : harmonyScore (con.comap f) w c = harmonyScore con w (f c) := rfl

/-! ### Evaluation by cons-recursion -/

@[simp] theorem harmonyScore_nil (con : ConstraintSet C (Fin 0)) (w : Fin 0 → ℝ) (x : C) :
    harmonyScore con w x = 0 := by
  simp [harmonyScore_def, dotProduct]

@[simp] theorem harmonyScore_cons (c₀ : Constraint C) (con : ConstraintSet C (Fin n))
    (w₀ : ℝ) (w : Fin n → ℝ) (x : C) :
    harmonyScore (Matrix.vecCons c₀ con) (Matrix.vecCons w₀ w) x =
      -(w₀ * (c₀ x : ℝ)) + harmonyScore con w x := by
  simp only [harmonyScore_def, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, neg_add]

@[simp] theorem harmonyScore_zero_weight (con : ConstraintSet C ι) (x : C) :
    harmonyScore con (0 : ι → ℝ) x = 0 := by
  simp [harmonyScore_def]

/-- Harmony depends only on the violation vector. -/
theorem harmonyScore_congr {con : ConstraintSet C ι} {w : ι → ℝ} {a b : C}
    (h : ∀ j, con j a = con j b) : harmonyScore con w a = harmonyScore con w b := by
  simp [harmonyScore_def, h]

/-! ### Concatenated and jointly evaluated constraint sets -/

/-- Harmony is additive over a concatenated constraint set and weight vector. -/
theorem harmonyScore_append {m : ℕ} (c₁ : ConstraintSet C (Fin n))
    (c₂ : ConstraintSet C (Fin m)) (w₁ : Fin n → ℝ) (w₂ : Fin m → ℝ) (x : C) :
    harmonyScore (Fin.append c₁ c₂) (Fin.append w₁ w₂) x =
      harmonyScore c₁ w₁ x + harmonyScore c₂ w₂ x := by
  simp [harmonyScore_def, dotProduct, Fin.sum_univ_add, add_comm]

/-- The harmony of a jointly evaluated constraint set is the sum of the mappings'
harmonies — constraint summation is innocuous for harmony ([magri-storme-2021]). -/
theorem harmonyScore_joint {κ I O : Type*} [Fintype κ] (inputs : κ → I)
    (con : ConstraintSet (I × O) ι) (w : ι → ℝ) (f : κ → O) :
    harmonyScore (con.joint inputs) w f = ∑ i, harmonyScore con w (inputs i, f i) := by
  simp only [harmonyScore_def, dotProduct, ConstraintSet.joint_apply, Constraint.joint_apply,
    Nat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

/-! ### Harmonic bounding (Pareto dominance) -/

variable {con : ConstraintSet C ι} {w : ι → ℝ} {a b : C}

/-- With non-negative weights, a candidate incurring no more violations than `b` on every
constraint has at least `b`'s harmony, which is harmonic bounding ([prince-smolensky-1993]). -/
theorem harmonyScore_le_of_forall_le (hw : 0 ≤ w) (h : ∀ i, con i a ≤ con i b) :
    harmonyScore con w b ≤ harmonyScore con w a :=
  neg_le_neg (dotProduct_le_dotProduct_of_nonneg_left (fun i ↦ Nat.cast_le.2 (h i)) hw)

/-- Strictly fewer violations on some positively weighted constraint give strictly greater
harmony. -/
theorem harmonyDominates_of_lt (hw : 0 ≤ w) (hle : ∀ i, con i a ≤ con i b)
    (hlt : ∃ i, 0 < w i ∧ con i a < con i b) :
    harmonyDominates con w a b :=
  neg_lt_neg (dotProduct_lt_dotProduct_of_nonneg_left (fun i ↦ Nat.cast_le.2 (hle i)) hw
    (hlt.imp fun _ h ↦ ⟨h.1, Nat.cast_lt.2 h.2⟩))

/-! ### The languages of a constraint system -/

section System

variable {I O : Type*}

/-- The **HG language** of a weighting assigns each input its candidates of greatest harmony. -/
def _root_.OptimalityTheory.ConstraintSystem.hgLanguage [Ring R] [Preorder R] [DecidableLE R]
    (S : ConstraintSystem I O ι) (w : ι → R) (i : I) : Finset O :=
  (S.gen i).argmax (harmonyScore (S.conAt i) w)

/-- The HG language of the joint system is the product of the system's HG languages, so that one
HG tableau suffices as one OT tableau does ([magri-2015]). -/
theorem _root_.OptimalityTheory.ConstraintSystem.hgLanguage_joint [Fintype I] [DecidableEq I]
    (S : ConstraintSystem I O ι) (w : ι → ℝ) :
    S.joint.hgLanguage w () = Fintype.piFinset (S.hgLanguage w) := by
  ext f
  rw [Fintype.mem_piFinset, ConstraintSystem.hgLanguage,
    show harmonyScore (S.joint.conAt ()) w = fun g ↦ ∑ i, harmonyScore (S.conAt i) w (g i) from
      funext fun g ↦ harmonyScore_joint id S.con w g]
  exact Finset.mem_argmax_piFinset_sum S.gen fun i ↦ harmonyScore (S.conAt i) w

end System

end HarmonicGrammar
