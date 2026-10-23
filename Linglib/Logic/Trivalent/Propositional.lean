/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Consequence

/-!
# Trivalent propositional logic

Propositional formulas built from atoms by negation, conjunction, disjunction and the conditional
are evaluated into `SignType` by an interpretation of the binary connectives, the Strong, Weak or
Middle Kleene tables or Cooper's or de Finetti's, with Kleene's negation throughout. A formula is
realized at a designation standard when its value is designated: K3 designates only `1` and LP also
`0`, so one evaluation yields both logics, and mixed consequence takes premises at one standard and
conclusions at another, as Cobreros, Égré, Ripley and van Rooij do.

## Main definitions

* `Trivalent.Formula`, `Trivalent.Formula.eval`: formulas and their values under the connectives.
* `Trivalent.Model.ofBool`: the Boolean model of a classical valuation of the atoms.
* `Trivalent.Formula.Realize`: realization at a designation standard, written `M ⊨[C, d] φ`.
* `Trivalent.Consequence`: mixed consequence over designation standards.

## Main results

* `Trivalent.Formula.realize_neg`, `Trivalent.Formula.isDual`: under any connectives negation
  swaps the standards.
* `Trivalent.consequence_iff_dual`: `Γ ⊨ Δ` in K3 iff `¬Δ ⊨ ¬Γ` in LP.
* `Trivalent.Formula.eval_ofBool`: on a Boolean model the Strong Kleene tables are classical.
* `Trivalent.k3_no_tautologies`, `Trivalent.lp_all_satisfiable`: the model sending every atom to
  `0` gives Strong Kleene K3 no tautologies and LP no unsatisfiable formula.
* `Trivalent.lp_no_explosion`: LP is paraconsistent.

## Implementation notes

The API mirrors `Mathlib.ModelTheory` (`Realize`, per-constructor `@[simp]` lemmas, `⊨` notation),
and consequence is the multiple-conclusion, list-based `MixedConsequence` rather than theories as
sets. The language has no constants, so `⊤` and `⊥` are `p ∨ ¬p` and `p ∧ ¬p` for an atom `p`, and
the model sending every atom to `0` voids every formula under the Strong Kleene tables.

## References

* [kleene-1952]
* [cobreros-etal-2012]
-/

@[expose] public section

namespace Trivalent

open SignType

open Consequence (IsDual MixedConsequence mixedConsequence_iff_dual)

/-- Propositional formulas over an atom type, built by negation, conjunction, disjunction and the
conditional. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | cond : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

/-- A trivalent model assigns a value to each atom. -/
abbrev Model (Atom : Type*) := Atom → SignType

/-- The Boolean model of a classical valuation of the atoms, which leaves no atom void. -/
def Model.ofBool {Atom : Type*} (v : Atom → Bool) : Model Atom := fun a ↦ ofProp (v a)

@[simp] theorem Model.ofBool_apply {Atom : Type*} (v : Atom → Bool) (a : Atom) :
    Model.ofBool v a = ofProp (v a) := rfl

namespace Formula

variable {Atom : Type*}

/-- The value of a formula under the connectives `C` in the model `M`. -/
def eval (C : Connectives) (M : Model Atom) : Formula Atom → SignType
  | .atom a => M a
  | .neg φ => -eval C M φ
  | .conj φ ψ => C.conj (eval C M φ) (eval C M ψ)
  | .disj φ ψ => C.disj (eval C M φ) (eval C M ψ)
  | .cond φ ψ => C.cond (eval C M φ) (eval C M ψ)

section Eval

variable (C : Connectives) (M : Model Atom)

@[simp] theorem eval_atom (a : Atom) : eval C M (.atom a) = M a := rfl

@[simp] theorem eval_neg (φ : Formula Atom) : eval C M (.neg φ) = -eval C M φ := rfl

@[simp] theorem eval_conj (φ ψ : Formula Atom) :
    eval C M (.conj φ ψ) = C.conj (eval C M φ) (eval C M ψ) := rfl

@[simp] theorem eval_disj (φ ψ : Formula Atom) :
    eval C M (.disj φ ψ) = C.disj (eval C M φ) (eval C M ψ) := rfl

@[simp] theorem eval_cond (φ ψ : Formula Atom) :
    eval C M (.cond φ ψ) = C.cond (eval C M φ) (eval C M ψ) := rfl

end Eval

/-- Classical evaluation on a Boolean valuation. -/
def evalBool (v : Atom → Bool) : Formula Atom → Bool
  | .atom a => v a
  | .neg φ => !evalBool v φ
  | .conj φ ψ => evalBool v φ && evalBool v ψ
  | .disj φ ψ => evalBool v φ || evalBool v ψ
  | .cond φ ψ => !evalBool v φ || evalBool v ψ

@[simp] theorem evalBool_atom (v : Atom → Bool) (a : Atom) : evalBool v (.atom a) = v a := rfl

@[simp] theorem evalBool_neg (v : Atom → Bool) (φ : Formula Atom) :
    evalBool v (.neg φ) = !evalBool v φ := rfl

@[simp] theorem evalBool_conj (v : Atom → Bool) (φ ψ : Formula Atom) :
    evalBool v (.conj φ ψ) = (evalBool v φ && evalBool v ψ) := rfl

@[simp] theorem evalBool_disj (v : Atom → Bool) (φ ψ : Formula Atom) :
    evalBool v (.disj φ ψ) = (evalBool v φ || evalBool v ψ) := rfl

@[simp] theorem evalBool_cond (v : Atom → Bool) (φ ψ : Formula Atom) :
    evalBool v (.cond φ ψ) = (!evalBool v φ || evalBool v ψ) := rfl

private theorem strongKleene_ofProp (x y : Bool) :
    Connectives.strongKleene.conj (ofProp x) (ofProp y) = ofProp (x && y) ∧
      Connectives.strongKleene.disj (ofProp x) (ofProp y) = ofProp (x || y) ∧
      Connectives.strongKleene.cond (ofProp x) (ofProp y) = ofProp (!x || y) := by
  cases x <;> cases y <;> decide

/-- On a Boolean model the strong Kleene tables are the classical ones. -/
theorem eval_ofBool (v : Atom → Bool) (φ : Formula Atom) :
    eval .strongKleene (Model.ofBool v) φ = ofProp (evalBool v φ) := by
  induction φ with
  | atom a => rfl
  | neg φ ih => rw [eval_neg, evalBool_neg, ih]; cases evalBool v φ <;> decide
  | conj φ ψ ihφ ihψ => rw [eval_conj, ihφ, ihψ]; exact (strongKleene_ofProp _ _).1
  | disj φ ψ ihφ ihψ => rw [eval_disj, ihφ, ihψ]; exact (strongKleene_ofProp _ _).2.1
  | cond φ ψ ihφ ihψ => rw [eval_cond, ihφ, ihψ]; exact (strongKleene_ofProp _ _).2.2

/-- A formula is realized at a designation standard when its value under the connectives clears
the threshold, so with the strong Kleene connectives `Realize .strongKleene M .k3` is strong Kleene
satisfaction and `Realize .strongKleene M .lp` is Priest's LP. -/
def Realize (C : Connectives) (M : Model Atom) (d : Trivalent.Designation) (φ : Formula Atom) :
    Prop :=
  d.threshold ≤ eval C M φ

@[inherit_doc] scoped notation:50 M " ⊨[" C ", " d "] " φ => Formula.Realize C M d φ

variable (C : Connectives) (M : Model Atom) (d : Trivalent.Designation)

@[simp] theorem realize_atom (a : Atom) : (M ⊨[C, d] Formula.atom a) ↔ d.threshold ≤ M a :=
  Iff.rfl

/-- Negation swaps the designation standards at the level of formulas, under any connectives. -/
@[simp] theorem realize_neg (φ : Formula Atom) :
    (M ⊨[C, d] Formula.neg φ) ↔ ¬(M ⊨[C, d.dual] φ) := by
  have h := Trivalent.Designation.dual_threshold_le_neg_iff d.dual (eval C M φ)
  rwa [Trivalent.Designation.dual_dual] at h

/-- Each standard is dual to the other along negation ([cobreros-etal-2012], Definition 20). -/
theorem isDual :
    IsDual Formula.neg (fun M : Model Atom ↦ Realize C M d.dual) (Realize C · d) := fun _ _ ↦ by
  simp

theorem realize_ofBool (v : Atom → Bool) (φ : Formula Atom) :
    (Model.ofBool v ⊨[.strongKleene, d] φ) ↔ evalBool v φ = Bool.true := by
  rw [Realize, eval_ofBool, Trivalent.Designation.threshold_le_ofProp_iff]

@[simp] theorem realize_conj (φ ψ : Formula Atom) :
    (M ⊨[.strongKleene, d] Formula.conj φ ψ) ↔
      (M ⊨[.strongKleene, d] φ) ∧ (M ⊨[.strongKleene, d] ψ) :=
  le_inf_iff

@[simp] theorem realize_disj (φ ψ : Formula Atom) :
    (M ⊨[.strongKleene, d] φ.disj ψ) ↔ (M ⊨[.strongKleene, d] φ) ∨ (M ⊨[.strongKleene, d] ψ) :=
  le_sup_iff

@[simp] theorem realize_cond (φ ψ : Formula Atom) :
    (M ⊨[.strongKleene, d] φ.cond ψ) ↔
      ((M ⊨[.strongKleene, d.dual] φ) → (M ⊨[.strongKleene, d] ψ)) := by
  change d.threshold ≤ -eval _ M φ ⊔ eval _ M ψ ↔ _
  rw [le_sup_iff, or_iff_not_imp_left]
  exact imp_congr_left ((realize_neg .strongKleene M d φ).not.trans not_not)

end Formula

/-- Mixed consequence under the connectives `C` takes premises at standard `m` and conclusions at
standard `n`. -/
abbrev Consequence {Atom : Type*} (C : Connectives) (m n : Trivalent.Designation)
    (Γ Δ : List (Formula Atom)) : Prop :=
  MixedConsequence (Formula.Realize C · m) (Formula.Realize C · n) Γ Δ

/-! ### Meta-theorems -/

open scoped Formula

variable {Atom : Type*}

/-- Negation dualizes consequence, so `Γ ⊨ Δ` at `m, n` iff `¬Δ ⊨ ¬Γ` at the dual standards, and
K3 and LP are each other's duals ([cobreros-etal-2012], Lemma 6). -/
theorem consequence_iff_dual {C : Connectives} {m n : Trivalent.Designation}
    {Γ Δ : List (Formula Atom)} :
    Consequence C m n Γ Δ ↔ Consequence C n.dual m.dual (Δ.map .neg) (Γ.map .neg) :=
  mixedConsequence_iff_dual (Formula.isDual C m) (Formula.isDual C n)

theorem eval_const_zero (φ : Formula Atom) :
    Formula.eval .strongKleene (fun _ : Atom ↦ 0) φ = 0 := by
  induction φ with
  | atom _ => rfl
  | neg ψ ih => simp [ih]
  | conj ψ χ ihψ ihχ | disj ψ χ ihψ ihχ | cond ψ χ ihψ ihχ =>
    simp only [Formula.eval_conj, Formula.eval_disj, Formula.eval_cond, ihψ, ihχ]
    decide

/-- K3 has no tautologies, since nothing is designated in the model sending every atom to `0`
([cobreros-etal-2012], Theorem 2). -/
theorem k3_no_tautologies [Nonempty Atom] (φ : Formula Atom) :
    ¬(∀ M : Model Atom, M ⊨[.strongKleene, .k3] φ) := by
  intro h
  have := h fun _ ↦ 0
  simp [Formula.Realize, eval_const_zero] at this

/-- Every formula is LP-satisfiable, since the model sending every atom to `0` designates
everything ([cobreros-etal-2012], Theorem 2). -/
theorem lp_all_satisfiable (φ : Formula Atom) :
    (fun _ : Atom ↦ 0) ⊨[.strongKleene, .lp] φ := by
  simp [Formula.Realize, eval_const_zero]

/-- Explosion fails in LP, since `{a ∧ ¬a} ⊭ b` with countermodel `M a = 0` and `M b = -1`. -/
theorem lp_no_explosion :
    ∃ (φ ψ : Formula Bool), ¬Consequence .strongKleene .lp .lp [.conj φ (.neg φ)] [ψ] := by
  refine ⟨.atom Bool.true, .atom Bool.false, fun h ↦ ?_⟩
  have := h (fun b ↦ if b then 0 else -1) fun γ hγ ↦ by
    simp only [List.mem_singleton] at hγ; subst hγ
    simp [Formula.Realize, Connectives.strongKleene]
  simp [Formula.Realize] at this

end Trivalent
