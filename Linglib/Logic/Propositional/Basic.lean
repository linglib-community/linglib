/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Insert

/-!
# Propositional formulas

`Propositional.Formula Atom` is the language of propositional logic over the atoms `Atom`, built
by negation, conjunction, disjunction and the conditional. `Formula.evalBool` is its classical
evaluation on a Boolean valuation, and `Formula.atoms` is the set of atoms that occur in a
formula. Many-valued semantics for the same language are in `Logic/Propositional/Trivalent.lean`.
-/

@[expose] public section

namespace Propositional

/-- Propositional formulas over an atom type, built by negation, conjunction, disjunction and the
conditional. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  | cond : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq

namespace Formula

variable {Atom : Type*}

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

/-- The atoms that occur in a formula. -/
def atoms : Formula Atom → Set Atom
  | .atom a => {a}
  | .neg φ => atoms φ
  | .conj φ ψ => atoms φ ∪ atoms ψ
  | .disj φ ψ => atoms φ ∪ atoms ψ
  | .cond φ ψ => atoms φ ∪ atoms ψ

@[simp] theorem atoms_atom (a : Atom) : (atom a).atoms = {a} := rfl

@[simp] theorem atoms_neg (φ : Formula Atom) : φ.neg.atoms = φ.atoms := rfl

@[simp] theorem atoms_conj (φ ψ : Formula Atom) : (φ.conj ψ).atoms = φ.atoms ∪ ψ.atoms := rfl

@[simp] theorem atoms_disj (φ ψ : Formula Atom) : (φ.disj ψ).atoms = φ.atoms ∪ ψ.atoms := rfl

@[simp] theorem atoms_cond (φ ψ : Formula Atom) : (φ.cond ψ).atoms = φ.atoms ∪ ψ.atoms := rfl

end Formula

end Propositional
