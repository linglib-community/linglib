/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Feature.Gender.Basic

/-!
# Gender assignment systems

An assignment system gives each noun of a language its gender from what the noun means and from
its form. Its semantic rules are a partial function of the meaning and its formal rules,
morphological or phonological, a function of the form; the semantic rules take precedence, and
the formal rules decide the nouns they leave, the semantic residue. The systems here are those
in which meaning wins every conflict: a formal rule that overrides a semantic one, as the German
diminutives make *Männchen* 'little man' neuter, is outside them. The nouns the semantic rules
cover are the semantic core, [where gender is a function of meaning](##Gender.AssignmentSystem.factorsThrough_semanticCore)
and [exactly where it is natural](##Gender.AssignmentSystem.isNatural_iff_mem_semanticCore).
Typological work finds no system that is formal alone, that is, none with an empty semantic
core.

## Implementation notes

The system is typed by the meaning `σ` its semantic rules read and the form `φ` its formal
rules read; a language's language file supplies the maps from nouns to both. Several rules of one
kind applying in order are one partial function, the first defined value
(`List.findSome?`). The formal rules are total, a default gender being their last clause, so a
system with no formal rules has a constant one.

## References

* [corbett-1991] — chapters 2 and 3: semantic and formal assignment, and the semantic core
* [dahl-2000] — the animacy refinement of the semantic core
* [kramer-2015] — the semantic core generalization restated
-/

@[expose] public section

namespace Gender

section Natural

variable {N σ G : Type*}

/-- A noun's gender is natural when the semantic rule assigns it to the noun's meaning. -/
def IsNatural (rule : σ → Option G) (sem : N → σ) (gender : N → G) (n : N) : Prop :=
  rule (sem n) = some (gender n)

instance [DecidableEq G] (rule : σ → Option G) (sem : N → σ) (gender : N → G) :
    DecidablePred (IsNatural rule sem gender) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

end Natural

/-- An assignment system consists of the semantic rules and the formal rules. -/
structure AssignmentSystem (σ φ G : Type*) where
  /-- The semantic rules, the gender they give a meaning where they apply. -/
  semantic : σ → Option G
  /-- The formal rules, the gender they give a form. -/
  formal : φ → G

namespace AssignmentSystem

variable {N σ φ G : Type*} (A : AssignmentSystem σ φ G) (sem : N → σ) (form : N → φ)

/-- The gender of a noun is the one the semantic rules give its meaning where they apply, and
otherwise the one the formal rules give its form. -/
def assign (n : N) : G := (A.semantic (sem n)).getD (A.formal (form n))

/-- A strict semantic system has formal rules that distinguish no forms. -/
def IsStrictSemantic : Prop := ∀ x y, A.formal x = A.formal y

/-- The semantic core is the set of nouns the semantic rules cover. -/
def semanticCore : Set N := {n | (A.semantic (sem n)).isSome}

variable {A sem form} {n : N} {g : G}

/-- The semantic rules decide the nouns they cover. -/
theorem assign_of_semantic (hs : A.semantic (sem n) = some g) : A.assign sem form n = g := by
  simp [assign, hs]

/-- The formal rules decide in the semantic residue. -/
theorem assign_of_semantic_eq_none (h : A.semantic (sem n) = none) :
    A.assign sem form n = A.formal (form n) := by
  simp [assign, h]

/-- In a strict semantic system the gender is a function of the meaning. -/
theorem factorsThrough_of_isStrictSemantic (h : A.IsStrictSemantic) :
    Function.FactorsThrough (A.assign sem form) sem := fun a b hab ↦ by
  simp [assign, h (form a) (form b), hab]

/-- Gender is a function of meaning on the semantic core. -/
theorem factorsThrough_semanticCore :
    ((A.semanticCore sem).domRestrict (A.assign sem form)).FactorsThrough
      ((A.semanticCore sem).domRestrict sem) :=
  fun a b hab ↦ by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 b.2
    have hab' : sem a = sem b := hab
    simp only [Set.domRestrict_apply, assign, hab', hg, Option.getD_some]

/-- A noun's gender is natural exactly when the noun lies in the semantic core. -/
theorem isNatural_iff_mem_semanticCore (n : N) :
    IsNatural A.semantic sem (A.assign sem form) n ↔ n ∈ A.semanticCore sem := by
  cases hs : A.semantic (sem n) <;> simp [IsNatural, semanticCore, assign, hs]

end AssignmentSystem

end Gender
