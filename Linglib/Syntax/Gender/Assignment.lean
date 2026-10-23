module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Gender.Basic

/-!
# Gender assignment systems

This file defines an assignment system, the rules by which a language assigns its nouns to
genders, and its semantic core.

An assignment system reads a noun's meaning through semantic rules and its form through
formal rules, morphological or phonological; the semantic rules take precedence, the formal
rules sort the semantic residue, and the residue gender catches what neither covers. No
attested system is formal alone: every system assigns by meaning on some nonempty set of
nouns, its semantic core, which here is the set of nouns the semantic rules cover, so that
the core determines gender by meaning as a theorem rather than a stipulation.

## Main definitions

* `Gender.AssignmentSystem`: semantic rules, formal rules and a residue gender.
* `Gender.AssignmentSystem.assign`: the gender of a noun under the rules, in order.
* `Gender.AssignmentSystem.IsStrictSemantic`: a system with no formal rules.
* `Gender.AssignmentSystem.semanticCore`: the nouns the semantic rules cover.

## Main results

* `Gender.AssignmentSystem.assign_of_formal`: a formal rule decides only in the semantic
  residue.
* `Gender.AssignmentSystem.factorsThrough_semanticCore`: on the semantic core, gender is
  a function of meaning.
* `Gender.AssignmentSystem.factorsThrough_of_isStrictSemantic`: in a strict semantic system,
  gender is a function of meaning everywhere.

## Implementation notes

The system is typed by the meaning `σ` its semantic rules read and the form `φ` its formal
rules read; a language's fragment supplies the maps from nouns to both. The rules are total
functions to an optional gender, so their order of application is fixed by construction.

## References

* [corbett-1991] — chapters 2 and 3: semantic and formal assignment, and the semantic core
* [dahl-2000] — the animacy refinement of the semantic core
* [kramer-2015] — the semantic core generalization restated
-/

@[expose] public section

namespace Gender

/-- An assignment system consists of semantic rules reading a noun's meaning, formal rules
reading its form, and the residue gender. -/
structure AssignmentSystem (σ φ G : Type*) where
  /-- The semantic rules, as a partial function of the meaning. -/
  semantic : σ → Option G
  /-- The formal rules, morphological or phonological, as a partial function of the form. -/
  formal : φ → Option G
  /-- The gender of nouns no rule covers. -/
  residue : G

namespace AssignmentSystem

variable {N σ φ G : Type*} (A : AssignmentSystem σ φ G) (sem : N → σ) (form : N → φ)

/-- The gender of a noun is decided by the semantic rules first, then by the formal rules on the
semantic residue, and by the residue gender last. -/
def assign (n : N) : G := ((A.semantic (sem n)).or (A.formal (form n))).getD A.residue

theorem assign_of_semantic {n : N} {g : G} (h : A.semantic (sem n) = some g) :
    A.assign sem form n = g := by
  simp [assign, h]

/-- Semantic rules take precedence, so a formal rule decides only in the semantic residue. -/
theorem assign_of_formal {n : N} {g : G} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = some g) : A.assign sem form n = g := by
  simp [assign, h₁, h₂]

theorem assign_of_residue {n : N} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = none) : A.assign sem form n = A.residue := by
  simp [assign, h₁, h₂]

/-- A strict semantic system has no formal rules. -/
def IsStrictSemantic : Prop := ∀ x, A.formal x = none

/-- In a strict semantic system the gender is a function of the meaning. -/
theorem factorsThrough_of_isStrictSemantic (h : A.IsStrictSemantic) :
    Function.FactorsThrough (A.assign sem form) sem := fun a b hab ↦ by
  simp [assign, hab, h (form a), h (form b)]

/-- The semantic core is the set of nouns the semantic rules cover. -/
def semanticCore : Set N := {n | (A.semantic (sem n)).isSome}

/-- On the semantic core, gender is a function of meaning. -/
theorem factorsThrough_semanticCore :
    ((A.semanticCore sem).domRestrict (A.assign sem form)).FactorsThrough
      ((A.semanticCore sem).domRestrict sem) :=
  fun a b hab ↦ by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 b.2
    have hab' : sem a = sem b := hab
    simp [assign, hab', hg]

end AssignmentSystem

end Gender
