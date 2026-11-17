module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Gender.Basic

/-!
# Gender assignment systems

An assignment system gives each noun of a language its gender from what the noun means and from
its form. Its semantic rules are a partial function of the meaning and its formal rules,
morphological or phonological, a partial function of the form; the semantic rules take
precedence, the formal rules decide the nouns they leave, and a residue gender takes what
neither covers. A formal rule that wins over a semantic one, as the German diminutives make
*Männchen* 'little man' neuter, is outside such a system. The nouns the semantic rules cover are
the semantic core, [where gender is a function of meaning](##Gender.AssignmentSystem.factorsThrough_semanticCore)
and [exactly where it is natural](##Gender.AssignmentSystem.isNatural_iff_mem_semanticCore).
Typological work finds no system that is formal alone, that is, none with an empty semantic
core.

## Implementation notes

The system is typed by the meaning `σ` its semantic rules read and the form `φ` its formal
rules read; a language's fragment supplies the maps from nouns to both. Several rules of one
kind applying in order are one partial function, the first defined value
(`List.findSome?`).

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

/-- An assignment system consists of the semantic rules, the formal rules and the residue
gender. -/
structure AssignmentSystem (σ φ G : Type*) where
  /-- The semantic rules, the gender they give a meaning where they apply. -/
  semantic : σ → Option G
  /-- The formal rules, the gender they give a form where they apply. -/
  formal : φ → Option G
  /-- The gender of nouns no rule covers. -/
  residue : G

namespace AssignmentSystem

variable {N σ φ G : Type*} (A : AssignmentSystem σ φ G) (sem : N → σ) (form : N → φ)

/-- The gender of a noun is the one the semantic rules give its meaning, else the one the formal
rules give its form, else the residue gender. -/
def assign (n : N) : G := ((A.semantic (sem n)).or (A.formal (form n))).getD A.residue

/-- A strict semantic system has no formal rule that applies. -/
def IsStrictSemantic : Prop := ∀ x, A.formal x = none

/-- The semantic core is the set of nouns the semantic rules cover. -/
def semanticCore : Set N := {n | (A.semantic (sem n)).isSome}

variable {A sem form} {n : N} {g : G}

/-- The semantic rules decide the nouns they cover. -/
theorem assign_of_semantic (hs : A.semantic (sem n) = some g) : A.assign sem form n = g := by
  simp [assign, hs]

theorem assign_of_semantic_eq_none (h : A.semantic (sem n) = none) :
    A.assign sem form n = (A.formal (form n)).getD A.residue := by
  simp [assign, h]

/-- A formal rule decides in the semantic residue. -/
theorem assign_of_formal (h₁ : A.semantic (sem n) = none) (h₂ : A.formal (form n) = some g) :
    A.assign sem form n = g := by
  simp [assign, h₁, h₂]

theorem assign_of_residue (h₁ : A.semantic (sem n) = none) (h₂ : A.formal (form n) = none) :
    A.assign sem form n = A.residue := by
  simp [assign, h₁, h₂]

/-- In a strict semantic system the gender is a function of the meaning. -/
theorem factorsThrough_of_isStrictSemantic (h : A.IsStrictSemantic) :
    Function.FactorsThrough (A.assign sem form) sem := fun a b hab ↦ by
  simp [assign, h _, hab]

/-- Gender is a function of meaning on the semantic core. -/
theorem factorsThrough_semanticCore :
    ((A.semanticCore sem).domRestrict (A.assign sem form)).FactorsThrough
      ((A.semanticCore sem).domRestrict sem) :=
  fun a b hab ↦ by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 b.2
    have hab' : sem a = sem b := hab
    simp only [Set.domRestrict_apply, assign, hab', hg, Option.some_or, Option.getD_some]

/-- A noun's gender is natural exactly when the noun lies in the semantic core. -/
theorem isNatural_iff_mem_semanticCore (n : N) :
    IsNatural A.semantic sem (A.assign sem form) n ↔ n ∈ A.semanticCore sem := by
  cases hs : A.semantic (sem n) <;> simp [IsNatural, semanticCore, assign, hs]

end AssignmentSystem

end Gender
