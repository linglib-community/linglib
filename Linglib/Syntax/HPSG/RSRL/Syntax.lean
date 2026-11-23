module

public import Linglib.Syntax.HPSG.RSRL.Signature
public import Mathlib.Data.Finset.Image

/-!
# RSRL syntax

This file defines the terms and formulae of the description language of RSRL.

A *term* picks out an entity, starting from the one being described: it is the colon, which
stands for that entity, a variable, or a term followed by an attribute. A *formula* says that a
term has a sort, that two terms denote the same entity, or that some variables stand in a
relation, and formulae are closed under negation, implication and universal quantification. A
*description* is a formula with no free variables, and a *grammar* is a set of descriptions.

Most principles of a grammar are *constraints* `σ ⇒ A`, which require the entities of the sort
`σ` to satisfy an attribute-value description `A`: a list of atoms, each giving a path a sort or
equating two paths.

## Implementation notes

Negation, implication and universal quantification are primitive and the other connectives are
defined from them, as in mathlib's `FirstOrder.Language.BoundedFormula`. As in Richter's syntax,
a relation symbol applies to variables only.

A constraint holds its atoms as a list and not as one formula, so that a proof names the atom it
uses and does not reach it by its place in a conjunction, as mathlib's `FieldAxiom` names the
axioms of a field. The formula of a constraint has no quantifier: the conjunction of its atoms
ends in `: ≈ :` and not in `Formula.top`, whose quantifier ranges over the components of the
described entity and would make each check of a worked model compute them.

## References

* [richter-2000]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.RSRL

universe u

variable {Srt : Type u} [PartialOrder Srt]

/-! ### Terms -/

variable (Sig : Signature Srt)

/-- A term of the description language is the colon, a variable, or a term followed by an attribute
([richter-2024], Definition 3). -/
inductive Term where
  /-- The colon denotes the described entity. -/
  | colon : Term
  /-- A variable. -/
  | var : ℕ → Term
  /-- The term `t.feat α` follows the attribute `α` from the entity that `t` denotes. -/
  | feat : Term → Sig.Attr → Term

variable {Sig}

namespace Term

/-- The term that follows the path `p` from the described entity. -/
def path (p : Path Sig) : Term Sig := p.foldl feat colon

@[simp] theorem path_nil : path ([] : Path Sig) = colon := rfl

@[simp] theorem path_concat (p : Path Sig) (α : Sig.Attr) : path (p ++ [α]) = (path p).feat α :=
  List.foldl_concat ..

/-- The variables that occur in a term ([richter-2024], Definition 5). -/
def freeVars : Term Sig → Finset ℕ
  | colon => ∅
  | var n => {n}
  | feat t _ => t.freeVars

@[simp] theorem freeVars_path (p : Path Sig) : (path p).freeVars = ∅ := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p α ih => rw [path_concat]; exact ih

/-- A term is colon-free when it starts at a variable rather than at the described entity. -/
def IsColonFree : Term Sig → Prop
  | colon => False
  | var _ => True
  | feat t _ => t.IsColonFree

instance decidableIsColonFree : DecidablePred (IsColonFree (Sig := Sig))
  | colon => isFalse id
  | var _ => isTrue trivial
  | feat t _ => decidableIsColonFree t

end Term

/-! ### Formulae -/

/-- A formula of the description language is a sort assignment, a path equation or a relational
formula, or is built from formulae by negation, implication and universal quantification
([richter-2024], Definition 4). -/
inductive Formula (Sig : Signature Srt) where
  /-- The sort assignment `t ∼ σ` says that `t` denotes an entity whose sort is at least as
  specific as `σ`. -/
  | sortAssign (t : Term Sig) (σ : Srt)
  /-- The path equation `t₁ ≈ t₂` says that `t₁` and `t₂` denote the same entity. -/
  | pathEq (t₁ t₂ : Term Sig)
  /-- The relational formula `ρ(x₁, …, xₙ)` says that the values of the variables stand in the
  relation `ρ`. -/
  | rel (ρ : Sig.Rel) (xs : Fin (Sig.arity ρ) → ℕ)
  /-- Negation. -/
  | neg (d : Formula Sig)
  /-- Classical implication. -/
  | imp (d e : Formula Sig)
  /-- The formula `all x d` says that `d` holds when `x` is any component of the described
  entity. -/
  | all (x : ℕ) (d : Formula Sig)


namespace Formula

/-- Conjunction. -/
protected def and (d e : Formula Sig) : Formula Sig := (d.imp e.neg).neg

/-- Disjunction. -/
protected def or (d e : Formula Sig) : Formula Sig := d.neg.imp e

/-- The formula `ex x d` says that `d` holds when `x` is some component of the described
entity. -/
def ex (x : ℕ) (d : Formula Sig) : Formula Sig := (all x d.neg).neg

/-- The biconditional of two formulae. -/
protected def iff (d e : Formula Sig) : Formula Sig := (d.imp e).and (e.imp d)

/-- The formula `∀ x₀ (x₀ ≈ x₀)`, which every entity satisfies, in place of a constant for
truth. -/
def top : Formula Sig := .all 0 (.pathEq (.var 0) (.var 0))

/-- The negation of `top`, which no entity satisfies. -/
def bot : Formula Sig := top.neg

/-- The conjunction of a list of formulae. -/
def conj (ds : List (Formula Sig)) : Formula Sig := ds.foldr Formula.and top

/-- The disjunction of a list of formulae. -/
def disj (ds : List (Formula Sig)) : Formula Sig := ds.foldr Formula.or bot

/-- The variables that occur free in a formula ([richter-2024], Definition 5). -/
def freeVars : Formula Sig → Finset ℕ
  | sortAssign t _ => t.freeVars
  | pathEq t₁ t₂ => t₁.freeVars ∪ t₂.freeVars
  | rel _ xs => Finset.univ.image xs
  | neg d => d.freeVars
  | imp d e => d.freeVars ∪ e.freeVars
  | all x d => d.freeVars.erase x

@[simp] theorem freeVars_and (d e : Formula Sig) :
    (d.and e).freeVars = d.freeVars ∪ e.freeVars := rfl

@[simp] theorem freeVars_or (d e : Formula Sig) : (d.or e).freeVars = d.freeVars ∪ e.freeVars := rfl

@[simp] theorem freeVars_ex (x : ℕ) (d : Formula Sig) :
    (ex x d).freeVars = d.freeVars.erase x := rfl

@[simp] theorem freeVars_iff (d e : Formula Sig) :
    (d.iff e).freeVars = d.freeVars ∪ e.freeVars := by
  simp [Formula.iff, freeVars, Finset.union_comm]

/-- A formula is colon-free when none of its terms starts at the described entity. -/
def IsColonFree : Formula Sig → Prop
  | sortAssign t _ => t.IsColonFree
  | pathEq t₁ t₂ => t₁.IsColonFree ∧ t₂.IsColonFree
  | rel _ _ => True
  | neg d | all _ d => d.IsColonFree
  | imp d e => d.IsColonFree ∧ e.IsColonFree

instance decidableIsColonFree : DecidablePred (IsColonFree (Sig := Sig))
  | sortAssign t _ => Term.decidableIsColonFree t
  | pathEq t₁ t₂ =>
    have := Term.decidableIsColonFree t₁
    have := Term.decidableIsColonFree t₂
    inferInstanceAs (Decidable (t₁.IsColonFree ∧ t₂.IsColonFree))
  | rel .. => isTrue trivial
  | neg d | all _ d => decidableIsColonFree d
  | imp d e =>
    have := decidableIsColonFree d
    have := decidableIsColonFree e
    inferInstanceAs (Decidable (d.IsColonFree ∧ e.IsColonFree))

end Formula

/-! ### Descriptions and grammars -/

/-- A description is a formula with no free variables ([richter-2024], Definition 6). -/
@[ext] structure Description (Sig : Signature Srt) where
  /-- The formula. -/
  toFormula : Formula Sig
  /-- The formula has no free variables. -/
  freeVars_toFormula : toFormula.freeVars = ∅ := by decide

attribute [coe] Description.toFormula
attribute [simp] Description.freeVars_toFormula

instance : Coe (Description Sig) (Formula Sig) := ⟨Description.toFormula⟩

/-- A grammar over a signature is a set of descriptions, its principles
([richter-2024], Definition 16). -/
abbrev Grammar (Sig : Signature Srt) := Set (Description Sig)

/-- The grammar whose principles are the members of a list. -/
def Grammar.ofList (ds : List (Description Sig)) : Grammar Sig := {d | d ∈ ds}

@[simp] theorem Grammar.mem_ofList {ds : List (Description Sig)} {d : Description Sig} :
    d ∈ Grammar.ofList ds ↔ d ∈ ds := Iff.rfl

@[simp] theorem Grammar.ofList_append (ds es : List (Description Sig)) :
    Grammar.ofList (ds ++ es) = Grammar.ofList ds ∪ Grammar.ofList es :=
  Set.ext fun _ ↦ List.mem_append

/-! ### Attribute-value descriptions and constraints on sorts -/

/-- An atom of an attribute-value description says that the path `p` has a value of the sort
`σ`, or that the paths `p` and `q` have the same value. -/
inductive PathAtom (Sig : Signature Srt) where
  /-- The path has a value whose sort is at least as specific as `σ`. -/
  | sort (p : Path Sig) (σ : Srt)
  /-- The two paths have the same value. -/
  | eq (p q : Path Sig)

namespace PathAtom

instance [DecidableEq Srt] [DecidableEq Sig.Attr] : DecidableEq (PathAtom Sig)
  | sort p σ, sort q τ => decidable_of_iff (p = q ∧ σ = τ) (by simp)
  | eq p q, eq p' q' => decidable_of_iff (p = p' ∧ q = q') (by simp)
  | sort .., eq .. => isFalse nofun
  | eq .., sort .. => isFalse nofun

/-- The formula that states an atom. -/
def toFormula : PathAtom Sig → Formula Sig
  | sort p σ => .sortAssign (.path p) σ
  | eq p q => .pathEq (.path p) (.path q)

@[simp] theorem freeVars_toFormula (a : PathAtom Sig) : a.toFormula.freeVars = ∅ := by
  cases a <;> simp [toFormula, Formula.freeVars]

/-- The description that states an atom. -/
@[simps] def toDescription (a : PathAtom Sig) : Description Sig :=
  ⟨a.toFormula, a.freeVars_toFormula⟩

end PathAtom

/-- A constraint `σ ⇒ A` requires every entity whose sort is at least as specific as `σ` to
satisfy each atom of the attribute-value description `A`. -/
structure Constraint (Sig : Signature Srt) where
  /-- The sort that the constraint applies to. -/
  sort : Srt
  /-- The atoms that the entities of that sort satisfy. -/
  atoms : List (PathAtom Sig)

namespace Constraint

instance [DecidableEq Srt] [DecidableEq Sig.Attr] : DecidableEq (Constraint Sig) := fun c c' ↦
  decidable_of_iff (c.sort = c'.sort ∧ c.atoms = c'.atoms) (by cases c; cases c'; simp)

/-- The conjunction of the atoms of a constraint, ending in the equation `: ≈ :`, which every
entity satisfies. -/
def body (c : Constraint Sig) : Formula Sig :=
  c.atoms.foldr (fun a d ↦ a.toFormula.and d) (PathAtom.eq [] []).toFormula

@[simp] theorem freeVars_body (c : Constraint Sig) : c.body.freeVars = ∅ := by
  unfold body
  induction c.atoms with
  | nil => simp
  | cons a as ih => simp [ih]

/-- The formula `: ∼ σ → A` that states the constraint `σ ⇒ A`. -/
def toFormula (c : Constraint Sig) : Formula Sig := (Formula.sortAssign .colon c.sort).imp c.body

@[simp] theorem freeVars_toFormula (c : Constraint Sig) : c.toFormula.freeVars = ∅ := by
  simp [toFormula, Formula.freeVars, Term.freeVars]

/-- The description that states a constraint. -/
@[coe, simps] def toDescription (c : Constraint Sig) : Description Sig :=
  ⟨c.toFormula, c.freeVars_toFormula⟩

instance : Coe (Constraint Sig) (Description Sig) := ⟨toDescription⟩

/-- The constraints among `C` that the sort `σ` inherits, those on `σ` and on its supersorts. -/
def inherited [DecidableLE Srt] (C : List (Constraint Sig)) (σ : Srt) : List (Constraint Sig) :=
  C.filter fun c ↦ σ ≤ c.sort

end Constraint

/-- The grammar whose principles are the constraints of a list. -/
abbrev Grammar.ofConstraints (C : List (Constraint Sig)) : Grammar Sig :=
  .ofList (C.map Constraint.toDescription)

theorem Grammar.ofConstraints_append (C D : List (Constraint Sig)) :
    Grammar.ofConstraints (C ++ D) = Grammar.ofConstraints C ∪ Grammar.ofConstraints D := by
  rw [ofConstraints, List.map_append, ofList_append]

end HPSG.RSRL
