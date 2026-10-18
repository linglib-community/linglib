module

public import Linglib.Syntax.HPSG.Interpretation
public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Function.Basic

/-!
# RSRL descriptions

This file defines the description language of RSRL and its satisfaction relation. A formula
assigns a sort to a term, equates two terms, applies a relation symbol to variables, or combines
formulae with the classical connectives and with quantifiers. The quantifiers range over the
components of the described entity rather than over the whole universe. A grammar is a list of
formulae, its principles, and an interpretation is a model of a grammar when every principle
holds of every entity.

Richter reserves the word description for a formula without free variables, and observes that
the denotation of a description does not depend on the variable assignment. The file proves
that observation. It also proves that a sort assignment is monotone in the sort, which is what
makes a constraint on a sort hold of the entities of every subsort.

## Main definitions

* `HPSG.RSRL.Desc`: a formula of the description language.
* `HPSG.RSRL.Desc.freeVars`: the variables that occur free in a formula.
* `HPSG.RSRL.Interpretation.Satisfies`: an entity satisfies a formula under a variable
  assignment.
* `HPSG.RSRL.Grammar`: a list of principles.
* `HPSG.RSRL.Interpretation.Models`: every entity satisfies every principle of the grammar.
* `HPSG.RSRL.Constraint`: a principle that requires the entities of one sort to satisfy a formula.
* `HPSG.RSRL.Constraint.inherited`: the constraints of a list that a sort inherits.

## Main results

* `HPSG.RSRL.Interpretation.satisfies_congr`: satisfaction depends only on the values that the
  assignment gives to the free variables.
* `HPSG.RSRL.Interpretation.models_iff_forall_assignment`: a model of a grammar of closed
  formulae satisfies them under every assignment.
* `HPSG.RSRL.Interpretation.forall_satisfies_map_toDesc_iff`: an entity satisfies a list of
  constraints exactly when it satisfies the constraints that its sort inherits.

## Implementation notes

A relational formula applies a relation symbol to exactly as many variables as its arity, as in
Richter's syntax. A term is passed to a relation by binding it to a quantified variable first.
`Models` evaluates each principle at the entity `u` under the constant assignment `fun _ ↦ u`, so
that it is decidable on a finite universe. For closed principles the choice of assignment is
immaterial by `models_iff_forall_assignment`.

## References

* [richter-2000]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v

variable {Srt : Type u} [PartialOrder Srt]

/-- A formula of the description language ([richter-2024], Definition 4). -/
inductive Desc (Sig : Signature Srt) where
  /-- The sort assignment `t ∼ σ` says that `t` denotes an entity whose sort is at least as
  specific as `σ`. -/
  | sortAssign (t : Term Sig) (σ : Srt)
  /-- The path equation `t₁ ≈ t₂` says that `t₁` and `t₂` denote the same entity. -/
  | pathEq (t₁ t₂ : Term Sig)
  /-- The relational formula `ρ(x₁, …, xₙ)` says that the values of the variables stand in the
  relation `ρ`. -/
  | rel (ρ : Sig.Rel) (xs : Fin (Sig.arity ρ) → ℕ)
  /-- Negation. -/
  | neg (d : Desc Sig)
  /-- Conjunction. -/
  | and (d e : Desc Sig)
  /-- Disjunction. -/
  | or (d e : Desc Sig)
  /-- Classical implication. -/
  | imp (d e : Desc Sig)
  /-- The formula `ex x d` says that `d` holds when `x` is some component of the described
  entity. -/
  | ex (x : ℕ) (d : Desc Sig)
  /-- The formula `all x d` says that `d` holds when `x` is any component of the described
  entity. -/
  | all (x : ℕ) (d : Desc Sig)

variable {Sig : Signature Srt} {U : Type v}

namespace Desc

/-- The biconditional of two formulae. -/
protected def iff (d e : Desc Sig) : Desc Sig := (d.imp e).and (e.imp d)

/-- The variables that occur free in a formula ([richter-2024], Definition 5). -/
def freeVars : Desc Sig → Finset ℕ
  | sortAssign t _ => t.freeVars
  | pathEq t₁ t₂ => t₁.freeVars ∪ t₂.freeVars
  | rel _ xs => Finset.univ.image xs
  | neg d => d.freeVars
  | and d e | or d e | imp d e => d.freeVars ∪ e.freeVars
  | ex x d | all x d => d.freeVars.erase x

@[simp] theorem freeVars_iff (d e : Desc Sig) : (d.iff e).freeVars = d.freeVars ∪ e.freeVars := by
  simp [Desc.iff, freeVars, Finset.union_comm]

end Desc

namespace Interpretation

variable (I : Interpretation Sig U)

/-! ### Satisfaction -/

/-- The entity `u` satisfies a formula under the assignment `g`
([richter-2024], Definition 14). An atomic formula with an undefined term is false. -/
def Satisfies (g : ℕ → U) (u : U) : Desc Sig → Prop
  | .sortAssign t σ => ∃ v ∈ I.termDenot g t u, I.S v ≤ σ
  | .pathEq t₁ t₂ => ∃ v ∈ I.termDenot g t₁ u, v ∈ I.termDenot g t₂ u
  | .rel ρ xs => I.R ρ fun i ↦ g (xs i)
  | .neg d => ¬ Satisfies g u d
  | .and d e => Satisfies g u d ∧ Satisfies g u e
  | .or d e => Satisfies g u d ∨ Satisfies g u e
  | .imp d e => Satisfies g u d → Satisfies g u e
  | .ex x d => ∃ w, I.IsComponentOf u w ∧ Satisfies (Function.update g x w) u d
  | .all x d => ∀ w, I.IsComponentOf u w → Satisfies (Function.update g x w) u d

instance decidableSatisfies [Fintype U] [DecidableEq U] [DecidableLE Srt] [Fintype Sig.Attr]
    [∀ ρ, DecidablePred (I.R ρ)] (g : ℕ → U) (u : U) :
    (d : Desc Sig) → Decidable (I.Satisfies g u d)
  | .sortAssign _ σ => Option.decidableExistsMem (p := (I.S · ≤ σ)) _
  | .pathEq _ t₂ => Option.decidableExistsMem (p := (· ∈ I.termDenot g t₂ u)) _
  | .rel .. => by unfold Satisfies; infer_instance
  | .neg d => by
    have := decidableSatisfies g u d
    unfold Satisfies; infer_instance
  | .and d e | .or d e | .imp d e => by
    have := decidableSatisfies g u d
    have := decidableSatisfies g u e
    unfold Satisfies; infer_instance
  | .ex x d | .all x d => by
    have (w : U) := decidableSatisfies (Function.update g x w) u d
    unfold Satisfies; infer_instance

variable {I} {g g' : ℕ → U} {u : U} {d e : Desc Sig}

@[simp] theorem satisfies_sortAssign {t : Term Sig} {σ : Srt} :
    I.Satisfies g u (.sortAssign t σ) ↔ ∃ v ∈ I.termDenot g t u, I.S v ≤ σ := Iff.rfl

@[simp] theorem satisfies_pathEq {t₁ t₂ : Term Sig} :
    I.Satisfies g u (.pathEq t₁ t₂) ↔ ∃ v ∈ I.termDenot g t₁ u, v ∈ I.termDenot g t₂ u :=
  Iff.rfl

@[simp] theorem satisfies_rel {ρ : Sig.Rel} {xs : Fin (Sig.arity ρ) → ℕ} :
    I.Satisfies g u (.rel ρ xs) ↔ I.R ρ fun i ↦ g (xs i) := Iff.rfl

@[simp] theorem satisfies_neg : I.Satisfies g u d.neg ↔ ¬ I.Satisfies g u d := Iff.rfl

@[simp] theorem satisfies_and :
    I.Satisfies g u (d.and e) ↔ I.Satisfies g u d ∧ I.Satisfies g u e := Iff.rfl

@[simp] theorem satisfies_or :
    I.Satisfies g u (d.or e) ↔ I.Satisfies g u d ∨ I.Satisfies g u e := Iff.rfl

@[simp] theorem satisfies_imp :
    I.Satisfies g u (d.imp e) ↔ I.Satisfies g u d → I.Satisfies g u e := Iff.rfl

@[simp] theorem satisfies_iff :
    I.Satisfies g u (d.iff e) ↔ (I.Satisfies g u d ↔ I.Satisfies g u e) := iff_def.symm

@[simp] theorem satisfies_ex {x : ℕ} : I.Satisfies g u (.ex x d) ↔
    ∃ w, I.IsComponentOf u w ∧ I.Satisfies (Function.update g x w) u d := Iff.rfl

@[simp] theorem satisfies_all {x : ℕ} : I.Satisfies g u (.all x d) ↔
    ∀ w, I.IsComponentOf u w → I.Satisfies (Function.update g x w) u d := Iff.rfl

/-- A sort assignment is monotone in the sort. -/
theorem Satisfies.sortAssign_mono {t : Term Sig} {σ τ : Srt} (hστ : σ ≤ τ)
    (h : I.Satisfies g u (.sortAssign t σ)) : I.Satisfies g u (.sortAssign t τ) :=
  let ⟨v, hv, hσ⟩ := h; ⟨v, hv, hσ.trans hστ⟩

/-! ### Free variables -/

private theorem update_congr {x : ℕ} {s : Finset ℕ} (h : ∀ y ∈ s.erase x, g y = g' y) (w : U) :
    ∀ y ∈ s, Function.update g x w y = Function.update g' x w y := fun y hy ↦ by
  obtain rfl | hyx := eq_or_ne y x
  · simp
  · simpa [Function.update_of_ne hyx] using h y (Finset.mem_erase.2 ⟨hyx, hy⟩)

/-- Satisfaction depends only on the values of the free variables. -/
theorem satisfies_congr : ∀ {g g' : ℕ → U},
    (∀ x ∈ d.freeVars, g x = g' x) → (I.Satisfies g u d ↔ I.Satisfies g' u d) := by
  induction d with
  | sortAssign t σ => intro g g' h; rw [satisfies_sortAssign, termDenot_congr h]; rfl
  | pathEq t₁ t₂ =>
    intro g g' h
    rw [satisfies_pathEq, termDenot_congr fun x hx ↦ h x (Finset.mem_union_left _ hx),
      termDenot_congr fun x hx ↦ h x (Finset.mem_union_right _ hx)]
    rfl
  | rel ρ xs =>
    intro g g' h
    have : (fun i ↦ g (xs i)) = fun i ↦ g' (xs i) :=
      funext fun i ↦ h _ (Finset.mem_image_of_mem xs (Finset.mem_univ i))
    rw [satisfies_rel, this]; rfl
  | neg d ih => exact fun h ↦ not_congr (ih h)
  | and d e ihd ihe =>
    exact fun h ↦ and_congr (ihd fun x hx ↦ h x (Finset.mem_union_left _ hx))
      (ihe fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | or d e ihd ihe =>
    exact fun h ↦ or_congr (ihd fun x hx ↦ h x (Finset.mem_union_left _ hx))
      (ihe fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | imp d e ihd ihe =>
    exact fun h ↦ imp_congr (ihd fun x hx ↦ h x (Finset.mem_union_left _ hx))
      (ihe fun x hx ↦ h x (Finset.mem_union_right _ hx))
  | ex x d ih =>
    exact fun h ↦ exists_congr fun w ↦ and_congr_right fun _ ↦ ih (update_congr h w)
  | all x d ih =>
    exact fun h ↦ forall_congr' fun w ↦ imp_congr_right fun _ ↦ ih (update_congr h w)

/-- The satisfaction of a closed formula does not depend on the assignment. -/
theorem satisfies_iff_of_freeVars_eq_empty (hd : d.freeVars = ∅) (g g' : ℕ → U) :
    I.Satisfies g u d ↔ I.Satisfies g' u d :=
  satisfies_congr fun x hx ↦ by simp [hd] at hx

end Interpretation

/-! ### Grammars and models -/

/-- A grammar over a signature is a list of formulae, its principles
([richter-2024], Definition 16). -/
abbrev Grammar (Sig : Signature Srt) := List (Desc Sig)

namespace Interpretation

variable (I : Interpretation Sig U) {G H : Grammar Sig} {u : U}

/-- An interpretation is a model of a grammar when every entity satisfies every principle
([richter-2024], Definition 18). -/
def Models (G : Grammar Sig) : Prop := ∀ u : U, ∀ d ∈ G, I.Satisfies (fun _ ↦ u) u d

instance [Fintype U] [DecidableEq U] [DecidableLE Srt] [Fintype Sig.Attr]
    [∀ ρ, DecidablePred (I.R ρ)] (G : Grammar Sig) : Decidable (I.Models G) := by
  unfold Models; infer_instance

variable {I}

/-- A model of a grammar of closed formulae satisfies them under every assignment. -/
theorem models_iff_forall_assignment (hG : ∀ d ∈ G, d.freeVars = ∅) :
    I.Models G ↔ ∀ (g : ℕ → U) (u : U), ∀ d ∈ G, I.Satisfies g u d :=
  ⟨fun h g u d hd ↦ (satisfies_iff_of_freeVars_eq_empty (hG d hd) _ g).1 (h u d hd),
    fun h u ↦ h _ u⟩

@[simp] theorem models_nil : I.Models [] := fun _ _ h ↦ absurd h List.not_mem_nil

@[simp] theorem models_append : I.Models (G ++ H) ↔ I.Models G ∧ I.Models H := by
  simp only [Models, List.mem_append, or_imp, forall_and]

/-- A model of a grammar is a model of any part of it. -/
theorem Models.mono (hI : I.Models H) (hGH : G ⊆ H) : I.Models G :=
  fun u d hd ↦ hI u d (hGH hd)

end Interpretation

/-! ### Constraints on sorts -/

/-- A constraint `σ ⇒ d` requires every entity whose sort is at least as specific as `σ` to
satisfy the formula `d`. -/
structure Constraint (Sig : Signature Srt) where
  /-- The sort that the constraint applies to. -/
  sort : Srt
  /-- The formula that the entities of that sort satisfy. -/
  body : Desc Sig

namespace Constraint

/-- The formula that states a constraint. -/
def toDesc (c : Constraint Sig) : Desc Sig := (Desc.sortAssign .colon c.sort).imp c.body

instance : Coe (Constraint Sig) (Desc Sig) := ⟨toDesc⟩

@[simp] theorem freeVars_toDesc (c : Constraint Sig) : c.toDesc.freeVars = c.body.freeVars := by
  simp [toDesc, Desc.freeVars, Term.freeVars]

/-- The constraints among `C` that the sort `σ` inherits, those on `σ` and on its supersorts. -/
def inherited [DecidableLE Srt] (C : List (Constraint Sig)) (σ : Srt) : List (Constraint Sig) :=
  C.filter fun c ↦ σ ≤ c.sort

end Constraint

namespace Interpretation

variable {I : Interpretation Sig U} {C : List (Constraint Sig)} {g : ℕ → U} {u : U}

@[simp] theorem satisfies_toDesc {c : Constraint Sig} :
    I.Satisfies g u c.toDesc ↔ I.S u ≤ c.sort → I.Satisfies g u c.body := by
  simp [Constraint.toDesc]

/-- An entity satisfies the formulae that state a list of constraints exactly when it satisfies
the bodies of the constraints that its sort inherits. An entity below several constrained sorts
therefore satisfies the constraints on all of them. -/
theorem forall_satisfies_map_toDesc_iff [DecidableLE Srt] :
    (∀ d ∈ C.map Constraint.toDesc, I.Satisfies g u d) ↔
      ∀ c ∈ Constraint.inherited C (I.S u), I.Satisfies g u c.body := by
  simp [Constraint.inherited]

/-- An interpretation is a model of a list of constraints exactly when every entity satisfies
the constraints that its sort inherits. -/
theorem models_map_toDesc_iff [DecidableLE Srt] : I.Models (C.map Constraint.toDesc) ↔
    ∀ u, ∀ c ∈ Constraint.inherited C (I.S u), I.Satisfies (fun _ ↦ u) u c.body :=
  forall_congr' fun _ ↦ forall_satisfies_map_toDesc_iff

/-- In a model, a constraint among the principles holds of every entity whose sort is at least
as specific as the constrained sort. -/
theorem Models.satisfies_body {G : Grammar Sig} (hI : I.Models G) {c : Constraint Sig}
    (hc : c.toDesc ∈ G) (hu : I.S u ≤ c.sort) : I.Satisfies (fun _ ↦ u) u c.body :=
  satisfies_toDesc.1 (hI u _ hc) hu

end Interpretation

end HPSG.RSRL
