module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.ModelTheory.Semantics

/-!
# Satisfaction: dependence, decidability, and families of structures

This file shows that the value of a term depends only on its variables, and that first-order
satisfaction is decidable on a finite structure with decidable equality and decidable relations,
so that `decide` checks `Realize` facts on concrete finite models. It also realizes terms and
formulas at an index of a family `interp : W → L.Structure M` of structures on one carrier, such
as the world-indexed interpretation of a constant-domain Kripke model, where mathlib's
instance-based `realize` needs the instance chosen at each index.

## Main definitions

- `FirstOrder.Language.BoundedFormula.decidableRealize` decides `BoundedFormula.Realize` by
  recursion on the formula, and `FirstOrder.Language.Formula.decidableRealize` is the same for
  formulas.
- `FirstOrder.Language.Term.realizeAt`, `FirstOrder.Language.Formula.RealizeAt`: realization in
  the structure a family carries at an index.

## Main results

- `FirstOrder.Language.Term.dependsOn_realize`: a term's value depends only on its variables.
-/

@[expose] public section

namespace FirstOrder.Language

open Structure

theorem Term.dependsOn_realize {L : Language} {M : Type*} [L.Structure M] {α : Type*}
    [DecidableEq α] (t : L.Term α) : DependsOn (fun v : α → M ↦ t.realize v) t.varFinset := by
  intro v₁ v₂ h
  induction t with
  | var a => exact h a (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  | func f ts ih =>
    refine congrArg _ (funext fun i ↦ ih i fun a ha ↦ h a ?_)
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)

section DecidableRealize

variable {L : Language} {M : Type*} [L.Structure M] [Fintype M] [DecidableEq M]
  [∀ (n : ℕ) (r : L.Relations n) (x : Fin n → M), Decidable (RelMap r x)] {α : Type*}

/-- Satisfaction on a finite structure with decidable equality and decidable relations is
decidable, by recursion on the formula; `decide` reduces through it on concrete models. -/
instance BoundedFormula.decidableRealize :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => .isFalse id
  | _, .equal _ _, _, _ => inferInstanceAs (Decidable (_ = _))
  | _, .rel R _, _, _ => inferInstanceAs (Decidable (RelMap R _))
  | _, .imp φ ψ, v, xs =>
    haveI := decidableRealize φ v xs
    haveI := decidableRealize ψ v xs
    inferInstanceAs (Decidable (_ → _))
  | _, .all φ, v, xs =>
    haveI : ∀ a, Decidable (φ.Realize v (Fin.snoc xs a)) := fun a ↦
      decidableRealize φ v (Fin.snoc xs a)
    inferInstanceAs (Decidable (∀ a, φ.Realize v (Fin.snoc xs a)))

instance Formula.decidableRealize (φ : L.Formula α) (v : α → M) : Decidable (φ.Realize v) :=
  BoundedFormula.decidableRealize φ v default

end DecidableRealize

/-! ### Realization in a family of structures -/

section RealizeAt

variable {L : Language} {W M α : Type*}

/-- [UPSTREAM] The value of a term in the structure the family carries at `w`. -/
def Term.realizeAt (t : L.Term α) (interp : W → L.Structure M) (w : W) (v : α → M) : M :=
  letI := interp w; t.realize v

/-- [UPSTREAM] Satisfaction in the structure the family carries at `w`. -/
def Formula.RealizeAt (ψ : L.Formula α) (interp : W → L.Structure M) (w : W) (v : α → M) :
    Prop :=
  letI := interp w; ψ.Realize v

variable (interp : W → L.Structure M) (w : W) (v : α → M)

@[simp] theorem Term.realizeAt_var (a : α) : (var a : L.Term α).realizeAt interp w v = v a :=
  rfl

@[simp] theorem Term.realizeAt_constants (c : L.Constants) :
    c.term.realizeAt interp w v = (interp w).funMap c default :=
  letI := interp w; Term.realize_constants

@[simp] theorem Formula.realizeAt_not (ψ : L.Formula α) :
    ψ.not.RealizeAt interp w v ↔ ¬ ψ.RealizeAt interp w v :=
  letI := interp w; Formula.realize_not

@[simp] theorem Formula.realizeAt_inf (ψ₁ ψ₂ : L.Formula α) :
    (ψ₁ ⊓ ψ₂).RealizeAt interp w v ↔ ψ₁.RealizeAt interp w v ∧ ψ₂.RealizeAt interp w v :=
  letI := interp w; Formula.realize_inf

@[simp] theorem Formula.realizeAt_sup (ψ₁ ψ₂ : L.Formula α) :
    (ψ₁ ⊔ ψ₂).RealizeAt interp w v ↔ ψ₁.RealizeAt interp w v ∨ ψ₂.RealizeAt interp w v :=
  letI := interp w; Formula.realize_sup

@[simp] theorem Formula.realizeAt_imp (ψ₁ ψ₂ : L.Formula α) :
    (ψ₁.imp ψ₂).RealizeAt interp w v ↔ (ψ₁.RealizeAt interp w v → ψ₂.RealizeAt interp w v) :=
  letI := interp w; Formula.realize_imp

@[simp] theorem Formula.realizeAt_rel₁ (R : L.Relations 1) (t : L.Term α) :
    (R.formula₁ t).RealizeAt interp w v ↔ (interp w).RelMap R ![t.realizeAt interp w v] :=
  letI := interp w; Formula.realize_rel₁

@[simp] theorem Formula.realizeAt_rel₂ (R : L.Relations 2) (t₁ t₂ : L.Term α) :
    (R.formula₂ t₁ t₂).RealizeAt interp w v ↔
      (interp w).RelMap R ![t₁.realizeAt interp w v, t₂.realizeAt interp w v] :=
  letI := interp w; Formula.realize_rel₂

end RealizeAt

end FirstOrder.Language
