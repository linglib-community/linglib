module

public import Linglib.Core.ModelTheory.Semantics

/-!
# Named-variable binders for first-order formulas

Mathlib's quantifiers on `BoundedFormula` bind de Bruijn indices, and its closures of named free
variables, `Formula.iAlls` and `Formula.iExs`, are noncomputable. This file closes a single named
free variable computably, with realization through `Function.update`; the definitions are
upstream candidates.

## Main definitions

* `FirstOrder.Language.Formula.all₁`, `FirstOrder.Language.Formula.ex₁`: the universal and
  existential closures of one named free variable.
* `FirstOrder.Language.Formula.toSentence`: a formula with no free variables, as a sentence.

## Main results

* `FirstOrder.Language.Formula.realize_all₁`, `FirstOrder.Language.Formula.realize_ex₁`: a
  closure is realized when its body is at every, or some, update of the valuation; `realizeAt_all₁`
  and `realizeAt_ex₁` are the same at an index of a family of structures.
-/

@[expose] public section

universe u v

namespace FirstOrder.Language.Formula

open FirstOrder Language

variable {L : Language.{u, v}} {α : Type*} [DecidableEq α]

/-- Universally close the named free variable `n`: relabel it to the bound variable and
quantify. Computable, unlike mathlib's `Formula.iAlls`. -/
def all₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).all

/-- Existentially close the named free variable `n`. Computable, unlike mathlib's
`Formula.iExs`. -/
def ex₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).ex

section Realize

variable {M : Type*} [L.Structure M]

theorem realize_relabel_update (n : α) (φ : L.Formula α) (v : α → M) (x : M) :
    (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).Realize v
      (Fin.snoc (default : Fin 0 → M) x) ↔ φ.Realize (Function.update v n x) := by
  rw [BoundedFormula.realize_relabel, Function.comp_update]
  refine iff_of_eq (congrArg₂ (BoundedFormula.Realize φ) ?_ (funext fun i ↦ i.elim0))
  simp [Fin.snoc, Function.comp_def]

@[simp]
theorem realize_all₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (all₁ n φ).Realize v ↔ ∀ x : M, φ.Realize (Function.update v n x) :=
  BoundedFormula.realize_all.trans <| forall_congr' <| realize_relabel_update n φ v

@[simp]
theorem realize_ex₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (ex₁ n φ).Realize v ↔ ∃ x : M, φ.Realize (Function.update v n x) :=
  BoundedFormula.realize_ex.trans <| exists_congr <| realize_relabel_update n φ v

/-- A formula with no occurring free variables, as a sentence. -/
def toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅) : L.Sentence :=
  φ.restrictFreeVar fun x ↦ absurd x.2 (by simp [h])

theorem realize_toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅)
    (v : α → M) :
    (M ⊨ φ.toSentence h) ↔ φ.Realize v :=
  BoundedFormula.realize_restrictFreeVar v (fun a ↦ absurd a.2 (by simp [h]))

end Realize

section RealizeAt

variable {W M : Type*} (interp : W → L.Structure M) (w : W) (v : α → M)

@[simp] theorem realizeAt_all₁ (n : α) (φ : L.Formula α) :
    (all₁ n φ).RealizeAt interp w v ↔ ∀ x : M, φ.RealizeAt interp w (Function.update v n x) :=
  letI := interp w; realize_all₁

@[simp] theorem realizeAt_ex₁ (n : α) (φ : L.Formula α) :
    (ex₁ n φ).RealizeAt interp w v ↔ ∃ x : M, φ.RealizeAt interp w (Function.update v n x) :=
  letI := interp w; realize_ex₁

end RealizeAt

end FirstOrder.Language.Formula
