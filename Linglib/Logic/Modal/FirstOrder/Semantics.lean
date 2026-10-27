module

public import Linglib.Core.ModelTheory.Semantics
public import Linglib.Logic.Modal.FirstOrder.Syntax

/-!
# Constant-domain Kripke semantics

A Kripke model for quantified modal logic has a set of worlds, an accessibility relation between
them, and at each world a first-order structure. In a *constant-domain* model every world has
the same domain of individuals, and only the interpretation of the symbols varies from world to
world. A formula is satisfied at a world under an assignment of individuals to its free
variables: atomic formulas are evaluated in the world's structure, necessity quantifies over the
accessible worlds, and the quantifiers range over the common domain. Because the domain does not
vary, the [Barcan formula](##realize_barcan) $\forall x \, \Box \varphi \to \Box \forall x \,
\varphi$ and [its converse](##realize_converseBarcan) hold in every model.

## Main definitions

* `FirstOrder.Language.ModalStructure`: a constant-domain Kripke model.
* `FirstOrder.Language.ModalFormula.Realize`: satisfaction of a modal formula at a world.

## Implementation notes

* `[UPSTREAM]` candidate for mathlib's `ModelTheory`, whose semantics has one structure and no
  accessibility relation.
* Accessibility is `Finset`-valued, for computation, as the team-semantics consumers require; it
  can be generalized to a `Prop`-valued relation when a consumer needs infinite branching.
* Quantifiers bind named variables and update the assignment with `Function.update`, as
  `Formula.all₁` and `Formula.ex₁` of `Core/ModelTheory/Binders.lean` do, rather than de Bruijn
  indices, since the consumers carry named variables.

## References

* [fitting-mendelsohn-2023] — constant-domain models, world-relative interpretation, the Barcan
  formulas
-/

@[expose] public section

namespace FirstOrder.Language

variable {L : Language} {W M α : Type*}

/-- A constant-domain Kripke model: an accessibility relation on the worlds `W` and, at each
world, an `L`-structure on the domain `M`. -/
structure ModalStructure (L : Language) (W M : Type*) where
  /-- The worlds accessible from each world. -/
  access : W → Finset W
  /-- The structure at each world. -/
  interp : W → L.Structure M

namespace ModalStructure

/-! ### World-relative interpretation

The interpretation function `I(w)(·)` of first-order modal semantics
([fitting-mendelsohn-2023] Definition 8.6.2): what a symbol denotes at a
world, read off the world's structure. -/

variable (K : ModalStructure L W M)

/-- The relation a relation symbol denotes at a world. -/
def relInterp {n : ℕ} (R : L.Relations n) (w : W) : (Fin n → M) → Prop :=
  (K.interp w).RelMap R

/-- The function a function symbol denotes at a world. -/
def funInterp {n : ℕ} (f : L.Functions n) (w : W) : (Fin n → M) → M :=
  (K.interp w).funMap f

/-- The relation a unary relation symbol denotes at a world, curried. -/
def relInterp₁ (R : L.Relations 1) (w : W) (d : M) : Prop :=
  K.relInterp R w (fun _ ↦ d)

/-- The element a constant denotes at a world. -/
def constInterp (c : L.Constants) (w : W) : M :=
  K.funInterp c w default

variable {α : Type*} (w : W) (v : α → M)

theorem realizeAt_constants (c : L.Constants) :
    c.term.realizeAt K.interp w v = K.constInterp c w :=
  Term.realizeAt_constants ..

theorem realizeAt_rel₁ (R : L.Relations 1) (t : L.Term α) :
    (R.formula₁ t).RealizeAt K.interp w v ↔ K.relInterp₁ R w (t.realizeAt K.interp w v) := by
  rw [Formula.realizeAt_rel₁, Matrix.cons_fin_one]
  rfl

end ModalStructure

namespace ModalFormula

variable [DecidableEq α]

/-- Satisfaction of a modal formula at a world under an assignment, $K, w \vDash_v \varphi$. -/
def Realize (K : ModalStructure L W M) :
    W → ModalFormula L α → (α → M) → Prop
  | w, .equal t₁ t₂, v => t₁.realizeAt K.interp w v = t₂.realizeAt K.interp w v
  | w, .rel R ts, v => K.relInterp R w fun i ↦ (ts i).realizeAt K.interp w v
  | _, .falsum, _ => False
  | w, .imp φ ψ, v => Realize K w φ v → Realize K w ψ v
  | w, .box φ, v => ∀ w' ∈ K.access w, Realize K w' φ v
  | w, .all x φ, v => ∀ d : M, Realize K w φ (Function.update v x d)

variable (K : ModalStructure L W M) (w : W) (v : α → M)

@[simp] theorem realize_equal (t₁ t₂ : L.Term α) :
    (equal t₁ t₂).Realize K w v ↔ t₁.realizeAt K.interp w v = t₂.realizeAt K.interp w v :=
  Iff.rfl

@[simp] theorem realize_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) :
    (rel R ts).Realize K w v ↔ K.relInterp R w fun i ↦ (ts i).realizeAt K.interp w v :=
  Iff.rfl

@[simp] theorem realize_bot :
    (⊥ : ModalFormula L α).Realize K w v ↔ False :=
  Iff.rfl

@[simp] theorem realize_imp (φ ψ : ModalFormula L α) :
    (imp φ ψ).Realize K w v ↔ (φ.Realize K w v → ψ.Realize K w v) :=
  Iff.rfl

@[simp] theorem realize_not (φ : ModalFormula L α) :
    (ModalFormula.not φ).Realize K w v ↔ ¬ φ.Realize K w v :=
  Iff.rfl

@[simp] theorem realize_top :
    (⊤ : ModalFormula L α).Realize K w v ↔ True := by
  simp [Top.top]

@[simp] theorem realize_inf (φ ψ : ModalFormula L α) :
    (φ ⊓ ψ).Realize K w v ↔ φ.Realize K w v ∧ ψ.Realize K w v := by
  simp [Min.min]

@[simp] theorem realize_sup (φ ψ : ModalFormula L α) :
    (φ ⊔ ψ).Realize K w v ↔ φ.Realize K w v ∨ ψ.Realize K w v := by
  simp [Max.max, imp_iff_not_or]

@[simp] theorem realize_box (φ : ModalFormula L α) :
    (box φ).Realize K w v ↔ ∀ w' ∈ K.access w, φ.Realize K w' v :=
  Iff.rfl

@[simp] theorem realize_all (x : α) (φ : ModalFormula L α) :
    (all x φ).Realize K w v ↔
      ∀ d : M, φ.Realize K w (Function.update v x d) :=
  Iff.rfl

@[simp] theorem realize_ex (x : α) (φ : ModalFormula L α) :
    (ModalFormula.ex x φ).Realize K w v ↔
      ∃ d : M, φ.Realize K w (Function.update v x d) := by
  simp [ModalFormula.ex, not_forall]

@[simp] theorem realize_diamond (φ : ModalFormula L α) :
    (diamond φ).Realize K w v ↔ ∃ w' ∈ K.access w, φ.Realize K w' v := by
  simp [diamond, not_forall]

@[simp] theorem realize_rel₁ (R : L.Relations 1) (t : L.Term α) :
    ((R.modalFormula₁ t).Realize K w v) ↔
      K.relInterp₁ R w (t.realizeAt K.interp w v) := by
  rw [Relations.modalFormula₁, ModalFormula.realize_rel]
  exact iff_of_eq (congrArg _
    (funext fun i ↦ by rw [Subsingleton.elim i 0, Matrix.cons_val_zero]))

/-! ### The Barcan laws

In a constant-domain model necessity and universal quantification commute. -/

theorem realize_barcan (x : α) (φ : ModalFormula L α) :
    (all x (box φ)).Realize K w v → (box (all x φ)).Realize K w v :=
  fun h w' hw' d ↦ h d w' hw'

theorem realize_converseBarcan (x : α) (φ : ModalFormula L α) :
    (box (all x φ)).Realize K w v → (all x (box φ)).Realize K w v :=
  fun h d w' hw' ↦ h w' hw' d

end ModalFormula

end FirstOrder.Language
