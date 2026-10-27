module

public import Mathlib.ModelTheory.Syntax

/-!
# The quantified modal language

Quantified modal logic adds a necessity operator to first-order logic. Its formulas over a
signature `L`, with free variables in `α`, are built as mathlib's first-order formulas are, from
equations between terms, relation symbols applied to terms, falsity and implication, together
with necessity and universal quantification over a named variable. Negation, the other
connectives, existential quantification and possibility are defined from these exactly as for
first-order formulas.

## Main definitions

* `FirstOrder.Language.ModalFormula L α`: the formulas of quantified modal logic.

## Implementation notes

`[UPSTREAM]` candidate for mathlib's `ModelTheory`.

## References

* [fitting-mendelsohn-2023]
-/

@[expose] public section

namespace FirstOrder.Language

variable {L : Language} {α : Type*}

/-- A formula of quantified modal logic over `L` with free variables in `α`. -/
inductive ModalFormula (L : Language) (α : Type*) where
  /-- The proposition that two terms are equal. -/
  | equal (t₁ t₂ : L.Term α) : ModalFormula L α
  /-- A relation symbol applied to terms. -/
  | rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term α) : ModalFormula L α
  /-- The contradiction. -/
  | falsum : ModalFormula L α
  /-- Implication. -/
  | imp (φ ψ : ModalFormula L α) : ModalFormula L α
  /-- Necessity. -/
  | box (φ : ModalFormula L α) : ModalFormula L α
  /-- Universal quantification of a named variable. -/
  | all (x : α) (φ : ModalFormula L α) : ModalFormula L α

namespace ModalFormula

instance : Inhabited (ModalFormula L α) := ⟨falsum⟩

instance : Bot (ModalFormula L α) := ⟨falsum⟩

/-- The negation of a modal formula. -/
@[match_pattern]
protected def not (φ : ModalFormula L α) : ModalFormula L α := φ.imp ⊥

instance : Top (ModalFormula L α) := ⟨ModalFormula.not ⊥⟩

instance : Min (ModalFormula L α) := ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (ModalFormula L α) := ⟨fun φ ψ => φ.not.imp ψ⟩

/-- Existential quantification of a named variable, defined as $\neg \forall x \neg$. -/
@[match_pattern]
protected def ex (x : α) (φ : ModalFormula L α) : ModalFormula L α :=
  (all x φ.not).not

/-- Possibility, defined as $\neg \Box \neg$. -/
@[match_pattern]
def diamond (φ : ModalFormula L α) : ModalFormula L α := (box φ.not).not

end ModalFormula

/-- Applies a relation symbol to terms as a modal formula. -/
abbrev Relations.modalFormula {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term α) : ModalFormula L α :=
  ModalFormula.rel R ts

/-- Applies a unary relation symbol to a term as a modal formula. -/
abbrev Relations.modalFormula₁ (R : L.Relations 1) (t : L.Term α) :
    ModalFormula L α :=
  ModalFormula.rel R ![t]

end FirstOrder.Language
