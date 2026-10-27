module

public import Mathlib.ModelTheory.Basic

/-!
# The monadic language on a type of predicate symbols

This file defines the monadic first-order language on a type `ι` of predicate symbols, the
relational counterpart of `Language.constantsOn`: one unary relation symbol `pred i` for each
`i : ι` and no other symbols. A language is monadic when its only symbols are unary relation
symbols, and a family of predicates on `M` is a structure for the monadic language.

## Main definitions

* `FirstOrder.Language.IsMonadic`: the language has only unary relation symbols.
* `FirstOrder.Language.monadic ι`: the monadic language on `ι`.
* `FirstOrder.Language.monadic.structure P`: the structure interpreting `pred i` as `P i`.
* `FirstOrder.Language.monadic.structureEquiv`: a bijection carrying each `P i` to `Q i` is an
  isomorphism of the structures.

## Implementation notes

The relation symbols form an inductive family, as mathlib's `orderRel` and `graphRel` do, and the
structure is named after mathlib's `constantsOn.structure`. The monadic signature with individual
constants is `(monadic Pred)[[Const]]`, mathlib's `Language.withConstants`: its structures are
`withConstantsStructure` over `monadic.structure` and `constantsOn.structure`, the constant symbol
of `c` is `(monadic Pred).con c`, and the relation symbol of `P` is `Sum.inl (.pred P)`.
-/

@[expose] public section

universe u v w w'

namespace FirstOrder.Language

open Structure

/-- A language is monadic when its only symbols are unary relation symbols. -/
class IsMonadic (L : Language.{u, v}) : Prop where
  isEmpty_functions : ∀ n, IsEmpty (L.Functions n)
  isEmpty_relations : ∀ n, n ≠ 1 → IsEmpty (L.Relations n)

instance (priority := 100) IsMonadic.isRelational (L : Language.{u, v}) [L.IsMonadic] :
    L.IsRelational :=
  IsMonadic.isEmpty_functions

/-- The relation symbols of the monadic language on `ι`, one unary symbol for each `i : ι`. -/
inductive monadicRel (ι : Type v) : ℕ → Type v
  | pred (i : ι) : monadicRel ι 1

/-- The monadic language with one unary relation symbol for each `i : ι` and no other symbols. -/
protected def monadic (ι : Type v) : Language.{0, v} := ⟨fun _ => Empty, monadicRel ι⟩

variable {ι : Type v}

instance : (Language.monadic ι).IsMonadic where
  isEmpty_functions _ := inferInstanceAs (IsEmpty Empty)
  isEmpty_relations _ hl := ⟨fun r => by cases r; exact hl rfl⟩

variable {M : Type w} {N : Type w'}

/-- The structure on `M` interpreting each symbol `pred i` as the predicate `P i`. -/
@[instance_reducible]
def monadic.structure (P : ι → M → Prop) : (Language.monadic ι).Structure M where
  RelMap | .pred i => fun x => P i (x 0)

variable {P : ι → M → Prop} {Q : ι → N → Prop}

@[simp] theorem relMap_monadic_structure (i : ι) (x : Fin 1 → M) :
    @RelMap _ M (monadic.structure P) 1 (.pred i) x ↔ P i (x 0) := Iff.rfl

instance monadic.structure.decidableRelMap [∀ i a, Decidable (P i a)] :
    ∀ {n : ℕ} (r : (Language.monadic ι).Relations n) (x : Fin n → M),
      Decidable (@RelMap _ _ (monadic.structure P) n r x)
  | _, .pred i, x => inferInstanceAs (Decidable (P i (x 0)))

/-- A bijection carrying each predicate `P i` to `Q i` is an isomorphism of the monadic
structures. -/
def monadic.structureEquiv (e : M ≃ N) (h : ∀ i x, Q i (e x) ↔ P i x) :
    @Language.Equiv (Language.monadic ι) M N (monadic.structure P) (monadic.structure Q) :=
  @Language.Equiv.mk _ M N (monadic.structure P) (monadic.structure Q) e
    (fun f => isEmptyElim f) (fun | .pred i => fun x => h i (x 0))

end FirstOrder.Language
