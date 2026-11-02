module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.ModelTheory.Basic

/-!
# The monadic language on a type of predicate symbols

This file defines the monadic first-order language on a type `ι` of predicate symbols, the
relational counterpart of `Language.constantsOn`: one unary relation symbol `pred i` for each
`i : ι` and no other symbols. A language is monadic when its only symbols are unary relation
symbols, and a family of predicates on `M` is a structure for the monadic language. Each element
has a unary type, the set of symbols holding of it, and two monadic structures are
[isomorphic exactly when](##FirstOrder.Language.nonempty_equiv_iff_mk_eq) each unary type has
equally many elements in both.

## Implementation notes

The relation symbols form an inductive family, as mathlib's `orderRel` and `graphRel` do, and the
structure is named after mathlib's `constantsOn.structure`. The monadic signature with individual
constants is `(monadic Pred)[[Const]]`, mathlib's `Language.withConstants`: its structures are
`withConstantsStructure` over `monadic.structure` and `constantsOn.structure`, the constant symbol
of `c` is `(monadic Pred).con c`, and the relation symbol of `P` is `Sum.inl (.pred P)`.

## References

* [lindstrom-1966]
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

/-- Every structure for the monadic language interprets each symbol as some predicate. -/
theorem monadic.eq_structure (S : (Language.monadic ι).Structure M) :
    S = monadic.structure fun i a => S.RelMap (.pred i) ![a] := by
  ext n R x
  · exact isEmptyElim R
  · obtain ⟨i⟩ := R
    exact iff_of_eq (congrArg _ (funext fun j => by rw [Subsingleton.elim j 0]; rfl))

/-! ### Unary types -/

section UnaryType

/-- The unary type of `a` is the set of unary relation symbols that hold of it. -/
def unaryType (L : Language.{u, v}) {M : Type w} [L.Structure M] (a : M) :
    L.Relations 1 → Prop := fun R => RelMap R ![a]

theorem unaryType_monadic_structure_eq_iff {P : ι → M → Prop} (a : M)
    (S : (Language.monadic ι).Relations 1 → Prop) :
    @unaryType _ M (monadic.structure P) a = S ↔ ∀ i, P i a ↔ S (.pred i) :=
  ⟨fun h i => Iff.of_eq (congrFun h (.pred i)),
    fun h => funext fun | .pred i => propext (h i)⟩

variable {L : Language.{u, v}}

private theorem comp_vec_one (f : M → N) (a : M) : f ∘ ![a] = ![f a] :=
  funext fun i => by rw [Subsingleton.elim i 0]; rfl

theorem Equiv.unaryType_apply [L.Structure M] [L.Structure N] (e : M ≃[L] N) (a : M) :
    L.unaryType (e a) = L.unaryType a :=
  funext fun R => propext <| by
    rw [unaryType, unaryType, ← comp_vec_one]
    exact StrongHomClass.map_rel e R ![a]

open Cardinal in
/-- Two structures for a monadic language are isomorphic exactly when each unary type has equally
many elements in both, so that a structure of type `⟨1, 1⟩` is "characterized up to isomorphism" by
the sizes of the four regions of its two predicates ([lindstrom-1966] §3). -/
theorem nonempty_equiv_iff_mk_eq [L.IsMonadic] {M N : Type w} [L.Structure M] [L.Structure N] :
    Nonempty (M ≃[L] N) ↔
      ∀ S, #(L.unaryType ⁻¹' {S} : Set M) = #(L.unaryType ⁻¹' {S} : Set N) := by
  refine ⟨fun ⟨e⟩ S => mk_congr (e.toEquiv.subtypeEquiv fun a => ?_), fun h => ?_⟩
  · exact (congrArg (· = S) (e.unaryType_apply a)).to_iff.symm
  · let e : M ≃ N := _root_.Equiv.ofFiberEquiv fun S => (Cardinal.eq.1 (h S)).some
    have he (a : M) : L.unaryType (e a) = L.unaryType a := _root_.Equiv.ofFiberEquiv_map _ a
    refine ⟨⟨e, fun f => isEmptyElim f, fun {n} R x => ?_⟩⟩
    obtain rfl : n = 1 := by_contra fun hn => (IsMonadic.isEmpty_relations n hn).elim R
    obtain ⟨a, rfl⟩ : ∃ a, x = ![a] := ⟨x 0, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
    rw [show e.toFun ∘ ![a] = ![e a] from comp_vec_one e a]
    exact Iff.of_eq (congrFun (he a) R)

end UnaryType

end FirstOrder.Language
