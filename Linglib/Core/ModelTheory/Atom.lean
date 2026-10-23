module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Order.Concept

/-!
# Atoms over variables

An atom `R(x₁, …, xₙ)` applies a relation symbol to variables, and an assignment realizes a set
of atoms when it makes each of them true. A set of atoms presents a structure on its variables,
its canonical structure, in which a relation holds of exactly the tuples its atoms list. The
assignments realizing a set of atoms in a structure are the homomorphisms out of its canonical
structure, so one set of atoms entails another along a map of variables in every structure
exactly when the map carries the atoms of the second into the first. This is Chandra and Merlin's
theorem on the containment of conjunctive queries.

## Main definitions

* `FirstOrder.Language.Atom`: atoms, renamed by `Atom.map`, permuted by `Equiv.Perm`, and read as
  atomic formulas by `Atom.toFormula`.
* `FirstOrder.Language.Atom.realizers`: the assignments realizing a set of atoms.
* `FirstOrder.Language.Atom.Canonical`: the structure a set of atoms presents on its variables.

## Main statements

* `FirstOrder.Language.Atom.Canonical.homEquiv`: the homomorphisms out of the canonical structure
  are the realizing assignments.
* `FirstOrder.Language.Atom.forall_realizers_subset_preimage_iff`: entailment along a map in every
  structure is inclusion of the renamed atoms.

## References

* [chandra-merlin-1977]
-/

@[expose] public section

universe u v w x y

namespace FirstOrder.Language

open Structure Pointwise

/-- An atom `R(x₁, …, xₙ)` applies a relation symbol to variables. -/
structure Atom (L : Language.{u, v}) (α : Type w) where
  {arity : ℕ}
  /-- The relation symbol. -/
  rel : L.Relations arity
  /-- The variables the relation symbol is applied to. -/
  args : Fin arity → α

namespace Atom

variable {L : Language.{u, v}} {α : Type w} {β : Type x} {M : Type y} [L.Structure M]

/-- `a.map f` renames the variables of `a` along `f`. -/
def map (f : α → β) (a : L.Atom α) : L.Atom β := ⟨a.rel, f ∘ a.args⟩

@[simp] theorem map_id (a : L.Atom α) : a.map id = a := rfl

@[simp] theorem map_id' : (map id : L.Atom α → L.Atom α) = id := rfl

@[simp] theorem map_map {γ : Type*} (f : α → β) (g : β → γ) (a : L.Atom α) :
    (a.map f).map g = a.map (g ∘ f) := rfl

/-- An assignment realizes an atom when the relation holds of the values of its variables. -/
def Realize (a : L.Atom α) (v : α → M) : Prop := RelMap a.rel (v ∘ a.args)

@[simp] theorem realize_mk {n : ℕ} (R : L.Relations n) (xs : Fin n → α) (v : α → M) :
    (⟨R, xs⟩ : L.Atom α).Realize v ↔ RelMap R (v ∘ xs) :=
  .rfl

@[simp] theorem realize_map {f : α → β} {a : L.Atom α} {v : β → M} :
    (a.map f).Realize v ↔ a.Realize (v ∘ f) :=
  .rfl

/-- An atom as an atomic formula. -/
def toFormula (a : L.Atom α) : L.Formula α := a.rel.formula (Term.var ∘ a.args)

@[simp] theorem realize_toFormula {a : L.Atom α} {v : α → M} :
    a.toFormula.Realize v ↔ a.Realize v := by
  simp [toFormula, Realize, Function.comp_def]

/-- Permutations of the variables act on atoms by renaming. -/
instance : MulAction (Equiv.Perm α) (L.Atom α) where
  smul σ a := a.map σ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_def (σ : Equiv.Perm α) (a : L.Atom α) : σ • a = a.map σ := rfl

variable (M) in
/-- The assignments that realize every atom of a set. -/
def realizers (T : Set (L.Atom α)) : Set (α → M) :=
  upperPolar (fun a v ↦ a.Realize v) T

variable {T T₁ T₂ : Set (L.Atom α)} {v : α → M}

theorem mem_realizers : v ∈ realizers M T ↔ ∀ a ∈ T, a.Realize v :=
  .rfl

theorem realizers_union (T₁ T₂ : Set (L.Atom α)) :
    realizers M (T₁ ∪ T₂) = realizers M T₁ ∩ realizers M T₂ :=
  upperPolar_union ..

theorem realizers_anti : Antitone (realizers M : Set (L.Atom α) → Set (α → M)) :=
  upperPolar_anti _

theorem mem_realizers_image_map {f : α → β} {v : β → M} :
    v ∈ realizers M (map f '' T) ↔ v ∘ f ∈ realizers M T := by
  simp [mem_realizers]

theorem mem_realizers_smul {σ : Equiv.Perm α} : v ∈ realizers M (σ • T) ↔ v ∘ σ ∈ realizers M T :=
  mem_realizers_image_map

theorem comp_mem_realizers {N : Type*} [L.Structure N] (φ : M →[L] N) (hv : v ∈ realizers M T) :
    φ ∘ v ∈ realizers N T :=
  mem_realizers.2 fun a ha ↦ φ.map_rel a.rel _ (mem_realizers.1 hv a ha)

/-- The structure a set of atoms presents on its variables. -/
def Canonical (_ : Set (L.Atom α)) : Type w := α

namespace Canonical

/-- A variable, as an element of the canonical structure. -/
def of (T : Set (L.Atom α)) : α → Canonical T := id

variable [L.IsRelational]

instance (T : Set (L.Atom α)) : L.Structure (Canonical T) where
  funMap f := isEmptyElim f
  RelMap R xs := ⟨R, xs⟩ ∈ T

theorem of_comp_mem_realizers_iff {B : Set (L.Atom β)} {f : α → β} :
    of B ∘ f ∈ realizers (Canonical B) T ↔ map f '' T ⊆ B := by
  simp only [mem_realizers, Set.image_subset_iff]
  rfl

theorem of_mem_realizers (T : Set (L.Atom α)) : of T ∈ realizers (Canonical T) T :=
  of_comp_mem_realizers_iff (f := id) |>.2 <| by rintro _ ⟨a, ha, rfl⟩; exact ha

/-- The homomorphisms out of the canonical structure are the realizing assignments. -/
def homEquiv (T : Set (L.Atom α)) : (Canonical T →[L] M) ≃ realizers M T where
  toFun φ := ⟨φ ∘ of T, fun a h ↦ φ.map_rel a.rel _ h⟩
  invFun v := ⟨v.1, fun f ↦ isEmptyElim f, fun _ _ h ↦ v.2 h⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Canonical

/-- One set of atoms entails another along a map of variables in every structure exactly when the
map carries the atoms of the second into the first. -/
theorem forall_realizers_subset_preimage_iff [L.IsRelational] {B : Set (L.Atom β)} {f : α → β} :
    (∀ (M : Type x) [L.Structure M], realizers M B ⊆ (· ∘ f) ⁻¹' realizers M T) ↔
      map f '' T ⊆ B := by
  refine ⟨fun h ↦ ?_, fun h M _ v hv ↦ mem_realizers_image_map.1 (realizers_anti h hv)⟩
  exact Canonical.of_comp_mem_realizers_iff.1 (h _ (Canonical.of_mem_realizers B))

end Atom

end FirstOrder.Language
