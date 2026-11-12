/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Ortholattice
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Ortholattice homomorphisms

An ortholattice homomorphism is a bounded lattice homomorphism that preserves the complement.
Between Boolean algebras every bounded lattice homomorphism is one, since complements there are
unique; between ortholattices preserving the complement is a further condition. A map that
preserves meets, the top and the complement is an ortholattice homomorphism, [by De
Morgan](##OrtholatticeHom.ofInfTopHom).

We use the `DFunLike` design, so the type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Implementation notes

The definitions assume only a `Compl` on each side, as mathlib's `SupHom` assumes only `Max`, so
that they apply to the lattices with an involution of `Core/Order/InvolutiveCompl.lean` as well as
to ortholattices. The class field `OrtholatticeHomClass.map_compl` is not exported: the root name
`map_compl` is mathlib's lemma for Heyting homomorphisms.

`[UPSTREAM]` candidate, beside `Mathlib/Order/Heyting/Hom.lean`.
-/

@[expose] public section

open Function

variable {F α β γ δ : Type*}

/-- The type of ortholattice homomorphisms from `α` to `β`: bounded lattice homomorphisms that
preserve the complement. -/
structure OrtholatticeHom (α β : Type*) [Lattice α] [BoundedOrder α] [Compl α] [Lattice β]
    [BoundedOrder β] [Compl β] extends BoundedLatticeHom α β where
  /-- An ortholattice homomorphism preserves the complement. -/
  protected map_compl' : ∀ a, toFun aᶜ = (toFun a)ᶜ

/-- `OrtholatticeHomClass F α β` states that `F` is a type of ortholattice homomorphisms.

You should extend this class when you extend `OrtholatticeHom`. -/
class OrtholatticeHomClass (F α β : Type*) [Lattice α] [BoundedOrder α] [Compl α] [Lattice β]
    [BoundedOrder β] [Compl β] [FunLike F α β] : Prop
    extends BoundedLatticeHomClass F α β where
  /-- An ortholattice homomorphism preserves the complement. -/
  map_compl (f : F) (a : α) : f aᶜ = (f a)ᶜ

attribute [simp] OrtholatticeHomClass.map_compl

/-- Between Boolean algebras every bounded lattice homomorphism preserves the complement. -/
instance (priority := 100) BoundedLatticeHomClass.toOrtholatticeHomClass [BooleanAlgebra α]
    [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β] :
    OrtholatticeHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with map_compl := map_compl' }

namespace OrtholatticeHom

section Compl

variable [Lattice α] [BoundedOrder α] [Compl α] [Lattice β] [BoundedOrder β] [Compl β]
  [Lattice γ] [BoundedOrder γ] [Compl γ] [Lattice δ] [BoundedOrder δ] [Compl δ]

instance : FunLike (OrtholatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := g
    congr

instance : OrtholatticeHomClass (OrtholatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'
  map_compl f := f.map_compl'

@[simp] theorem toFun_eq_coe (f : OrtholatticeHom α β) : f.toFun = f := rfl

@[simp] theorem coe_toBoundedLatticeHom (f : OrtholatticeHom α β) :
    ⇑f.toBoundedLatticeHom = f := rfl

@[ext]
theorem ext {f g : OrtholatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (α) in
/-- `id` as an `OrtholatticeHom`. -/
protected def id : OrtholatticeHom α α where
  toBoundedLatticeHom := BoundedLatticeHom.id α
  map_compl' _ := rfl

@[simp, norm_cast] theorem coe_id : ⇑(OrtholatticeHom.id α) = id := rfl

@[simp] theorem id_apply (a : α) : OrtholatticeHom.id α a = a := rfl

instance : Inhabited (OrtholatticeHom α α) := ⟨OrtholatticeHom.id α⟩

/-- Composition of `OrtholatticeHom`s as an `OrtholatticeHom`. -/
def comp (f : OrtholatticeHom β γ) (g : OrtholatticeHom α β) : OrtholatticeHom α γ where
  toBoundedLatticeHom := f.toBoundedLatticeHom.comp g.toBoundedLatticeHom
  map_compl' a := by simp

@[simp] theorem coe_comp (f : OrtholatticeHom β γ) (g : OrtholatticeHom α β) :
    ⇑(f.comp g) = f ∘ g := rfl

@[simp] theorem comp_apply (f : OrtholatticeHom β γ) (g : OrtholatticeHom α β) (a : α) :
    f.comp g a = f (g a) := rfl

@[simp] theorem comp_assoc (f : OrtholatticeHom γ δ) (g : OrtholatticeHom β γ)
    (h : OrtholatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp] theorem comp_id (f : OrtholatticeHom α β) : f.comp (OrtholatticeHom.id α) = f :=
  ext fun _ ↦ rfl

@[simp] theorem id_comp (f : OrtholatticeHom α β) : (OrtholatticeHom.id β).comp f = f :=
  ext fun _ ↦ rfl

end Compl

section InvolutiveCompl

variable [Lattice α] [BoundedOrder α] [InvolutiveCompl α] [Lattice β] [BoundedOrder β]
  [InvolutiveCompl β]

/-- A map between lattices with an involution that preserves meets, the top and the complement is
an ortholattice homomorphism: it preserves joins and the bottom by De Morgan. -/
def ofInfTopHom (f : InfTopHom α β) (map_compl : ∀ a, f aᶜ = (f a)ᶜ) : OrtholatticeHom α β where
  toFun := f
  map_inf' := map_inf f
  map_top' := map_top f
  map_sup' a b := by
    rw [← InvolutiveCompl.compl_compl (a ⊔ b), InvolutiveCompl.compl_sup, map_compl, map_inf,
      map_compl, map_compl, InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl,
      InvolutiveCompl.compl_compl]
  map_bot' := by
    rw [← InvolutiveCompl.compl_top (α := α), map_compl, map_top, InvolutiveCompl.compl_top]
  map_compl' := map_compl

@[simp] theorem coe_ofInfTopHom (f : InfTopHom α β) (map_compl : ∀ a, f aᶜ = (f a)ᶜ) :
    ⇑(ofInfTopHom f map_compl) = f := rfl

end InvolutiveCompl

end OrtholatticeHom
