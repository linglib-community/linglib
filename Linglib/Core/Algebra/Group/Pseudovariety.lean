/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Pseudovariety`.
-/
module

public import Linglib.Core.Algebra.Group.Aperiodic
public import Linglib.Core.Algebra.Group.LocallyTrivial
public import Linglib.Core.Algebra.Group.Subquotient
public import Linglib.Core.GroupTheory.Congruence.Hom
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Fintype.Option
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Order.CompleteLattice.Defs

/-!
# Pseudovarieties of finite monoids and semigroups

This file defines pseudovarieties of finite monoids and of finite semigroups. A *pseudovariety* is
a class of finite monoids, or of finite semigroups, closed under submonoids or subsemigroups,
quotients and finite direct products, the empty product being the trivial one. Pseudovarieties are
the algebraic side of Eilenberg's variety theorem, which matches the monoid ones with the
varieties of regular languages and the semigroup ones with the varieties of languages of nonempty
words.

## Main definitions

* `Monoid.Pseudovariety`, `Semigroup.Pseudovariety`: classes of finite monoids, respectively
  semigroups, closed under substructures, quotients and products.
* `Monoid.Pseudovariety.generated`: the least pseudovariety containing a class of finite monoids.
* `Monoid.aperiodicVariety`: the pseudovariety of finite aperiodic monoids.
* `Semigroup.definiteVariety`, `Semigroup.reverseDefiniteVariety`,
  `Semigroup.locallyTrivialVariety`: the pseudovarieties **D**, **K** and **LI**.

## Main results

* `Monoid.Pseudovariety.pi_mem`: closure under finite dependent products.
* `Monoid.Pseudovariety.mem_quotient_of_le`, `mem_quotient_ker`, `mem_quotient_inf` and their
  semigroup counterparts: closure properties of quotients by congruences.
* The pseudovarieties of finite monoids form a complete lattice, with infimum the intersection.

## Implementation notes

`mem` is a total predicate on `Type u` monoids or semigroups that implies finiteness
(`finite_of_mem`), so the order on pseudovarieties is inclusion of classes of finite structures and
is antisymmetric. The structures live in a fixed universe `u`, like mathlib's `MorphismProperty`;
concrete pseudovarieties are universe-polymorphic definitions. The semigroup pseudovarieties
**D**, **K** and **LI** have no monoid counterpart, since their conditions at the idempotent `1`
force triviality; the pseudovariety **N** of nilpotent semigroups is the intersection of **D** and
**K** and is not bundled.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

universe u

namespace Monoid

/-- A *pseudovariety of finite monoids* is a class of finite monoids closed under submonoids,
quotients and finite products, with closure phrased through injective and surjective
homomorphisms. -/
structure Pseudovariety where
  /-- The monoids belonging to the pseudovariety. -/
  mem : ∀ (M : Type u) [Monoid M], Prop
  /-- Every member is finite. -/
  finite_of_mem : ∀ {M : Type u} [Monoid M], mem M → Finite M
  /-- The domain of an injective homomorphism into a member is a member. -/
  sub : ∀ {M N : Type u} [Monoid M] [Monoid N] {f : M →* N},
    Function.Injective f → mem N → mem M
  /-- The codomain of a surjective homomorphism from a member is a member. -/
  quot : ∀ {M N : Type u} [Monoid M] [Monoid N] {f : M →* N},
    Function.Surjective f → mem M → mem N
  /-- The product of two members is a member. -/
  prod : ∀ {M N : Type u} [Monoid M] [Monoid N], mem M → mem N → mem (M × N)
  /-- The trivial monoid is a member. -/
  memUnit : mem PUnit.{u + 1}

namespace Pseudovariety

variable (V : Pseudovariety.{u})

@[ext] theorem ext {V W : Pseudovariety.{u}}
    (h : ∀ (M : Type u) [Monoid M], V.mem M ↔ W.mem M) : V = W := by
  obtain ⟨Vm, _, _, _, _, _⟩ := V
  obtain ⟨Wm, _, _, _, _, _⟩ := W
  obtain rfl : Vm = Wm := funext fun M ↦ funext fun _ ↦ propext (h M)
  rfl

instance : PartialOrder Pseudovariety.{u} where
  le V W := ∀ (M : Type u) [Monoid M], V.mem M → W.mem M
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ M _ h := h₂ M (h₁ M h)
  le_antisymm _ _ h₁ h₂ := ext fun M _ ↦ ⟨h₁ M, h₂ M⟩

theorem le_def {V W : Pseudovariety.{u}} :
    V ≤ W ↔ ∀ (M : Type u) [Monoid M], V.mem M → W.mem M := Iff.rfl

theorem mem_of_mulEquiv {M N : Type u} [Monoid M] [Monoid N] (e : M ≃* N) (h : V.mem M) :
    V.mem N :=
  V.quot (f := e.toMonoidHom) e.surjective h

theorem mem_of_isSubquotient {M N : Type u} [Monoid M] [Monoid N] (h : IsSubquotient M N)
    (hN : V.mem N) : V.mem M := by
  obtain ⟨P, f, hf⟩ := h
  exact V.quot hf (V.sub P.subtype_injective hN)

/-! ### Quotients by congruences -/

/-- Membership of a quotient descends along a coarsening of congruences. -/
theorem mem_quotient_of_le {M : Type u} [Monoid M] {c d : Con M} (h : c ≤ d)
    (hc : V.mem c.Quotient) : V.mem d.Quotient :=
  V.quot (f := Con.map c d h) (Con.lift_surjective_of_surjective _ Con.mk'_surjective) hc

/-- The quotient by the kernel of a homomorphism into a member is a member. -/
theorem mem_quotient_ker {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) (h : V.mem N) :
    V.mem (Con.ker f).Quotient :=
  V.sub (Con.kerLift_injective f) h

/-- The quotient by the meet of two congruences is a member when both quotients are. -/
theorem mem_quotient_inf {M : Type u} [Monoid M] {c d : Con M} (hc : V.mem c.Quotient)
    (hd : V.mem d.Quotient) : V.mem (c ⊓ d).Quotient := by
  have h : Con.ker (c.mk'.prod d.mk') ≤ c ⊓ d := by
    rw [Con.ker_prod, Con.mk'_ker, Con.mk'_ker]
  exact V.mem_quotient_of_le h (V.mem_quotient_ker _ (V.prod hc hd))

/-! ### Finite products -/

/-- Reindexing a dependent product of monoids along an equivalence of the index. -/
private def piCongrLeftMul {α β : Type*} (P : β → Type*) [∀ b, Mul (P b)] (e : α ≃ β) :
    (∀ a, P (e a)) ≃* (∀ b, P b) :=
  { Equiv.piCongrLeft P e with
    map_mul' := fun f g ↦ by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp [Equiv.piCongrLeft_apply_apply] }

/-- Splitting a dependent product of monoids over `Option`. -/
private def piOptionEquivProdMul {α : Type*} (f : Option α → Type*) [∀ i, Mul (f i)] :
    (∀ i, f i) ≃* f none × ∀ a, f (some a) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _ ↦ rfl }

/-- A pseudovariety is closed under finite dependent products. -/
theorem pi_mem {ι : Type u} [Finite ι] {f : ι → Type u} [∀ i, Monoid (f i)]
    (h : ∀ i, V.mem (f i)) : V.mem (∀ i, f i) := by
  refine Finite.induction_empty_option
    (P := fun J ↦ ∀ (g : J → Type u) [∀ i, Monoid (g i)], (∀ i, V.mem (g i)) → V.mem (∀ i, g i))
    ?_ ?_ ?_ ι f h
  · intro α β e ih g _ hg
    exact V.mem_of_mulEquiv (piCongrLeftMul g e) (ih (fun a ↦ g (e a)) fun a ↦ hg (e a))
  · intro g _ _
    exact V.mem_of_mulEquiv (MulEquiv.ofUnique (M := PUnit.{u + 1})) V.memUnit
  · intro α _ ih g _ hg
    exact V.mem_of_mulEquiv (piOptionEquivProdMul g).symm
      (V.prod (hg none) (ih _ fun a ↦ hg (some a)))

/-! ### The lattice of pseudovarieties -/

instance : InfSet Pseudovariety.{u} where
  sInf s :=
    { mem M := Finite M ∧ ∀ V ∈ s, V.mem M
      finite_of_mem h := h.1
      sub hf h := have := h.1; ⟨.of_injective _ hf, fun V hV ↦ V.sub hf (h.2 V hV)⟩
      quot hf h := have := h.1; ⟨.of_surjective _ hf, fun V hV ↦ V.quot hf (h.2 V hV)⟩
      prod hM hN := have := hM.1; have := hN.1
        ⟨inferInstance, fun V hV ↦ V.prod (hM.2 V hV) (hN.2 V hV)⟩
      memUnit := ⟨inferInstance, fun V _ ↦ V.memUnit⟩ }

theorem mem_sInf {s : Set Pseudovariety.{u}} {M : Type u} [Monoid M] :
    (sInf s).mem M ↔ Finite M ∧ ∀ V ∈ s, V.mem M := Iff.rfl

instance : CompleteLattice Pseudovariety.{u} :=
  completeLatticeOfInf _ fun _ ↦ ⟨fun V hV _ _ hM ↦ hM.2 V hV,
    fun V hV M _ hM ↦ mem_sInf.2 ⟨V.finite_of_mem hM, fun _ hW ↦ hV hW M hM⟩⟩

/-- The greatest pseudovariety consists of all finite monoids. -/
@[simp] theorem mem_top {M : Type u} [Monoid M] : (⊤ : Pseudovariety.{u}).mem M ↔ Finite M :=
  ⟨And.left, fun h ↦ ⟨h, fun _ h ↦ h.elim⟩⟩

/-- The least pseudovariety consists of the trivial monoids. -/
@[simp] theorem mem_bot {M : Type u} [Monoid M] :
    (⊥ : Pseudovariety.{u}).mem M ↔ Subsingleton M := by
  refine ⟨fun h ↦ h.2 ⟨fun M _ ↦ Subsingleton M, fun _ ↦ Finite.of_subsingleton,
    fun hf _ ↦ hf.subsingleton, fun hf _ ↦ hf.subsingleton, fun _ _ ↦ inferInstance,
    inferInstance⟩ trivial, fun _ ↦ ?_⟩
  have : Unique M := uniqueOfSubsingleton 1
  exact ⟨Finite.of_subsingleton, fun V _ ↦ V.mem_of_mulEquiv MulEquiv.ofUnique V.memUnit⟩

/-- The pseudovariety *generated* by a class of monoids is the least pseudovariety containing its
finite members. -/
def generated (S : ∀ (M : Type u) [Monoid M], Prop) : Pseudovariety.{u} :=
  sInf {V | ∀ (N : Type u) [Monoid N] [Finite N], S N → V.mem N}

theorem subset_generated {S : ∀ (M : Type u) [Monoid M], Prop} {M : Type u} [Monoid M]
    [Finite M] (h : S M) : (generated S).mem M :=
  ⟨‹_›, fun _ hV ↦ hV M h⟩

theorem generated_le {S : ∀ (M : Type u) [Monoid M], Prop} {V : Pseudovariety.{u}}
    (h : ∀ (N : Type u) [Monoid N] [Finite N], S N → V.mem N) : generated S ≤ V :=
  sInf_le h

end Pseudovariety

/-- The pseudovariety of finite aperiodic monoids, the algebraic counterpart of the star-free
languages. -/
def aperiodicVariety : Pseudovariety.{u} where
  mem M _ := Finite M ∧ IsAperiodic M
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hM hN := have := hM.1; have := hN.1; ⟨inferInstance, hM.2.prod hN.2⟩
  memUnit := ⟨inferInstance, IsAperiodic.of_subsingleton⟩

@[simp] theorem mem_aperiodicVariety {M : Type u} [Monoid M] :
    aperiodicVariety.mem M ↔ Finite M ∧ IsAperiodic M := Iff.rfl

end Monoid

namespace Semigroup

/-- A *pseudovariety of finite semigroups* is a class of finite semigroups closed under
subsemigroups, quotients and finite products, with closure phrased through injective and surjective
`MulHom`s. -/
structure Pseudovariety where
  /-- The semigroups belonging to the pseudovariety. -/
  mem : ∀ (S : Type u) [Semigroup S], Prop
  /-- Every member is finite. -/
  finite_of_mem : ∀ {S : Type u} [Semigroup S], mem S → Finite S
  /-- The domain of an injective homomorphism into a member is a member. -/
  sub : ∀ {S T : Type u} [Semigroup S] [Semigroup T] {f : S →ₙ* T},
    Function.Injective f → mem T → mem S
  /-- The codomain of a surjective homomorphism from a member is a member. -/
  quot : ∀ {S T : Type u} [Semigroup S] [Semigroup T] {f : S →ₙ* T},
    Function.Surjective f → mem S → mem T
  /-- The product of two members is a member. -/
  prod : ∀ {S T : Type u} [Semigroup S] [Semigroup T], mem S → mem T → mem (S × T)
  /-- The trivial semigroup is a member. -/
  memUnit : mem PUnit.{u + 1}

namespace Pseudovariety

variable (V : Pseudovariety.{u})

@[ext] theorem ext {V W : Pseudovariety.{u}}
    (h : ∀ (S : Type u) [Semigroup S], V.mem S ↔ W.mem S) : V = W := by
  obtain ⟨Vm, _, _, _, _, _⟩ := V
  obtain ⟨Wm, _, _, _, _, _⟩ := W
  obtain rfl : Vm = Wm := funext fun S ↦ funext fun _ ↦ propext (h S)
  rfl

instance : PartialOrder Pseudovariety.{u} where
  le V W := ∀ (S : Type u) [Semigroup S], V.mem S → W.mem S
  le_refl _ _ _ h := h
  le_trans _ _ _ h₁ h₂ S _ h := h₂ S (h₁ S h)
  le_antisymm _ _ h₁ h₂ := ext fun S _ ↦ ⟨h₁ S, h₂ S⟩

theorem mem_of_mulEquiv {S T : Type u} [Semigroup S] [Semigroup T] (e : S ≃* T) (h : V.mem S) :
    V.mem T :=
  V.quot (f := e.toMulHom) e.surjective h

/-- Membership of a quotient descends along a coarsening of congruences. -/
theorem mem_quotient_of_le {S : Type u} [Semigroup S] {c d : Con S} (h : c ≤ d)
    (hc : V.mem c.Quotient) : V.mem d.Quotient :=
  V.quot (Con.mapMulHom_surjective c d h) hc

/-- The quotient by the kernel of a homomorphism into a member is a member. -/
theorem mem_quotient_ker {S T : Type u} [Semigroup S] [Semigroup T] (f : S →ₙ* T)
    (h : V.mem T) : V.mem (Con.ker f).Quotient :=
  V.sub (Con.kerLiftMulHom_injective f) h

/-- The quotient by the meet of two congruences is a member when both quotients are. -/
theorem mem_quotient_inf {S : Type u} [Semigroup S] {c d : Con S} (hc : V.mem c.Quotient)
    (hd : V.mem d.Quotient) : V.mem (c ⊓ d).Quotient := by
  have h : Con.ker (c.mkMulHom.prod d.mkMulHom) ≤ c ⊓ d := by
    rw [Con.ker_prodMulHom, Con.ker_mkMulHom_eq, Con.ker_mkMulHom_eq]
  exact V.mem_quotient_of_le h (V.mem_quotient_ker _ (V.prod hc hd))

end Pseudovariety

/-! ### The bundled pseudovarieties -/

/-- The pseudovariety **D** of definite semigroups. -/
def definiteVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsDefinite S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

/-- The pseudovariety **K** of reverse definite semigroups. -/
def reverseDefiniteVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsReverseDefinite S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

/-- The pseudovariety **LI** of locally trivial semigroups. -/
def locallyTrivialVariety : Pseudovariety.{u} where
  mem S _ := Finite S ∧ IsLocallyTrivial S
  finite_of_mem h := h.1
  sub hf h := have := h.1; ⟨.of_injective _ hf, h.2.of_injective hf⟩
  quot hf h := have := h.1; ⟨.of_surjective _ hf, h.2.of_surjective hf⟩
  prod hS hT := have := hS.1; have := hT.1; ⟨inferInstance, hS.2.prod hT.2⟩
  memUnit := ⟨inferInstance, fun _ _ _ ↦ rfl⟩

@[simp] theorem mem_definiteVariety {S : Type u} [Semigroup S] :
    definiteVariety.mem S ↔ Finite S ∧ IsDefinite S := Iff.rfl

@[simp] theorem mem_reverseDefiniteVariety {S : Type u} [Semigroup S] :
    reverseDefiniteVariety.mem S ↔ Finite S ∧ IsReverseDefinite S := Iff.rfl

@[simp] theorem mem_locallyTrivialVariety {S : Type u} [Semigroup S] :
    locallyTrivialVariety.mem S ↔ Finite S ∧ IsLocallyTrivial S := Iff.rfl

end Semigroup
