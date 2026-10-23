/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Algebra.Group.Subquotient`, beside the GreensRelations stack;
split `Defs`/`Finite` at upstream time (the cardinality import doubles the import cone).
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Subquotients of monoids

A monoid `T` is a *subquotient* of a monoid `S` when `T` is a homomorphic image of a
submonoid of `S`. In finite semigroup theory the relation is called *division* (`T ≼ S`), and in
group theory a *section*. This file defines the relation and proves it transitive, closed under
products, and, on finite monoids, antisymmetric up to isomorphism.

## Main definitions

* `Monoid.IsSubquotient T S`: `T` is a homomorphic image of a submonoid of `S`.

## References

* [eilenberg-1976]
-/

@[expose] public section

namespace Monoid

variable {T S R : Type*} [Monoid T] [Monoid S] [Monoid R]

/-- A monoid `T` is a *subquotient* of `S` when it is a homomorphic image of a submonoid
of `S`. -/
@[to_additive /-- An additive monoid `T` is a *subquotient* of `S` when it is a homomorphic
image of an additive submonoid of `S`. -/]
def IsSubquotient (T S : Type*) [Monoid T] [Monoid S] : Prop :=
  ∃ (N : Submonoid S) (f : N →* T), Function.Surjective f

@[to_additive]
theorem IsSubquotient.of_surjective (f : S →* T) (hf : Function.Surjective f) :
    IsSubquotient T S :=
  ⟨⊤, f.comp Submonoid.topEquiv.toMonoidHom, hf.comp Submonoid.topEquiv.surjective⟩

@[to_additive]
theorem _root_.MulEquiv.isSubquotient (e : T ≃* S) : IsSubquotient T S :=
  IsSubquotient.of_surjective e.symm.toMonoidHom e.symm.surjective

@[to_additive (attr := refl)]
theorem IsSubquotient.refl (T : Type*) [Monoid T] : IsSubquotient T T :=
  (MulEquiv.refl T).isSubquotient

@[to_additive]
theorem _root_.Submonoid.isSubquotient (N : Submonoid S) : IsSubquotient N S :=
  ⟨N, .id _, Function.surjective_id⟩

@[to_additive]
theorem _root_.Con.isSubquotient_quotient (c : Con S) : IsSubquotient c.Quotient S :=
  IsSubquotient.of_surjective c.mk' c.mk'_surjective

@[to_additive]
theorem _root_.MonoidHom.isSubquotient_mrange (f : S →* T) :
    IsSubquotient (MonoidHom.mrange f) S :=
  IsSubquotient.of_surjective f.mrangeRestrict f.mrangeRestrict_surjective

@[to_additive]
theorem IsSubquotient.trans (hTS : IsSubquotient T S) (hSR : IsSubquotient S R) :
    IsSubquotient T R := by
  obtain ⟨N, f, hf⟩ := hTS
  obtain ⟨M, g, hg⟩ := hSR
  have e := Submonoid.equivMapOfInjective (N.comap g) M.subtype M.subtype_injective
  exact ⟨(N.comap g).map M.subtype, (f.comp (g.submonoidComap N)).comp e.symm.toMonoidHom,
    (hf.comp (g.submonoidComap_surjective N hg)).comp e.symm.surjective⟩

@[to_additive]
theorem IsSubquotient.of_injective (f : T →* S) (hf : Function.Injective f) :
    IsSubquotient T S :=
  (MulEquiv.ofLeftInverse' f (Function.leftInverse_invFun hf)).isSubquotient.trans
    (MonoidHom.mrange f).isSubquotient

@[to_additive isSubquotient_prod_left]
theorem isSubquotient_prod_left (T S : Type*) [Monoid T] [Monoid S] :
    IsSubquotient T (T × S) :=
  IsSubquotient.of_injective (MonoidHom.inl T S) (Prod.mk_left_injective 1)

@[to_additive isSubquotient_prod_right]
theorem isSubquotient_prod_right (T S : Type*) [Monoid T] [Monoid S] :
    IsSubquotient T (S × T) :=
  IsSubquotient.of_injective (MonoidHom.inr S T) (Prod.mk_right_injective 1)

@[to_additive IsSubquotient.prod /-- Subquotients are closed under componentwise
products. -/]
theorem IsSubquotient.prod {T' S' : Type*} [Monoid T'] [Monoid S']
    (h : IsSubquotient T S) (h' : IsSubquotient T' S') :
    IsSubquotient (T × T') (S × S') := by
  obtain ⟨N, f, hf⟩ := h
  obtain ⟨N', f', hf'⟩ := h'
  exact ⟨N.prod N', (f.prodMap f').comp (N.prodEquiv N').toMonoidHom,
    (hf.prodMap hf').comp (N.prodEquiv N').surjective⟩

@[to_additive]
theorem IsSubquotient.finite [Finite S] (h : IsSubquotient T S) : Finite T := by
  obtain ⟨N, f, hf⟩ := h
  exact .of_surjective f hf

@[to_additive]
theorem IsSubquotient.card_le [Finite S] (h : IsSubquotient T S) :
    Nat.card T ≤ Nat.card S := by
  obtain ⟨N, f, hf⟩ := h
  exact (Nat.card_le_card_of_surjective f hf).trans
    (Nat.card_le_card_of_injective N.subtype N.subtype_injective)

@[to_additive /-- A subquotient of maximal cardinality is an isomorph. -/]
theorem IsSubquotient.nonempty_mulEquiv_of_card_le [Finite S] (hTS : IsSubquotient T S)
    (hle : Nat.card S ≤ Nat.card T) : Nonempty (T ≃* S) := by
  obtain ⟨N, f, hf⟩ := hTS
  have hNS : Nat.card N ≤ Nat.card S := Nat.card_le_card_of_injective _ N.subtype_injective
  have hSN : Nat.card S ≤ Nat.card N := hle.trans (Nat.card_le_card_of_surjective f hf)
  exact ⟨(MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (hNS.trans hle))).symm.trans
    (MulEquiv.ofBijective N.subtype (N.subtype_injective.bijective_of_nat_card_le hSN))⟩

@[to_additive /-- Finite additive monoids that are subquotients of each other are
isomorphic. -/]
theorem IsSubquotient.nonempty_mulEquiv [Finite S] (hTS : IsSubquotient T S)
    (hST : IsSubquotient S T) : Nonempty (T ≃* S) := by
  have := hTS.finite
  exact hTS.nonempty_mulEquiv_of_card_le hST.card_le

end Monoid
