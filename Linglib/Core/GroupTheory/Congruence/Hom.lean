/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Hom`, extending its `section Mul`. The monoid
`Con.lift`, `Con.kerLift` and `Con.map` are then these with `map_one'` added, as `Con.mk'` already
is `Con.mkMulHom`.
-/
module

public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Homomorphisms on a congruence quotient of a magma

Mathlib states the homomorphisms out of a congruence quotient, `Con.lift`, `Con.kerLift` and
`Con.map`, for `MulOneClass` and `MonoidHom`, although their construction never uses the unit. This
file states them for a bare multiplication. A `MulHom` constant on the classes of `c`
[lifts](##Con.liftMulHom) to `c.Quotient`, and uniquely, since homomorphisms out of the quotient
are [determined](##Con.mulHom_ext) by their composite with the quotient map. The lift is
[surjective](##Con.liftMulHom_surjective_iff) exactly when the homomorphism is, and
[injective](##Con.liftMulHom_injective_iff) exactly when `c` is its kernel. The
[kernel lift](##Con.kerLiftMulHom) and the [map induced by a coarsening](##Con.mapMulHom) are
special cases.
-/

@[expose] public section

open Function

variable {M N : Type*} [Mul M] [Mul N]

namespace Con

variable {c d : Con M} {f : M →ₙ* N}

/-- The natural homomorphism from a magma to its quotient by a congruence relation is
surjective. -/
@[to_additive /-- The natural homomorphism from an additive magma to its quotient by an additive
congruence relation is surjective. -/]
theorem mkMulHom_surjective : Surjective c.mkMulHom :=
  Quotient.mk''_surjective

/-! ### The universal property -/

variable (c f) in
/-- The homomorphism on the quotient of a magma by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
@[to_additive /-- The homomorphism on the quotient of an additive magma by an additive congruence
relation `c` induced by a homomorphism constant on `c`'s equivalence classes. -/]
def liftMulHom (H : c ≤ ker f) : c.Quotient →ₙ* N where
  toFun x := Con.liftOn x f fun _ _ h ↦ H h
  map_mul' x y := Con.induction_on₂ x y fun m n ↦ map_mul f m n

/-- The diagram describing the universal property for quotients of magmas commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
additive magmas commutes. -/]
theorem liftMulHom_coe (H : c ≤ ker f) (x : M) : c.liftMulHom f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of magmas commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
additive magmas commutes. -/]
theorem liftMulHom_comp_mkMulHom (H : c ≤ ker f) : (c.liftMulHom f H).comp c.mkMulHom = f :=
  rfl

/-- Homomorphisms on the quotient of a magma by a congruence relation `c` are equal if their
compositions with `c.mkMulHom` are equal. -/
@[to_additive (attr := ext) /-- Homomorphisms on the quotient of an additive magma by an additive
congruence relation `c` are equal if their compositions with `c.mkAddHom` are equal. -/]
theorem mulHom_ext {f g : c.Quotient →ₙ* N} (h : f.comp c.mkMulHom = g.comp c.mkMulHom) : f = g :=
  MulHom.ext fun x ↦ Con.induction_on x (DFunLike.congr_fun h)

/-- A homomorphism `f` from the quotient of a magma by a congruence relation is the homomorphism
induced on the quotient by `f` composed with the natural map to the quotient. -/
@[to_additive (attr := simp) /-- A homomorphism `f` from the quotient of an additive magma by an
additive congruence relation is the homomorphism induced on the quotient by `f` composed with the
natural map to the quotient. -/]
theorem liftMulHom_apply_mkMulHom (f : c.Quotient →ₙ* N) :
    c.liftMulHom (f.comp c.mkMulHom) (fun _ _ h ↦ congrArg f (c.eq.2 h)) = f :=
  mulHom_ext rfl

/-- The uniqueness part of the universal property for quotients of magmas. -/
@[to_additive /-- The uniqueness part of the universal property for quotients of additive
magmas. -/]
theorem liftMulHom_unique (H : c ≤ ker f) (g : c.Quotient →ₙ* N) (Hg : g.comp c.mkMulHom = f) :
    g = c.liftMulHom f H :=
  mulHom_ext Hg

/-- The homomorphism induced on the quotient is surjective exactly when the homomorphism is. -/
@[to_additive /-- The homomorphism induced on the quotient is surjective exactly when the
homomorphism is. -/]
theorem liftMulHom_surjective_iff {H : c ≤ ker f} :
    Surjective (c.liftMulHom f H) ↔ Surjective f :=
  Quot.surjective_lift _

/-- Surjective homomorphisms constant on a congruence relation `c`'s equivalence classes induce a
surjective homomorphism on `c`'s quotient. -/
@[to_additive /-- Surjective homomorphisms constant on an additive congruence relation `c`'s
equivalence classes induce a surjective homomorphism on `c`'s quotient. -/]
theorem liftMulHom_surjective_of_surjective (H : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.liftMulHom f H) :=
  liftMulHom_surjective_iff.2 hf

/-- The homomorphism induced on the quotient by `c` is injective exactly when `c` is the kernel of
the homomorphism. -/
@[to_additive /-- The homomorphism induced on the quotient by `c` is injective exactly when `c` is
the kernel of the homomorphism. -/]
theorem liftMulHom_injective_iff {H : c ≤ ker f} : Injective (c.liftMulHom f H) ↔ c = ker f :=
  (Setoid.lift_injective_iff_ker_eq_of_le H).trans
    ⟨fun h ↦ (toSetoid_injective h).symm, fun h ↦ h ▸ rfl⟩

/-! ### The kernel lift -/

variable (f) in
/-- The homomorphism induced on the quotient of a magma by the kernel of a homomorphism. -/
@[to_additive /-- The homomorphism induced on the quotient of an additive magma by the kernel of a
homomorphism. -/]
def kerLiftMulHom : (ker f).Quotient →ₙ* N :=
  (ker f).liftMulHom f le_rfl

/-- The diagram described by the universal property for quotients of magmas, when the congruence
relation is the kernel of the homomorphism, commutes. -/
@[to_additive (attr := simp) /-- The diagram described by the universal property for quotients of
additive magmas, when the additive congruence relation is the kernel of the homomorphism,
commutes. -/]
theorem kerLiftMulHom_mk (x : M) : kerLiftMulHom f x = f x :=
  rfl

/-- A homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive /-- A homomorphism `f` induces an injective homomorphism on the quotient by `f`'s
kernel. -/]
theorem kerLiftMulHom_injective (f : M →ₙ* N) : Injective (kerLiftMulHom f) :=
  liftMulHom_injective_iff.2 rfl

/-! ### The map induced by a coarsening -/

variable (c d) in
/-- Given congruence relations `c, d` on a magma such that `d` contains `c`, `d`'s quotient map
induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive /-- Given additive congruence relations `c, d` on an additive magma such that `d`
contains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient
by `d`. -/]
def mapMulHom (h : c ≤ d) : c.Quotient →ₙ* d.Quotient :=
  c.liftMulHom d.mkMulHom (h.trans (ker_mkMulHom_eq d).ge)

@[to_additive (attr := simp)]
theorem mapMulHom_coe (h : c ≤ d) (x : M) : c.mapMulHom d h x = x :=
  rfl

end Con
