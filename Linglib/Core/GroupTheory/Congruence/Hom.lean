/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Hom`, extending its `section Mul`.
Upstreaming needs `@[to_additive]` on each declaration, and the monoid `Con.lift`/`Con.map`
should then be re-derived from these, as `Con.mk'` already is from `Con.mkMulHom`.
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Homomorphisms on a congruence quotient of a magma

Mathlib's `Con` API for quotient homomorphisms — `Con.lift`, `Con.kerLift`, `Con.map` and the
isomorphism theorems — lives in `section MulOneClass` and is `MonoidHom`-valued. Its `section Mul`
provides only `Con.mkMulHom`, `Con.ker`, `Con.mapGen`, `Con.mapOfSurjective` and
`Con.correspondence`. This file adds the `MulHom`-valued lift, together with its universal
property, the kernel lift, and the map induced by a coarsening.

Homomorphisms are *consumed* through `MulHomClass` and *produced* as concrete `→ₙ*`, following
`Con.ker` and `Con.mapOfSurjective`. The cost of consuming through `MulHomClass` is that the
universal-property statements coerce the argument, as in `liftMulHom_comp_mkMulHom`.

## Main definitions

* `Con.liftMulHom`: the homomorphism induced on the quotient by one constant on the classes.
* `Con.kerLiftMulHom`: the homomorphism induced by `f` on the quotient by its kernel.
* `Con.mapMulHom`: the homomorphism `c.Quotient →ₙ* d.Quotient` induced by `c ≤ d`.

## Main results

* `Con.mulHom_ext`, `Con.liftMulHom_unique`: the universal property of the quotient.
* `Con.liftMulHom_injective`, `Con.kerLiftMulHom_injective`: injectivity of the lifts.
* `Con.ker_prod`, `Con.ker_prodMulHom`: the kernel of a paired homomorphism is the meet of the
  kernels.
-/

@[expose] public section

variable {M N : Type*} [Mul M] [Mul N] {F : Type*} [FunLike F M N] [MulHomClass F M N]

namespace Con

variable (c : Con M)

/-- The homomorphism on `c.Quotient` induced by a homomorphism constant on `c`'s classes. -/
def liftMulHom (f : F) (H : c ≤ Con.ker f) : c.Quotient →ₙ* N where
  toFun x := Con.liftOn x f fun _ _ h => H h
  map_mul' x y := Con.induction_on₂ x y fun _ _ => by
    dsimp only [← Con.coe_mul, Con.liftOn_coe]
    rw [map_mul]

@[simp] theorem liftMulHom_coe (f : F) (H : c ≤ Con.ker f) (x : M) :
    c.liftMulHom f H (x : c.Quotient) = f x := rfl

@[simp] theorem liftMulHom_comp_mkMulHom (f : F) (H : c ≤ Con.ker f) :
    (c.liftMulHom f H).comp (mkMulHom c) = (f : M →ₙ* N) := rfl

theorem mkMulHom_surjective : Function.Surjective (mkMulHom c) := Quotient.mk''_surjective

variable {c} in
theorem liftMulHom_surjective_of_surjective {f : F} (H : c ≤ Con.ker f)
    (hf : Function.Surjective f) : Function.Surjective (c.liftMulHom f H) := fun y =>
  have ⟨w, hw⟩ := hf y
  ⟨(w : c.Quotient), hw⟩

variable {c} in
/-- The lift is injective when the kernel of `f` refines the congruence. -/
theorem liftMulHom_injective {f : F} {H : c ≤ Con.ker f} (H' : Con.ker f ≤ c) :
    Function.Injective (c.liftMulHom f H) := fun x y =>
  Con.induction_on₂ x y fun _ _ h => c.eq.2 <| H' <| (Con.ker_rel f).mpr h

theorem liftMulHom_apply_mkMulHom (f : c.Quotient →ₙ* N) :
    (c.liftMulHom (f.comp (mkMulHom c)) fun _ _ h => congrArg f (c.eq.2 h)) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- **Extensionality for homomorphisms out of a congruence quotient**: they agree as soon as they
agree on the quotient map. -/
@[ext] theorem mulHom_ext {f g : c.Quotient →ₙ* N}
    (h : f.comp (mkMulHom c) = g.comp (mkMulHom c)) : f = g := by
  rw [← liftMulHom_apply_mkMulHom c f, ← liftMulHom_apply_mkMulHom c g]; congr 1

theorem liftMulHom_funext (f g : c.Quotient →ₙ* N) (h : ∀ a : M, f a = g a) : f = g :=
  mulHom_ext c <| DFunLike.ext _ _ h

/-- **The universal property**: the lift is the unique homomorphism restricting to `f`. -/
theorem liftMulHom_unique {f : F} (H : c ≤ Con.ker f) (g : c.Quotient →ₙ* N)
    (Hg : g.comp (mkMulHom c) = (f : M →ₙ* N)) : g = c.liftMulHom f H :=
  mulHom_ext c (Hg.trans (liftMulHom_comp_mkMulHom c f H).symm)

/-- The homomorphism induced by `f` on the quotient by its kernel. -/
def kerLiftMulHom (f : F) : (Con.ker f).Quotient →ₙ* N := liftMulHom _ f le_rfl

@[simp] theorem kerLiftMulHom_coe (f : F) (x : M) :
    kerLiftMulHom f (x : (Con.ker f).Quotient) = f x := rfl

/-- The kernel lift is injective: it exhibits `(ker f).Quotient` as a sub-object of `N`, which is
what closure-under-quotient arguments consume. -/
theorem kerLiftMulHom_injective (f : F) : Function.Injective (kerLiftMulHom f) :=
  liftMulHom_injective le_rfl

theorem kerLiftMulHom_surjective_of_surjective {f : F} (hf : Function.Surjective f) :
    Function.Surjective (kerLiftMulHom f) := liftMulHom_surjective_of_surjective le_rfl hf

/-- The homomorphism of quotients induced by a coarsening `c ≤ d`. -/
def mapMulHom (d : Con M) (h : c ≤ d) : c.Quotient →ₙ* d.Quotient :=
  c.liftMulHom (d.mkMulHom) (by rw [Con.ker_mkMulHom_eq]; exact h)

@[simp] theorem mapMulHom_coe (d : Con M) (h : c ≤ d) (x : M) :
    c.mapMulHom d h (x : c.Quotient) = (x : d.Quotient) := rfl

theorem mapMulHom_surjective (d : Con M) (h : c ≤ d) :
    Function.Surjective (c.mapMulHom d h) :=
  liftMulHom_surjective_of_surjective _ d.mkMulHom_surjective

/-! ### Kernels of paired homomorphisms -/

/-- The kernel of a paired homomorphism is the meet of the kernels. -/
theorem ker_prodMulHom {N' : Type*} [Mul N'] (f : M →ₙ* N) (g : M →ₙ* N') :
    Con.ker (f.prod g) = Con.ker f ⊓ Con.ker g :=
  Con.ext fun _ _ => by simp [Con.ker_rel, Prod.ext_iff, Con.inf_iff_and]

/-- The kernel of a paired monoid homomorphism is the meet of the kernels. -/
theorem ker_prod {M N N' : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass N']
    (f : M →* N) (g : M →* N') : Con.ker (f.prod g) = Con.ker f ⊓ Con.ker g :=
  ker_prodMulHom (f : M →ₙ* N) (g : M →ₙ* N')

end Con
