/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.GroupTheory.Congruence.Basic`, beside `Con.prod`.
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Kernels of paired homomorphisms

The kernel of the pairing `x ↦ (f x, g x)` of two homomorphisms is the meet of their kernels, for
[magma](##Con.ker_prodMulHom) and for [monoid](##Con.ker_prod) homomorphisms.
-/

@[expose] public section

namespace Con

variable {M N N' : Type*}

/-- The kernel of a paired homomorphism is the meet of the kernels. -/
@[to_additive ker_prodAddHom /-- The kernel of a paired homomorphism is the meet of the
kernels. -/]
theorem ker_prodMulHom [Mul M] [Mul N] [Mul N'] (f : M →ₙ* N) (g : M →ₙ* N') :
    ker (f.prod g) = ker f ⊓ ker g :=
  ext fun _ _ ↦ Prod.ext_iff

/-- The kernel of a paired monoid homomorphism is the meet of the kernels. -/
@[to_additive ker_prod /-- The kernel of a paired additive monoid homomorphism is the meet of
the kernels. -/]
theorem ker_prod [MulOneClass M] [MulOneClass N] [MulOneClass N'] (f : M →* N) (g : M →* N') :
    ker (f.prod g) = ker f ⊓ ker g :=
  ext fun _ _ ↦ Prod.ext_iff

end Con
