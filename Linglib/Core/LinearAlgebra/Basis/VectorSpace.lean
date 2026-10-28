module

public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear maps with prescribed values on a linearly independent family

`[UPSTREAM]` candidate for `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`. A linearly independent
family in a vector space can be sent to any family of values by a linear map, defined on the span
of the family by `Module.Basis.constr` and extended to the whole space by
`LinearMap.exists_extend`. Mathlib proves the case of a functional equal to `1` on the family,
`Module.exists_dual_forall_apply_eq_one`, which follows from this one.
-/

@[expose] public section

open Module

variable {ι K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- A linear map may take any values on a linearly independent family. -/
theorem LinearIndependent.exists_linearMap_forall_apply_eq {v : ι → V}
    (hv : LinearIndependent K v) (w : ι → W) : ∃ f : V →ₗ[K] W, ∀ i, f (v i) = w i := by
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Basis.span hv).constr ℕ w)
  refine ⟨f, fun i ↦ ?_⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Basis.coe_span_apply,
    Basis.constr_basis] using LinearMap.congr_fun hf (Basis.span hv i)
