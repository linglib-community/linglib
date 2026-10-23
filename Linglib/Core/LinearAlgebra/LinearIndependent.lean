module

public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear maps prescribed on a linearly independent family

This file proves that a linearly independent family of vectors can be sent to any family of
values by a linear map: given `hv : LinearIndependent K v` and `w : ι → W`, there is a linear map
`f` with `f (v i) = w i` for every `i`. The map is built on the span of `v` by
`Module.Basis.constr` and extended to the whole space by `LinearMap.exists_extend`.

## Main results

* `LinearIndependent.exists_linearMap_apply_eq`: a linear map with prescribed values on a
  linearly independent family.
-/

@[expose] public section

variable {ι K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- A linear map may take any values on a linearly independent family. -/
theorem LinearIndependent.exists_linearMap_apply_eq {v : ι → V} (hv : LinearIndependent K v)
    (w : ι → W) : ∃ f : V →ₗ[K] W, ∀ i, f (v i) = w i := by
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr K w)
  refine ⟨f, fun i ↦ ?_⟩
  have h := LinearMap.congr_fun hf (Module.Basis.span hv i)
  rwa [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis,
    Module.Basis.span_apply] at h
