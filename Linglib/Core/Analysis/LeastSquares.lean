module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Least-squares solutions

`IsLeastSquares A b x` says `x` minimises the residual norm `‖b − A y‖` over the domain of a
linear map `A` between real inner product spaces. Mathlib characterises the minimisers of a
continuous linear map by its adjoint
(`ContinuousLinearMap.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero`); in finite
dimension every linear map is continuous, and this file packages the resulting API: the normal
equations in adjoint and inner-product form, existence by orthogonal projection, uniqueness of
fitted values, and the solution coset.

`[UPSTREAM]` candidate; generalises from `ℝ` to `RCLike 𝕜`.

## Main declarations

* `IsLeastSquares A b x`: `x` minimises `‖b − A y‖`.
* `isLeastSquares_iff_adjoint_eq_zero`, `isLeastSquares_iff_inner_eq_zero`: the **normal
  equations** — the adjoint kills the residual, equivalently the residual is orthogonal to the
  range of `A`.
* `exists_isLeastSquares`, `isLeastSquares_of_map_eq`: solutions exist, and an interpolating
  point is one.
* `IsLeastSquares.map_eq`, `IsLeastSquares.iff_map_eq`: fitted values are unique, and the
  solutions are exactly the preimages of the fitted value.
-/

@[expose] public section

namespace Core

open RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (A : E →ₗ[ℝ] F) (b : F)

/-- `x` is a **least-squares solution** of `A y ≈ b` if it minimises the residual norm
`‖b − A y‖`. -/
def IsLeastSquares (x : E) : Prop := IsMinOn (fun y => ‖b - A y‖) Set.univ x

variable {A b} {x x' : E}

theorem isLeastSquares_of_map_eq (h : A x = b) : IsLeastSquares A b x :=
  isMinOn_univ_iff.mpr fun y => by simp [h]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem isLeastSquares_iff_adjoint_eq_zero :
    IsLeastSquares A b x ↔ LinearMap.adjoint A (b - A x) = 0 := by
  have := FiniteDimensional.complete ℝ E
  have := FiniteDimensional.complete ℝ F
  rw [IsLeastSquares, isMinOn_univ_iff, LinearMap.adjoint_eq_toCLM_adjoint]
  simpa using
    (LinearMap.toContinuousLinearMap A).forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero b x

theorem isLeastSquares_iff_inner_eq_zero :
    IsLeastSquares A b x ↔ ∀ y, ⟪b - A x, A y⟫ = 0 := by
  rw [isLeastSquares_iff_adjoint_eq_zero]
  refine ⟨fun h y => ?_, fun h => ext_inner_right ℝ fun y => ?_⟩
  · rw [← LinearMap.adjoint_inner_left, h, inner_zero_left]
  · rw [LinearMap.adjoint_inner_left, h, inner_zero_left]

theorem exists_isLeastSquares : ∃ x, IsLeastSquares A b x := by
  have : CompleteSpace (LinearMap.range A) := FiniteDimensional.complete ℝ _
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp ((LinearMap.range A).starProjection_apply_mem b)
  exact ⟨x, isLeastSquares_iff_inner_eq_zero.mpr fun y => hx ▸
    Submodule.starProjection_inner_eq_zero b (A y) (LinearMap.mem_range_self A y)⟩

theorem IsLeastSquares.map_eq (hx : IsLeastSquares A b x) (hx' : IsLeastSquares A b x') :
    A x = A x' := by
  rw [isLeastSquares_iff_adjoint_eq_zero] at hx hx'
  have h : LinearMap.adjoint A (A x - A x') = 0 := by
    rw [show A x - A x' = (b - A x') - (b - A x) by abel, map_sub, hx, hx', sub_zero]
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
  nth_rewrite 1 [← map_sub]
  rw [← LinearMap.adjoint_inner_right, h, inner_zero_right]

theorem IsLeastSquares.iff_map_eq (hx : IsLeastSquares A b x) :
    IsLeastSquares A b x' ↔ A x' = A x :=
  ⟨fun hx' => hx'.map_eq hx, fun h => isMinOn_univ_iff.mpr fun y => h ▸ isMinOn_univ_iff.mp hx y⟩

theorem IsLeastSquares.eq_of_injective (hA : Function.Injective A) (hx : IsLeastSquares A b x)
    (hx' : IsLeastSquares A b x') : x = x' :=
  hA (hx.map_eq hx')

end Core
