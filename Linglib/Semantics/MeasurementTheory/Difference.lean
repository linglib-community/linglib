module

public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Basic.Real.Embedding
public import Linglib.Core.Algebra.Order.Archimedean.Hom
public import Linglib.Semantics.MeasurementTheory.Invariance

import Mathlib.Tactic.Linarith

/-!
# Difference measurement

Degrees whose differences can be added and compared, such as dates or temperatures, form a torsor of
an ordered group, with no distinguished origin. A [measure](##MeasurementTheory.IsDifferenceMeasure)
of them is a real-valued map under which one difference is at most another exactly when the measured
differences are. When the differences are Archimedean [there is
one](##MeasurementTheory.exists_isDifferenceMeasure), fixed by a unit and an origin. Two measures
[differ by a positive affine map](##MeasurementTheory.exists_mem_positiveAffine_comp_eq), and [a
positive affine map carries a measure to a measure](##MeasurementTheory.IsDifferenceMeasure.comp),
so the positive affine maps are the changes of scale of difference measurement. The measured
differences themselves [are
proportional](##MeasurementTheory.IsDifferenceMeasure.exists_pos_forall_sub_eq), so their ratios do
not depend on the measure.

## Implementation notes

The degrees are a torsor of an ordered additive group, where [krantz-1971] measure a set with a
weak order on its pairs satisfying sign reversal, weak monotonicity, solvability and an Archimedean
axiom.

## TODO

* The representation and uniqueness theorems for an algebraic-difference structure in that sense.

## References

* [krantz-1971]
-/

@[expose] public section

open Function

namespace MeasurementTheory

variable {V P : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [AddTorsor V P]

/-- A real-valued map measures the differences of a torsor when one difference is at most another
exactly when the measured differences are. -/
-- [krantz-1971] Theorem 4.2, p. 151
def IsDifferenceMeasure (φ : P → ℝ) : Prop :=
  ∀ a b c d : P, φ a - φ b ≤ φ c - φ d ↔ a -ᵥ b ≤ c -ᵥ d

namespace IsDifferenceMeasure

variable {φ ψ : P → ℝ}

omit [IsOrderedAddMonoid V] in
theorem sub_eq_sub (h : IsDifferenceMeasure φ) {a b c d : P} (e : a -ᵥ b = c -ᵥ d) :
    φ a - φ b = φ c - φ d :=
  le_antisymm ((h a b c d).2 e.le) ((h c d a b).2 e.ge)

/-- The additive measure of the differences that a difference measure induces. -/
noncomputable def toOrderAddMonoidHom (h : IsDifferenceMeasure φ) : V →+o ℝ where
  toFun v := φ (v +ᵥ Classical.arbitrary P) - φ (Classical.arbitrary P)
  map_zero' := by simp
  map_add' v w := by
    have := h.sub_eq_sub (a := v +ᵥ (w +ᵥ Classical.arbitrary P)) (b := w +ᵥ Classical.arbitrary P)
      (c := v +ᵥ Classical.arbitrary P) (d := Classical.arbitrary P) (by simp)
    rw [add_vadd]
    linarith
  monotone' v w hvw := (h _ _ _ _).2 (by simpa using hvw)

omit [IsOrderedAddMonoid V] in
theorem toOrderAddMonoidHom_vsub (h : IsDifferenceMeasure φ) (a b : P) :
    h.toOrderAddMonoidHom (a -ᵥ b) = φ a - φ b :=
  h.sub_eq_sub (by simp)

omit [IsOrderedAddMonoid V] in
theorem toOrderAddMonoidHom_injective (h : IsDifferenceMeasure φ) :
    Injective h.toOrderAddMonoidHom := by
  have key (v w : V) : h.toOrderAddMonoidHom v ≤ h.toOrderAddMonoidHom w ↔ v ≤ w :=
    (h _ _ _ _).trans (by simp)
  exact fun v w e ↦ le_antisymm ((key v w).1 e.le) ((key w v).1 e.ge)

/-- Under two measures of the same differences the measured differences are proportional. -/
theorem exists_pos_forall_sub_eq (hφ : IsDifferenceMeasure φ) (hψ : IsDifferenceMeasure ψ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b, ψ a - ψ b = c * (φ a - φ b) := by
  obtain ⟨c, hc, h⟩ := hφ.toOrderAddMonoidHom.exists_pos_forall_eq_mul hψ.toOrderAddMonoidHom
    hφ.toOrderAddMonoidHom_injective hψ.toOrderAddMonoidHom_injective
  exact ⟨c, hc, fun a b ↦ by
    rw [← toOrderAddMonoidHom_vsub hψ, ← toOrderAddMonoidHom_vsub hφ, h]⟩

omit [IsOrderedAddMonoid V] in
/-- A positive affine map carries a difference measure to a difference measure. -/
-- [krantz-1971] Theorem 4.2, p. 151
theorem comp (hφ : IsDifferenceMeasure φ) {u : ℝ ≃o ℝ}
    (hu : u ∈ (positiveAffine : Set (ℝ ≃o ℝ))) : IsDifferenceMeasure (u ∘ φ) := by
  obtain ⟨c, hc, b, hu⟩ := hu
  intro p q r s
  simp only [comp_apply, hu]
  rw [← hφ p q r s, add_sub_add_right_eq_sub, add_sub_add_right_eq_sub, ← mul_sub, ← mul_sub,
    mul_le_mul_iff_of_pos_left hc]

end IsDifferenceMeasure

/-- Two measures of the same differences differ by a positive affine map. -/
-- [krantz-1971] Theorem 4.2, p. 151
theorem exists_mem_positiveAffine_comp_eq {φ ψ : P → ℝ} (hφ : IsDifferenceMeasure φ)
    (hψ : IsDifferenceMeasure ψ) : ∃ u ∈ (positiveAffine : Set (ℝ ≃o ℝ)), ψ = u ∘ φ := by
  obtain ⟨c, hc, h⟩ := hφ.exists_pos_forall_sub_eq hψ
  let p := Classical.arbitrary P
  refine ⟨(OrderIso.mulLeft₀ c hc).trans (OrderIso.addRight (ψ p - c * φ p)),
    ⟨c, hc, ψ p - c * φ p, fun t ↦ by simp⟩, funext fun a ↦ ?_⟩
  have := h a p
  simp only [comp_apply, OrderIso.trans_apply, OrderIso.mulLeft₀_apply, OrderIso.addRight_apply]
  linarith

/-- A torsor of an Archimedean ordered group has a difference measure. -/
-- [krantz-1971] Theorem 4.2, p. 151
theorem exists_isDifferenceMeasure [Archimedean V] : ∃ φ : P → ℝ, IsDifferenceMeasure φ := by
  obtain ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective V
  refine ⟨fun a ↦ f (a -ᵥ Classical.arbitrary P), fun a b c d ↦ ?_⟩
  rw [← map_sub, ← map_sub, vsub_sub_vsub_cancel_right, vsub_sub_vsub_cancel_right]
  exact ((OrderHomClass.mono f).strictMono_of_injective hf).le_iff_le

end MeasurementTheory
