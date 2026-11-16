module

public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Linglib.Core.Algebra.Order.Archimedean.Hom
public import Linglib.Semantics.MeasurementTheory.Invariance

/-!
# Extensive measurement

Quantities that can be added and compared, such as lengths with their differences, form an ordered
group, and a measure of them is an additive, order-preserving, injective map into the reals. An
Archimedean ordered group has one (`Archimedean.exists_orderAddMonoidHom_real_injective`, Hölder's
theorem), which fixes a unit. Two measures [differ by a
similarity](##MeasurementTheory.exists_mem_similarity_comp_eq), and [a similarity carries a
measure to a measure](##MeasurementTheory.exists_orderAddMonoidHom_eq_comp), so the similarities
are the changes of scale of extensive measurement.

## Implementation notes

The quantities are an ordered additive group, where [krantz-1971] measure a weakly ordered set with
a concatenation that is associative only up to equivalence and has no inverses.

## TODO

* The representation and uniqueness theorems for a closed extensive structure in that sense, by way
  of its group of differences.

## References

* [krantz-1971]
-/

@[expose] public section

open Function

namespace MeasurementTheory

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- Two additive measures of an ordered group differ by a similarity. -/
-- [krantz-1971] Theorem 3.1, p. 74
theorem exists_mem_similarity_comp_eq (f g : M →+o ℝ) (hf : Injective f) (hg : Injective g) :
    ∃ u ∈ (similarity : Set (ℝ ≃o ℝ)), ⇑g = u ∘ f := by
  obtain ⟨c, hc, h⟩ := f.exists_pos_forall_eq_mul g hf hg
  exact ⟨OrderIso.mulLeft₀ c hc, ⟨c, hc, fun t ↦ by simp⟩, funext fun x ↦ by simp [h]⟩

omit [IsOrderedAddMonoid M] in
/-- A similarity carries an additive measure of an ordered group to an additive measure. -/
-- [krantz-1971] Theorem 3.1, p. 74
theorem exists_orderAddMonoidHom_eq_comp (f : M →+o ℝ) (hf : Injective f) {u : ℝ ≃o ℝ}
    (hu : u ∈ (similarity : Set (ℝ ≃o ℝ))) : ∃ g : M →+o ℝ, Injective g ∧ ⇑g = u ∘ f := by
  obtain ⟨c, hc, hu⟩ := hu
  refine ⟨⟨(AddMonoidHom.mulLeft c).comp (f : M →+ ℝ), fun x y h ↦
    mul_le_mul_of_nonneg_left (OrderHomClass.mono f h) hc.le⟩,
    fun x y h ↦ hf (mul_left_cancel₀ hc.ne' h), funext fun x ↦ (hu (f x)).symm⟩

end MeasurementTheory
