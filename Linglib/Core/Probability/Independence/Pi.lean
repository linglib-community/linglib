module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Probability.Independence.Basic

/-!
# Independence under a product measure

Under a product of probability measures, events that depend on disjoint sets of coordinates are
independent. `[UPSTREAM]` candidate for `Mathlib/Probability/Independence/Basic.lean`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)] {ν : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (ν i)]
  {S T : Finset ι} {A B : Set (∀ i, α i)}

/-- Under a product measure, events on disjoint sets of coordinates are independent. -/
theorem indepSet_pi_of_dependsOn (hA : DependsOn (· ∈ A) S) (hB : DependsOn (· ∈ B) T)
    (h : Disjoint S T) : IndepSet A B (Measure.pi ν) := by
  have hind := (iIndepFun_pi (μ := ν) (X := fun _ ↦ id) fun _ ↦ aemeasurable_id).indepFun_finset
    S T h fun _ ↦ measurable_pi_apply _
  have key {C : Set (∀ i, α i)} {U : Finset ι} (hC : DependsOn (· ∈ C) U) :
      C = (fun w (i : U) ↦ w i) ⁻¹' ((fun w (i : U) ↦ w i) '' C) := by
    ext w
    refine ⟨fun hw ↦ ⟨w, hw, rfl⟩, fun ⟨w', hw', heq⟩ ↦ ?_⟩
    have : (w' ∈ C) = (w ∈ C) := hC fun i hi ↦ congrFun heq ⟨i, hi⟩
    exact this ▸ hw'
  rw [key hA, key hB, indepSet_iff_measure_inter_eq_mul .of_discrete .of_discrete _]
  exact hind.measure_inter_preimage_eq_mul _ _ .of_discrete .of_discrete

end ProbabilityTheory
