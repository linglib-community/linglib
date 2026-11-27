/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.ProductMeasure

/-!
# Infinite products of one probability measure

The infinite product `Measure.infinitePi fun _ ↦ ν` of copies of one probability measure is the
law of a sequence of independent random variables with law `ν`. It is invariant under permuting
the coordinates, and it depends measurably on `ν`.

## Main results

* `MeasureTheory.Measure.infinitePi.smulInvariantMeasure_domMulAct`: invariance under
  permutations of the index type.
* `MeasureTheory.measurable_infinitePi_const`: measurability in the factor.
* `ProbabilityTheory.Kernel.iid ι E`: the kernel sending a probability measure `m` on `E` to the
  law of an independent family of random variables with law `m`.

`[UPSTREAM]` candidates for `Mathlib/Probability/ProductMeasure.lean`.
-/

public section

namespace MeasureTheory

/-- An infinite product of copies of one probability measure is invariant under permuting the
coordinates. -/
instance Measure.infinitePi.smulInvariantMeasure_domMulAct {ι E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → E) (Measure.infinitePi fun _ : ι ↦ ν) := by
  refine ⟨fun c s hs ↦ ?_⟩
  have hc : (fun x : ι → E ↦ c • x) =
      MeasurableEquiv.piCongrLeft (fun _ ↦ E) (DomMulAct.mk.symm c).symm := by
    ext x i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft', DomMulAct.smul_apply]
  rw [hc, ← Measure.map_apply (MeasurableEquiv.measurable _) hs]
  exact congrArg (· s) (Measure.infinitePi_map_piCongrLeft (fun _ : ι ↦ ν) _)

/-- The law of an independent and identically distributed family depends measurably on the law of
its terms. -/
theorem measurable_infinitePi_const {E : Type*} [MeasurableSpace E] (ι : Type*) :
    Measurable fun m : ProbabilityMeasure E ↦ Measure.infinitePi fun _ : ι ↦ (m : Measure E) := by
  have hpi := isPiSystem_squareCylinders (α := fun _ : ι ↦ E)
    (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) fun _ ↦ MeasurableSet.univ
  refine .measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_squareCylinders.symm hpi ?_
  rintro _ ⟨s, t, ht, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
  simp_rw [Measure.infinitePi_pi _ fun i _ ↦ ht i]
  exact Finset.measurable_prod _ fun i _ ↦
    (Measure.measurable_coe (ht i)).comp measurable_subtype_coe

end MeasureTheory

namespace ProbabilityTheory

open MeasureTheory

/-- The kernel sending a probability measure `m` to the law `m^∞` of an independent family of
random variables with law `m`. -/
@[expose] noncomputable def Kernel.iid (ι E : Type*) [MeasurableSpace E] :
    Kernel (ProbabilityMeasure E) (ι → E) where
  toFun m := Measure.infinitePi fun _ : ι ↦ (m : Measure E)
  measurable' := measurable_infinitePi_const ι

@[simp]
theorem Kernel.iid_apply {ι E : Type*} [MeasurableSpace E] (m : ProbabilityMeasure E) :
    Kernel.iid ι E m = Measure.infinitePi fun _ : ι ↦ (m : Measure E) := rfl

instance {ι E : Type*} [MeasurableSpace E] : IsMarkovKernel (Kernel.iid ι E) :=
  ⟨fun m ↦ by rw [Kernel.iid_apply]; infer_instance⟩

end ProbabilityTheory
