/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Constructions.Projective
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
* `MeasureTheory.ext_of_map_fin`: finite measures on sequences with the same laws of the first
  `n` terms, for every `n`, are equal.
* `MeasureTheory.infinitePi_map_fin`: the first `n` terms of an independent and identically
  distributed sequence have the finite product law.
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

/-- Two finite measures on sequences are equal as soon as, for every `n`, they give the first `n`
terms the same law. -/
theorem ext_of_map_fin {E : Type*} [MeasurableSpace E] {μ ν : Measure (ℕ → E)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (fun x (i : Fin n) ↦ x i) = ν.map (fun x (i : Fin n) ↦ x i)) : μ = ν := by
  refine IsProjectiveLimit.unique (P := fun I : Finset ℕ ↦ ν.map I.restrict) (fun I ↦ ?_)
    (fun I ↦ rfl)
  have hI (i : I) : (i : ℕ) < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)
  have hg : Measurable fun (y : Fin (I.sup id + 1) → E) (i : I) ↦ y ⟨i, hI i⟩ := by fun_prop
  have hm : Measurable fun (x : ℕ → E) (i : Fin (I.sup id + 1)) ↦ x i := by fun_prop
  have e : I.restrict = (fun (y : Fin (I.sup id + 1) → E) (i : I) ↦ y ⟨i, hI i⟩) ∘
      fun (x : ℕ → E) (i : Fin (I.sup id + 1)) ↦ x i := rfl
  change μ.map I.restrict = ν.map I.restrict
  rw [e, ← Measure.map_map hg hm, ← Measure.map_map hg hm, h]

/-- The first `n` terms of an independent and identically distributed sequence are independent
and identically distributed. -/
theorem infinitePi_map_fin {E : Type*} [MeasurableSpace E] (m : Measure E)
    [IsProbabilityMeasure m] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ m).map (fun x (i : Fin n) ↦ x i) =
      Measure.pi fun _ : Fin n ↦ m := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  let t : ℕ → Set E := fun i ↦ if h : i < n then s ⟨i, h⟩ else Set.univ
  have ht (i : ℕ) : MeasurableSet (t i) := by
    by_cases h : i < n <;> simp [t, h, hs]
  have hpre : (fun x (i : Fin n) ↦ x i) ⁻¹' Set.univ.pi s = (Finset.range n : Set ℕ).pi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio]
    exact ⟨fun hx i hi ↦ by simpa [t, hi] using hx ⟨i, hi⟩,
      fun hx i ↦ by simpa [t, i.isLt] using hx i i.isLt⟩
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs), hpre, Measure.infinitePi_pi _ fun i _ ↦ ht i,
    ← Fin.prod_univ_eq_prod_range (fun i ↦ m (t i))]
  exact Finset.prod_congr rfl fun i _ ↦ by simp [t, i.isLt]

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
