/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Infix
public import Linglib.Core.MeasureTheory.Integral.Layercake
public import Linglib.Core.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures on lists

Lists carry the discrete σ-algebra. `Measure.listProd` is the law of a list of independent draws,
one from each measure in a list: the `List`-indexed product measure, built from the binary product
as mathlib builds `MeasureTheory.Measure.tprod`. It [multiplies on the lists with head in one set
and tail in another](##MeasureTheory.Measure.listProd_cons_image2) and is [ω-Scott-continuous in
each factor](##MeasureTheory.Measure.ωScottContinuous_listProd).

Under a measure on lists the cylinders `x.cylinder`, the lists beginning with `x`, are counted two
ways: [the lists of length at least `n` are partitioned by their prefix of length
`n`](##MeasureTheory.Measure.tsum_measure_cylinder_length), and a list has one prefix more than its
length, so [the total measure of the cylinders is the integral of the length plus
one](##MeasureTheory.Measure.tsum_measure_cylinder).

## Implementation notes

The discrete σ-algebra is registered globally as the library's convention. It is the right one on
lists over a countable type with measurable singletons, the case of derivation trees and branching
processes: there `List.cons` is measurable, and the formulas for `Measure.listProd` are stated
under those hypotheses.

## TODO

A σ-algebra on `List α` that makes `List.cons` measurable for every `α`, and is discrete when `α`
is countable and discrete, would make `Measure.listProd` the product measure in general.
-/

@[expose] public section

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

instance List.instMeasurableSpace {α : Type*} : MeasurableSpace (List α) := ⊤

namespace MeasureTheory.Measure

/-! ### Cylinders -/

section Cylinder

variable {α : Type*} [Countable α] (μ : Measure (List α))

/-- The lists of length at least `n` are partitioned by their prefix of length `n`. -/
theorem tsum_measure_cylinder_length (n : ℕ) :
    ∑' x : {x : List α // x.length = n}, μ x.1.cylinder = μ {y | n ≤ y.length} := by
  rw [show {y : List α | n ≤ y.length} = List.take n ⁻¹' {x | x.length = n} by ext; simp,
    ← tsum_measure_preimage_singleton (Set.to_countable _) fun _ _ ↦ .of_discrete]
  exact tsum_congr fun x ↦ by rw [← x.1.take_preimage_singleton, x.2]

/-- The total measure of the cylinders is the integral of the number of prefixes, the length plus
one. -/
theorem tsum_measure_cylinder :
    ∑' x : List α, μ x.cylinder = ∫⁻ y, (y.length : ℝ≥0∞) + 1 ∂μ := by
  simp_rw [← Nat.cast_add_one]
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma',
    lintegral_natCast_eq_tsum_measure_lt (f := fun y : List α ↦ y.length + 1) .of_discrete]
  exact tsum_congr fun n ↦ (tsum_measure_cylinder_length μ n).trans (by simp)

end Cylinder

/-! ### Products of lists of measures -/

section ListProd

variable {α : Type*} [MeasurableSpace α]

/-- The law of a list of independent draws, one from each measure in the list. -/
noncomputable def listProd : List (Measure α) → Measure (List α)
  | [] => dirac []
  | μ :: μs => (μ.prod (listProd μs)).map (Function.uncurry List.cons)

@[simp] theorem listProd_nil : listProd ([] : List (Measure α)) = dirac [] := rfl

theorem listProd_cons (μ : Measure α) (μs : List (Measure α)) :
    listProd (μ :: μs) = (μ.prod (listProd μs)).map (Function.uncurry List.cons) := rfl

@[simp] theorem listProd_nil_singleton_cons (x : α) (xs : List α) :
    listProd ([] : List (Measure α)) {x :: xs} = 0 := by
  rw [listProd_nil, dirac_apply' _ .of_discrete]
  simp

theorem isProbabilityMeasure_listProd {μs : List (Measure α)}
    (h : ∀ μ ∈ μs, IsProbabilityMeasure μ) : IsProbabilityMeasure (listProd μs) := by
  induction μs with
  | nil => rw [listProd_nil]; infer_instance
  | cons μ μs ih =>
    have := ih fun ν hν ↦ h ν (List.mem_cons_of_mem _ hν)
    have := h μ (List.mem_cons_self ..)
    rw [listProd_cons]
    infer_instance

variable [Countable α] [MeasurableSingletonClass α]

/-- The total mass of a product of a list of measures is the product of their total masses. -/
theorem listProd_univ (μs : List (Measure α)) :
    listProd μs Set.univ = (μs.map (· Set.univ)).prod := by
  induction μs with
  | nil => simp
  | cons μ μs ih =>
    rw [listProd_cons, map_apply .of_discrete .univ, Set.preimage_univ, ← Set.univ_prod_univ,
      prod_prod, ih, List.map_cons, List.prod_cons]

theorem listProd_univ_le_one {μs : List (Measure α)} (h : ∀ μ ∈ μs, μ Set.univ ≤ 1) :
    listProd μs Set.univ ≤ 1 := by
  rw [listProd_univ]
  refine (List.prod_le_pow_length _ 1 fun x hx ↦ ?_).trans_eq (one_pow _)
  obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hx
  exact h μ hμ

/-- The product measure of the lists with head in `s` and tail in `t`. -/
theorem listProd_cons_image2 (μ : Measure α) (μs : List (Measure α)) (s : Set α)
    (t : Set (List α)) :
    listProd (μ :: μs) (Set.image2 List.cons s t) = μ s * listProd μs t := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete, ← prod_prod]
  congr 1
  ext ⟨_, _⟩
  simp

@[simp] theorem listProd_cons_singleton_cons (μ : Measure α) (μs : List (Measure α)) (x : α)
    (xs : List α) : listProd (μ :: μs) {x :: xs} = μ {x} * listProd μs {xs} := by
  rw [← listProd_cons_image2, Set.image2_singleton]

@[simp] theorem listProd_cons_singleton_nil (μ : Measure α) (μs : List (Measure α)) :
    listProd (μ :: μs) {[]} = 0 := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete]
  convert measure_empty (μ := μ.prod (listProd μs))
  ext ⟨_, _⟩
  simp

variable {γ : Type*} [OmegaCompletePartialOrder γ]

theorem ωScottContinuous_listProd {ι : Type*} {F : ι → γ → Measure α} {l : List ι}
    (hF : ∀ i ∈ l, ωScottContinuous (F i)) :
    ωScottContinuous fun x ↦ listProd (l.map fun i ↦ F i x) := by
  induction l with
  | nil => exact ωScottContinuous.const
  | cons i l ih =>
    simp only [List.map_cons, listProd_cons]
    exact ωScottContinuous_map (ωScottContinuous_prod (hF i (List.mem_cons_self ..))
      (ih fun j hj ↦ hF j (List.mem_cons_of_mem _ hj))) .of_discrete

end ListProd

end MeasureTheory.Measure
