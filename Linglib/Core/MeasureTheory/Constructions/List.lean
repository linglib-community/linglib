/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Integral.Layercake
public import Linglib.Core.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measures on lists

Lists carry the discrete σ-algebra, so every function out of a list type is measurable and, over
a countable type, every measure on lists is s-finite. `Measure.listProd` is the law of a list of
independent draws, one from each measure in a list of measures: the `List`-indexed product
measure, built from the binary product.

The prefix sets `{y | x <+: y}` of a measure on lists are counted two ways. The lists of length
at least `n` are partitioned by their prefix of length `n`, and a list has one prefix more than
its length, so the total measure of the prefix sets is the integral of the length plus one.

## Main definitions

* `MeasureTheory.Measure.listProd`: the product of a list of measures.

## Main results

* `MeasureTheory.Measure.listProd_cons_singleton_cons`: the product measure of a singleton list is
  the product of the singleton measures.
* `MeasureTheory.Measure.ωScottContinuous_listProd`: the product is ω-Scott-continuous in each
  factor.
* `MeasureTheory.Measure.tsum_measure_setOf_prefix_length`,
  `MeasureTheory.Measure.tsum_measure_setOf_prefix`: the prefix sets counted by length, and in
  total.

## Implementation notes

The discrete σ-algebra is the only reasonable choice on lists over a countable discrete type,
which is the case of interest for derivation trees and branching processes; it is registered
globally here as the library's convention.
-/

@[expose] public section

open MeasureTheory OmegaCompletePartialOrder
open scoped ENNReal

instance {α : Type*} : MeasurableSpace (List α) := ⊤

namespace MeasureTheory.Measure

/-! ### Prefix sets -/

section Prefixes

variable {α : Type*} [Countable α] (μ : Measure (List α))

/-- The lists of length at least `n` are partitioned by their prefix of length `n`. -/
theorem tsum_measure_setOf_prefix_length (n : ℕ) :
    ∑' x : {x : List α // x.length = n}, μ {y | x.1 <+: y} = μ {y | n ≤ y.length} := by
  have h (x : {x : List α // x.length = n}) : {y | x.1 <+: y} = List.take n ⁻¹' {x.1} := by
    ext y
    simp [List.prefix_iff_eq_take, x.2, eq_comm]
  have hs : {y : List α | n ≤ y.length} = List.take n ⁻¹' {x | x.length = n} := by
    ext y
    simp
  simp_rw [h]
  rw [hs, ← tsum_measure_preimage_singleton (Set.to_countable _) fun _ _ ↦ .of_discrete]
  rfl

/-- The total measure of the prefix sets is the integral of the number of prefixes, the length
plus one. -/
theorem tsum_measure_setOf_prefix :
    ∑' x, μ {y | x <+: y} = ∫⁻ y, (y.length : ℝ≥0∞) + 1 ∂μ := by
  simp_rw [← Nat.cast_add_one]
  rw [← (Equiv.sigmaFiberEquiv List.length).tsum_eq, ENNReal.tsum_sigma',
    lintegral_natCast_eq_tsum_measure_lt (f := fun y : List α ↦ y.length + 1) .of_discrete]
  show ∑' n, ∑' x : {x : List α // x.length = n}, μ {y | x.1 <+: y} = _
  exact tsum_congr fun n ↦ (tsum_measure_setOf_prefix_length μ n).trans (by simp)

end Prefixes

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
    have := ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    have := h μ (List.mem_cons_self ..)
    rw [listProd_cons]
    infer_instance

variable [Countable α] [MeasurableSingletonClass α]

theorem listProd_univ_le_one {μs : List (Measure α)} (h : ∀ μ ∈ μs, μ Set.univ ≤ 1) :
    listProd μs Set.univ ≤ 1 := by
  induction μs with
  | nil => simp
  | cons μ μs ih =>
    rw [listProd_cons, map_apply .of_discrete .univ, Set.preimage_univ, ← Set.univ_prod_univ,
      prod_prod]
    exact mul_le_one' (h μ (List.mem_cons_self ..)) (ih fun ν hν => h ν (List.mem_cons_of_mem _ hν))

@[simp] theorem listProd_cons_singleton_nil (μ : Measure α) (μs : List (Measure α)) :
    listProd (μ :: μs) {[]} = 0 := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete]
  convert measure_empty (μ := μ.prod (listProd μs))
  ext ⟨_, _⟩
  simp

@[simp] theorem listProd_cons_singleton_cons (μ : Measure α) (μs : List (Measure α)) (x : α)
    (xs : List α) : listProd (μ :: μs) {x :: xs} = μ {x} * listProd μs {xs} := by
  rw [listProd_cons, map_apply .of_discrete .of_discrete, ← prod_prod]
  congr 1
  ext ⟨_, _⟩
  simp

variable {γ : Type*} [OmegaCompletePartialOrder γ]

theorem ωScottContinuous_listProd {ι : Type*} {F : ι → γ → Measure α} {l : List ι}
    (hF : ∀ i ∈ l, ωScottContinuous (F i)) :
    ωScottContinuous fun x => listProd (l.map fun i => F i x) := by
  induction l with
  | nil => exact ωScottContinuous.const
  | cons i l ih =>
    simp only [List.map_cons, listProd_cons]
    exact ωScottContinuous_map (ωScottContinuous_prod (hF i (List.mem_cons_self ..))
      (ih fun j hj => hF j (List.mem_cons_of_mem _ hj))) .of_discrete

end ListProd

end MeasureTheory.Measure
