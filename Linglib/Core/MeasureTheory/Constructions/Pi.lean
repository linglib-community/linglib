/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Splitting one coordinate off a finite product measure

Mathlib splits a coordinate off `Measure.pi` only for index type `Fin (n + 1)`
(`measurePreserving_piFinSuccAbove`). This file gives the same tower for `Equiv.piSplitAt`, which
works over any finite index type: the measurable equivalence and the statement that it carries
`Measure.pi μ` to `(μ i).prod (Measure.pi fun j : {j // j ≠ i} ↦ μ j)`. With `Measure.prod_apply`
and `Measure.pi_pi` this computes probabilities that tie the other coordinates to the `i`-th.

## Main definitions

* `MeasurableEquiv.piSplitAt`: the measurable version of `Equiv.piSplitAt`.

## Main results

* `MeasureTheory.measurePreserving_piSplitAt`: splitting a coordinate preserves the product measure.
* `MeasureTheory.Measure.pi_setOf_apply_eq_apply`: two coordinates are almost surely distinct when
  one of the factors has no atoms.

## Implementation notes

`[UPSTREAM]` candidates: the equivalence for `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`,
beside `MeasurableEquiv.piFinSuccAbove`, and the two theorems for
`Mathlib/MeasureTheory/Constructions/Pi.lean`.
-/

@[expose] public section

open MeasureTheory Set

universe u
variable {ι : Type*} [DecidableEq ι] {α : ι → Type u}

namespace MeasurableEquiv

/-- Measurable version of `Equiv.piSplitAt`. -/
@[simps! -fullyApplied]
def piSplitAt (α : ι → Type*) [∀ i, MeasurableSpace (α i)] (i : ι) :
    (∀ j, α j) ≃ᵐ α i × ∀ j : {j // j ≠ i}, α j where
  toEquiv := Equiv.piSplitAt i α
  measurable_toFun := (measurable_pi_apply i).prodMk <| measurable_pi_iff.2 fun _ ↦
    measurable_pi_apply _
  measurable_invFun := measurable_pi_iff.2 fun j ↦ by
    by_cases h : j = i
    · subst h; simpa using measurable_fst
    · simpa [h] using! (measurable_pi_apply (⟨j, h⟩ : {j // j ≠ i})).comp measurable_snd

end MeasurableEquiv

namespace MeasureTheory

variable [Fintype ι]

theorem measurePreserving_piSplitAt {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (i : ι) :
    MeasurePreserving (MeasurableEquiv.piSplitAt α i) (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j : {j // j ≠ i} ↦ μ j) := by
  set e := (MeasurableEquiv.piSplitAt α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (Measure.pi_eq fun s _ ↦ ?_).symm⟩
  rw [e.map_apply, Fintype.prod_eq_mul_prod_subtype_ne _ i, ← Measure.pi_pi, ← Measure.prod_prod]
  congr 1 with ⟨x, f⟩
  simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod, Subtype.forall]
  refine ⟨fun h ↦ ⟨by simpa [e] using h i, fun j hj ↦ by simpa [e, hj] using h j⟩, fun h j ↦ ?_⟩
  by_cases hj : j = i
  · subst hj; simpa [e] using h.1
  · simpa [e, hj] using h.2 j hj

theorem volume_preserving_piSplitAt (α : ι → Type u) [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))] (i : ι) :
    MeasurePreserving (MeasurableEquiv.piSplitAt α i) :=
  measurePreserving_piSplitAt (fun _ ↦ volume) i

end MeasureTheory

namespace MeasureTheory.Measure

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [MeasurableSpace X]
  [MeasurableEq X] (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]

theorem pi_setOf_apply_eq_apply {j k : ι} (hjk : j ≠ k) [NullSingletonClass (μ j)] :
    Measure.pi μ {x | x j = x k} = 0 := by
  have hS : {x : ι → X | x j = x k} = MeasurableEquiv.piSplitAt (fun _ ↦ X) k ⁻¹'
      {p | p.2 ⟨j, hjk⟩ = p.1} := by ext; simp
  rw [hS, (measurePreserving_piSplitAt μ k).measure_preimage_equiv]
  refine measure_prod_null_of_ae_null ?_ (.of_forall fun a ↦ ?_)
  · have h : Measurable fun p : X × ({l // l ≠ k} → X) ↦ (p.2 ⟨j, hjk⟩, p.1) := by fun_prop
    exact h measurableSet_diagonal
  · exact pi_eval_preimage_null (fun l : {l // l ≠ k} ↦ μ l) (i := ⟨j, hjk⟩)
      (measure_singleton a)

end MeasureTheory.Measure
