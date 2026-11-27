/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Group.Action
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Probability.IdentDistribIndep
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Exchangeable families of random variables

A family of random variables `X : ι → Ω → E` is *exchangeable* if its joint law is unchanged by
permuting the indices: for every permutation `σ` of `ι`, the families `fun i ↦ X (σ i)` and `X`
have the same law on `ι → E`. Equivalently, the joint law is invariant under the action of the
permutations of `ι` on `ι → E` by precomposition.

## Main definitions

* `ProbabilityTheory.Exchangeable X μ`: the family `X` is exchangeable under `μ`.

## Main statements

* `ProbabilityTheory.exchangeable_iff_smulInvariantMeasure_map`: a family is exchangeable if and
  only if its joint law is invariant under permuting the coordinates.
* `ProbabilityTheory.Exchangeable.identDistrib`: the members of an exchangeable family are
  identically distributed.
* `ProbabilityTheory.Exchangeable.comp`: applying one measurable function to every member of an
  exchangeable family gives an exchangeable family.
* `ProbabilityTheory.Exchangeable.comp_embedding`: a subfamily of an exchangeable family is
  exchangeable.
* `ProbabilityTheory.iIndepFun.exchangeable`: independent and identically distributed random
  variables are exchangeable.

## Implementation notes

The definition asks for invariance under all permutations of `ι`. For infinite `ι` the usual
definition asks only for the permutations that move finitely many indices. The two agree for a
finite measure, since a measurable cylinder constrains finitely many indices and a permutation
agrees on finitely many indices with one that moves finitely many.

## TODO

* The equivalence with invariance under the permutations that move finitely many indices.
* De Finetti's theorem: an exchangeable sequence in a standard Borel space is a mixture of
  independent and identically distributed sequences.

## Tags

exchangeable, exchangeability, de Finetti
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω ι κ E F : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure Ω} {X : ι → Ω → E}

/-- A family of random variables `X : ι → Ω → E` is *exchangeable* if its joint law is unchanged
by permuting the indices. The joint law only makes sense when `fun ω i ↦ X i ω` is almost
everywhere measurable, so this is part of the definition. -/
structure Exchangeable (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) : Prop where
  aemeasurable : AEMeasurable (fun ω i ↦ X i ω) μ
  map_eq (σ : Equiv.Perm ι) : μ.map (fun ω i ↦ X (σ i) ω) = μ.map fun ω i ↦ X i ω

namespace Exchangeable

/-- An exchangeable family has the same joint law as each of its reindexings by a permutation. -/
theorem identDistrib_perm (h : Exchangeable X μ) (σ : Equiv.Perm ι) :
    IdentDistrib (fun ω i ↦ X (σ i) ω) (fun ω i ↦ X i ω) μ μ where
  aemeasurable_fst :=
    (Measurable.of_eval fun i ↦ measurable_pi_apply (σ i)).comp_aemeasurable h.aemeasurable
  aemeasurable_snd := h.aemeasurable
  map_eq := h.map_eq σ

/-- The members of an exchangeable family are identically distributed. -/
theorem identDistrib (h : Exchangeable X μ) (i j : ι) : IdentDistrib (X i) (X j) μ μ := by
  classical
  simpa [Function.comp_def] using (h.identDistrib_perm (Equiv.swap i j)).comp (measurable_pi_apply j)

/-- Applying one measurable function to every member of an exchangeable family gives an
exchangeable family. -/
theorem comp (h : Exchangeable X μ) {g : E → F} (hg : Measurable g) :
    Exchangeable (fun i ↦ g ∘ X i) μ :=
  have hG : Measurable fun (x : ι → E) i ↦ g (x i) := by fun_prop
  ⟨hG.comp_aemeasurable h.aemeasurable, fun σ ↦ ((h.identDistrib_perm σ).comp hG).map_eq⟩

/-- A subfamily of an exchangeable family is exchangeable. -/
theorem comp_embedding (h : Exchangeable X μ) (f : κ ↪ ι) : Exchangeable (X ∘ f) μ where
  aemeasurable :=
    (Measurable.of_eval fun k ↦ measurable_pi_apply (f k)).comp_aemeasurable h.aemeasurable
  map_eq τ := by
    have := ((h.identDistrib_perm (τ.viaEmbedding f)).comp (u := fun x k ↦ x (f k))
      (Measurable.of_eval fun k ↦ measurable_pi_apply (f k))).map_eq
    simpa [Function.comp_def, Equiv.Perm.viaEmbedding_apply] using this

end Exchangeable

/-- A family is exchangeable if and only if its joint law is invariant under permuting the
coordinates. -/
theorem exchangeable_iff_smulInvariantMeasure_map (hX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    Exchangeable X μ ↔
      SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → E) (μ.map fun ω i ↦ X i ω) := by
  have key (σ : Equiv.Perm ι) : μ.map (fun ω i ↦ X (σ i) ω) =
      (μ.map fun ω i ↦ X i ω).map (DomMulAct.mk σ • ·) :=
    (AEMeasurable.map_map_of_aemeasurable
      (measurable_const_smul (DomMulAct.mk σ)).aemeasurable hX).symm
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hX, fun σ ↦ (key σ).trans (MeasureTheory.map_smul _ _)⟩⟩
  exact ((smulInvariantMeasure_tfae (Equiv.Perm ι)ᵈᵐᵃ _).out 1 6).2 fun c ↦
    (key (DomMulAct.mk.symm c)).symm.trans (h.map_eq _)

/-- The coordinates on `ι → E` are exchangeable under a measure if and only if the measure is
invariant under permuting the coordinates. -/
theorem exchangeable_eval_iff {μ : Measure (ι → E)} :
    Exchangeable (fun i (x : ι → E) ↦ x i) μ ↔ SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → E) μ := by
  simpa using exchangeable_iff_smulInvariantMeasure_map (X := fun i (x : ι → E) ↦ x i)
    (μ := μ) aemeasurable_id

/-- Independent and identically distributed random variables are exchangeable. -/
theorem iIndepFun.exchangeable [Countable ι] (hX : iIndepFun X μ)
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) : Exchangeable X μ where
  aemeasurable := .of_eval fun i ↦ (hid i i).aemeasurable_fst
  map_eq σ := (IdentDistrib.pi (fun i ↦ hid (σ i) i) (hX.precomp σ.injective) hX).map_eq

end ProbabilityTheory
