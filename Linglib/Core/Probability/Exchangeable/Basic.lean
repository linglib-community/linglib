/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.GroupTheory.Perm.Finite
public import Linglib.Core.MeasureTheory.Group.Action
public import Linglib.Core.Probability.ProductMeasure
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.MeasureTheory.Constructions.Projective
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
* `ProbabilityTheory.Exchangeable.of_finite_support`: under a finite measure, it is enough to
  check the permutations that move finitely many indices.
* `ProbabilityTheory.Exchangeable.map_precomp_eq`: the joint law is unchanged by reindexing along
  an injective map.
* `ProbabilityTheory.Exchangeable.identDistrib`: the members of an exchangeable family are
  identically distributed.
* `ProbabilityTheory.iIndepFun.exchangeable`: independent and identically distributed random
  variables are exchangeable.
* `ProbabilityTheory.exchangeable_of_map_eq_bind`: a mixture of laws of independent and
  identically distributed sequences is exchangeable.

## Implementation notes

The definition asks for invariance under all permutations of `ι`, which is the statement that
the joint law is an invariant measure. For infinite `ι` the usual definition asks only for the
permutations that move finitely many indices; under a finite measure the two agree.

## Tags

exchangeable, exchangeability
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section Exchangeable

variable {Ω ι ι' E F : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure Ω} {X Y : ι → Ω → E}

/-- A family of random variables `X : ι → Ω → E` is *exchangeable* if its joint law is unchanged
by permuting the indices. -/
structure Exchangeable (X : ι → Ω → E) (μ : Measure Ω := by volume_tac) : Prop where
  /-- The family is jointly almost everywhere measurable, so that its joint law is defined. -/
  protected aemeasurable : AEMeasurable (fun ω i ↦ X i ω) μ
  /-- Reindexing the family by a permutation does not change its joint law. -/
  protected map_eq (σ : Equiv.Perm ι) : μ.map (fun ω i ↦ X (σ i) ω) = μ.map fun ω i ↦ X i ω

private theorem aemeasurable_comp_index (hX : AEMeasurable (fun ω i ↦ X i ω) μ) {f : ι' → ι} :
    AEMeasurable (fun ω k ↦ X (f k) ω) μ :=
  (Measurable.of_eval fun k ↦ measurable_pi_apply (f k)).comp_aemeasurable hX

/-- Under a finite measure, reindexing along `f` preserves the joint law as soon as on each
finite set of indices `f` agrees with a reindexing that does. -/
private theorem map_comp_eq_of_forall_finset [IsFiniteMeasure μ]
    (hX : AEMeasurable (fun ω i ↦ X i ω) μ) {f : ι → ι}
    (h : ∀ I : Finset ι, ∃ g : ι → ι, Set.EqOn g f I ∧
      μ.map (fun ω i ↦ X (g i) ω) = μ.map fun ω i ↦ X i ω) :
    μ.map (fun ω i ↦ X (f i) ω) = μ.map fun ω i ↦ X i ω := by
  have hr (I : Finset ι) : Measurable (I.restrict (π := fun _ ↦ E)) :=
    .of_eval fun _ ↦ measurable_pi_apply _
  refine IsProjectiveLimit.unique
    (P := fun I : Finset ι ↦ (μ.map fun ω i ↦ X i ω).map I.restrict) (fun I ↦ ?_) (fun I ↦ rfl)
  obtain ⟨g, hgf, hg⟩ := h I
  beta_reduce
  rw [← hg, AEMeasurable.map_map_of_aemeasurable (hr I).aemeasurable (aemeasurable_comp_index hX),
    AEMeasurable.map_map_of_aemeasurable (hr I).aemeasurable (aemeasurable_comp_index hX)]
  congr 1
  ext ω i
  simp [hgf (Finset.mem_coe.2 i.2)]

namespace Exchangeable

/-- A family indexed by a type with at most one element is exchangeable. -/
theorem of_subsingleton [Subsingleton ι] (hX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    Exchangeable X μ :=
  ⟨hX, fun σ ↦ by rw [Subsingleton.elim σ 1]; rfl⟩

/-- Under a finite measure, a family is exchangeable as soon as its joint law is unchanged by the
permutations that move finitely many indices. -/
theorem of_finite_support [IsFiniteMeasure μ] (hX : AEMeasurable (fun ω i ↦ X i ω) μ)
    (h : ∀ τ : Equiv.Perm ι, {i | τ i ≠ i}.Finite →
      μ.map (fun ω i ↦ X (τ i) ω) = μ.map fun ω i ↦ X i ω) : Exchangeable X μ where
  aemeasurable := hX
  map_eq σ := map_comp_eq_of_forall_finset hX fun I ↦
    let ⟨τ, hτ, hτI⟩ := σ.exists_finite_setOf_ne_and_eqOn I
    ⟨τ, hτI, h τ hτ⟩

/-- A family almost everywhere equal to an exchangeable family is exchangeable. -/
theorem congr (h : Exchangeable X μ) (hXY : ∀ᵐ ω ∂μ, ∀ i, X i ω = Y i ω) : Exchangeable Y μ where
  aemeasurable := h.aemeasurable.congr (hXY.mono fun ω hω ↦ funext hω)
  map_eq σ := by
    rw [← Measure.map_congr (hXY.mono fun ω hω ↦ funext hω),
      ← Measure.map_congr (f := fun ω i ↦ X (σ i) ω) (hXY.mono fun ω hω ↦ funext fun i ↦ hω (σ i))]
    exact h.map_eq σ

/-- An exchangeable family has the same joint law as each of its reindexings by a permutation. -/
theorem identDistrib_perm (h : Exchangeable X μ) (σ : Equiv.Perm ι) :
    IdentDistrib (fun ω i ↦ X (σ i) ω) (fun ω i ↦ X i ω) μ μ :=
  ⟨aemeasurable_comp_index h.aemeasurable, h.aemeasurable, h.map_eq σ⟩

/-- The members of an exchangeable family are identically distributed. -/
theorem identDistrib (h : Exchangeable X μ) (i j : ι) : IdentDistrib (X i) (X j) μ μ := by
  classical
  simpa [Function.comp_def] using
    (h.identDistrib_perm (Equiv.swap i j)).comp (measurable_pi_apply j)

/-- Applying one measurable function to every member of an exchangeable family gives an
exchangeable family. -/
theorem comp (h : Exchangeable X μ) {g : E → F} (hg : Measurable g) :
    Exchangeable (fun i ↦ g ∘ X i) μ :=
  have hG : Measurable fun (x : ι → E) i ↦ g (x i) := by fun_prop
  ⟨hG.comp_aemeasurable h.aemeasurable, fun σ ↦ ((h.identDistrib_perm σ).comp hG).map_eq⟩

/-- A subfamily of an exchangeable family is exchangeable. -/
theorem precomp {f : ι' → ι} (hf : f.Injective) (h : Exchangeable X μ) :
    Exchangeable (fun k ↦ X (f k)) μ where
  aemeasurable := aemeasurable_comp_index h.aemeasurable
  map_eq τ := by
    have := ((h.identDistrib_perm (τ.viaEmbedding ⟨f, hf⟩)).comp (u := fun x k ↦ x (f k))
      (Measurable.of_eval fun k ↦ measurable_pi_apply (f k))).map_eq
    have hv (k : ι') : τ.viaEmbedding ⟨f, hf⟩ (f k) = f (τ k) := τ.viaEmbedding_apply ⟨f, hf⟩ k
    simpa [Function.comp_def, hv] using this

/-- Under a finite measure, reindexing an exchangeable family along an injective map of the index
type into itself does not change its joint law. -/
theorem map_precomp_eq [IsFiniteMeasure μ] (h : Exchangeable X μ) {f : ι → ι}
    (hf : f.Injective) : μ.map (fun ω i ↦ X (f i) ω) = μ.map fun ω i ↦ X i ω :=
  map_comp_eq_of_forall_finset h.aemeasurable fun I ↦
    let ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : I ↦ (i : ι)) (fun i : I ↦ f i)
      Subtype.val_injective (hf.comp Subtype.val_injective)
    ⟨σ, fun i hi ↦ hσ ⟨i, hi⟩, h.map_eq σ⟩

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
    Exchangeable (fun i (x : ι → E) ↦ x i) μ ↔
      SMulInvariantMeasure (Equiv.Perm ι)ᵈᵐᵃ (ι → E) μ := by
  simpa using exchangeable_iff_smulInvariantMeasure_map (X := fun i (x : ι → E) ↦ x i)
    (μ := μ) aemeasurable_id

/-- A family is exchangeable if and only if the coordinates are exchangeable under its joint
law. -/
theorem exchangeable_iff_exchangeable_eval_map (hX : AEMeasurable (fun ω i ↦ X i ω) μ) :
    Exchangeable X μ ↔ Exchangeable (fun i (x : ι → E) ↦ x i) (μ.map fun ω i ↦ X i ω) := by
  rw [exchangeable_eval_iff, exchangeable_iff_smulInvariantMeasure_map hX]

/-- Independent and identically distributed random variables are exchangeable. -/
theorem iIndepFun.exchangeable_of_aemeasurable (hX : iIndepFun X μ)
    (hm : AEMeasurable (fun ω i ↦ X i ω) μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) :
    Exchangeable X μ where
  aemeasurable := hm
  map_eq σ := by
    rw [(hX.precomp σ.injective).map_fun_eq_infinitePi_map₀ (aemeasurable_comp_index hm),
      hX.map_fun_eq_infinitePi_map₀ hm]
    congr 1
    ext1 i
    exact (hid _ _).map_eq

/-- Countably many independent and identically distributed random variables are exchangeable. -/
theorem iIndepFun.exchangeable [Countable ι] (hX : iIndepFun X μ)
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ) : Exchangeable X μ :=
  hX.exchangeable_of_aemeasurable (.of_eval fun i ↦ (hid i i).aemeasurable_fst) hid

/-- A family whose joint law is a mixture of laws of independent and identically distributed
sequences is exchangeable. -/
theorem exchangeable_of_map_eq_bind {X : ℕ → Ω → E} (hX : AEMeasurable (fun ω i ↦ X i ω) μ)
    {Λ : Measure (ProbabilityMeasure E)}
    (h : μ.map (fun ω i ↦ X i ω) =
      Λ.bind fun m ↦ Measure.infinitePi fun _ : ℕ ↦ (m : Measure E)) :
    Exchangeable X μ := by
  rw [exchangeable_iff_smulInvariantMeasure_map hX, h]
  exact smulInvariantMeasure_bind (measurable_infinitePi_const ℕ).aemeasurable
    (ae_of_all _ fun _ ↦ inferInstance)

end Exchangeable

end ProbabilityTheory
