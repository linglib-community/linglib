/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization

/-!
# Cores of a realization and categorial freedom

Bloomfield distinguishes suppletion of a bound form, the *-en* of *ox : oxen*, from suppletion of
the underlying form, the *bet-* of *good : better* and the *went* of *go : went*. Given a map from
forms to their cores, the cores of a cell are those of its forms, and an index whose forms vary
[either keeps its cores or varies them](##Morphology.Root.suppletive_core_dichotomy); taking each
form as its own core [recovers form variance](##Morphology.Root.hasSuppletiveCore_singleton). An
index is cross-categorial when it is licensed in two contexts of different categories, as the
category-free roots of Marantz and Arad are.

## Implementation notes

The extraction of cores is a parameter, since it encodes the analysis of each form into an
underlying form and the bound forms added to it.

## References

* [bloomfield-1933]
* [marantz-1997]
* [arad-2005]
-/

@[expose] public section

namespace Morphology.Root

open Morphology

variable {R Ctx F C K : Type*}

/-- The cores of a realization at a cell, the union of the cores `extract` assigns to the cell's
forms. -/
def cellCores (S : Realization R Ctx F) (extract : F → Finset C) [DecidableEq C] :
    R → Ctx → Finset C :=
  fun r c ↦ (S.realize r c).biUnion extract

@[simp] theorem cellCores_singleton (S : Realization R Ctx F) [DecidableEq F]
    (r : R) (c : Ctx) : cellCores S (fun f ↦ {f}) r c = S.realize r c := by
  simp [cellCores, Finset.biUnion_singleton_eq_self]

/-- An index **has a suppletive core** when its cores vary across contexts, as *go* does in
*go : went* ([bloomfield-1933]'s suppletion of the underlying form). -/
def HasSuppletiveCore (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] (r : R) : Prop :=
  IsVariantIn (cellCores S extract) r

/-- An index is **affixally inflected** when its forms vary but its cores do not, as in
*kind : kinder* and in *ox : oxen*, whose plural suffix is suppletive. -/
def IsAffixallyInflected (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] (r : R) : Prop :=
  S.IsSuppletive r ∧ IsConstantIn (cellCores S extract) r

theorem isAffixallyInflected_iff (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] {r : R} :
    IsAffixallyInflected S extract r ↔
      S.IsSuppletive r ∧ ¬ HasSuppletiveCore S extract r := by
  rw [IsAffixallyInflected, HasSuppletiveCore, isConstantIn_iff_not_isVariantIn]

/-- An index whose forms vary is either affixally inflected or has a suppletive core. -/
theorem suppletive_core_dichotomy (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] {r : R} (h : S.IsSuppletive r) :
    IsAffixallyInflected S extract r ∨ HasSuppletiveCore S extract r :=
  (em (HasSuppletiveCore S extract r)).symm.imp
    (fun hv ↦ (isAffixallyInflected_iff S extract).2 ⟨h, hv⟩) id

theorem hasSuppletiveCore_singleton (S : Realization R Ctx F) [DecidableEq F]
    (r : R) : HasSuppletiveCore S (fun f ↦ {f}) r ↔ S.IsSuppletive r := by
  simp only [HasSuppletiveCore, Realization.IsSuppletive, IsVariantIn, cellCores_singleton]

/-- An index is **cross-categorial** when it is licensed in two contexts whose categories `k`
differ, as a category-free root is ([marantz-1997], [arad-2005]). -/
def IsCrossCategorial (S : Realization R Ctx F) (k : Ctx → K) (r : R) : Prop :=
  ∃ c c', k c ≠ k c' ∧ S.IsLicensed r c ∧ S.IsLicensed r c'

section Decidable

variable (S : Realization R Ctx F) (extract : F → Finset C)

instance [Fintype Ctx] [DecidableEq C] (r : R) :
    Decidable (HasSuppletiveCore S extract r) :=
  inferInstanceAs (Decidable (∃ c c', ∃ x ∈ cellCores S extract r c,
    ∃ x' ∈ cellCores S extract r c', x ≠ x'))

instance [Fintype Ctx] [DecidableEq F] [DecidableEq C] (r : R) :
    Decidable (IsAffixallyInflected S extract r) :=
  inferInstanceAs (Decidable (S.IsSuppletive r ∧ ∀ c c' : Ctx,
    ∀ x ∈ cellCores S extract r c, ∀ x' ∈ cellCores S extract r c', x = x'))

instance [Fintype Ctx] [DecidableEq F] [DecidableEq K] (k : Ctx → K) (r : R) :
    Decidable (IsCrossCategorial S k r) :=
  inferInstanceAs (Decidable (∃ c c', k c ≠ k c' ∧
    S.IsLicensed r c ∧ S.IsLicensed r c'))

end Decidable

end Morphology.Root
