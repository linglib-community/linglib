/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Defs

/-!
# IDENT

IDENT(F) requires correspondent elements to have the same value for the feature F. This is the
one family of faithfulness constraints that reads the elements, through a labelling of each
position type: `Correspondence.identViol` counts the corresponding pairs whose labels differ, and
`Correspondence.maxViolFeature` and `Correspondence.depViolFeature` are MAX and DEP of a
privative property.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
-/

@[expose] public section

namespace OptimalityTheory.Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

section Ident

variable {F : Type*} [DecidableEq F]

/-- IDENT counts the corresponding pairs that differ under the labellings `s` and `t`, which
give each position its segment or the value of one of its features. -/
def identViol (s : ι → F) (t : κ → F) (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ s x.1 ≠ t x.2).card

@[simp] theorem identViol_empty (s : ι → F) (t : κ → F) : identViol s t ∅ = 0 := rfl

@[simp] theorem identViol_inv (R : Correspondence ι κ) (s : ι → F) (t : κ → F) :
    R.inv.identViol t s = R.identViol s t := by
  rw [identViol, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ ne_comm)

theorem identViol_eq_zero_iff_of_graph {R : Correspondence ι κ} {f : ι → κ}
    (hf : R.rel = Function.graph f) (s : ι → F) (t : κ → F) :
    R.identViol s t = 0 ↔ ∀ i, s i = t (f i) := by
  simp only [identViol, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not]
  refine ⟨fun H i ↦ H ((mem_iff_of_graph hf).2 rfl), ?_⟩
  rintro H ⟨i, j⟩ hij
  rw [← (mem_iff_of_graph hf).1 hij]
  exact H i

end Ident

section Feature

variable (p : ι → Prop) (q : κ → Prop) [DecidablePred p] [DecidablePred q]

/-- MAX of a privative property counts the corresponding pairs whose first member has it and
whose second lacks it, the autosegment being lost. -/
def maxViolFeature (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ p x.1 ∧ ¬ q x.2).card

/-- DEP of a privative property counts the corresponding pairs whose second member has it and
whose first lacks it, the autosegment being inserted. -/
def depViolFeature (R : Correspondence ι κ) : ℕ :=
  (R.filter fun x ↦ ¬ p x.1 ∧ q x.2).card

@[simp] theorem maxViolFeature_empty : maxViolFeature p q ∅ = 0 := rfl

@[simp] theorem depViolFeature_empty : depViolFeature p q ∅ = 0 := rfl

@[simp] theorem maxViolFeature_inv (R : Correspondence ι κ) :
    R.inv.maxViolFeature q p = R.depViolFeature p q := by
  rw [maxViolFeature, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm)

@[simp] theorem depViolFeature_inv (R : Correspondence ι κ) :
    R.inv.depViolFeature q p = R.maxViolFeature p q := by
  rw [depViolFeature, card_filter_inv]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm)

theorem maxViolFeature_pos_iff (R : Correspondence ι κ) :
    0 < R.maxViolFeature p q ↔ ∃ x ∈ R, p x.1 ∧ ¬ q x.2 := by
  simp [maxViolFeature, Finset.card_pos, Finset.filter_nonempty_iff]

end Feature

end OptimalityTheory.Correspondence
