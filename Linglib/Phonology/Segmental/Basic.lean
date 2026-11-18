/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Phonology.Segmental.Defs

/-!
# Basic theory of segments

This file develops the theory of the segments defined in `Phonology/Segmental/Defs.lean`. A
segment is determined by [the feature values it has](##Phonology.Segment.specs), and it
[includes a feature matrix](##Phonology.Segment.le_iff_specs_subset) exactly when it has
each of the matrix's values, so that including `[+nasal, −voice]`
[is being [+nasal] and [−voice]](##Phonology.Segment.setFeature_le_iff).

Two segments [have the same restriction](##Phonology.Segment.restrict_eq_restrict_iff) to a set of
features exactly when they agree on it, and a set of features is
[distinctive](##Phonology.IsDistinctive) for an inventory when no two of its segments do.

## References

* [hayes-2009]
-/

@[expose] public section

namespace Phonology

variable {s t d : Segment} {f g : Feature} {v : Bool} {C D : Finset Feature}
  {I J : Finset Segment}

namespace Segment

/-! ### Feature values -/

/-- The feature values a segment has. -/
def specs (s : Segment) : Finset (Feature × Bool) := Finset.univ.filter fun p ↦ s p.1 = some p.2

@[simp] theorem mem_specs : (f, v) ∈ s.specs ↔ s f = some v := by simp [specs]

theorem subset_specs_iff {d : Finset (Feature × Bool)} :
    d ⊆ s.specs ↔ ∀ p ∈ d, s p.1 = some p.2 := by
  simp [Finset.subset_iff, specs]

/-- A segment is determined by the feature values it has. -/
theorem specs_injective : Function.Injective specs := fun s t h ↦ ext' fun f ↦ by
  cases hs : s f with
  | some v => exact (mem_specs.1 (h ▸ mem_specs.2 hs)).symm
  | none =>
    cases ht : t f with
    | some v => exact absurd (mem_specs.1 (h ▸ mem_specs.2 ht)) (by simp [hs])
    | none => rfl

/-! ### Inclusion -/

/-- A segment includes a feature matrix exactly when it has each of the matrix's values. -/
theorem le_iff_specs_subset : d ≤ s ↔ d.specs ⊆ s.specs := by
  simp [le_def, Finset.subset_iff]

instance : PartialOrder Segment where
  le_refl _ _ _ := id
  le_trans _ _ _ h h' f v hv := h' f v (h f v hv)
  le_antisymm _ _ h h' :=
    specs_injective <| (le_iff_specs_subset.1 h).antisymm (le_iff_specs_subset.1 h')

instance : DecidableLT Segment := decidableLTOfDecidableLE

instance : OrderBot Segment where
  bot_le _ := nofun

/-- The meet of two segments is what they share: the values they both have. -/
instance : SemilatticeInf Segment where
  inf s t := ⟨fun f ↦ if s f = t f then s f else none⟩
  inf_le_left s t f v h := by
    change (if s f = t f then s f else none) = some v at h
    split_ifs at h; exact h
  inf_le_right s t f v h := by
    change (if s f = t f then s f else none) = some v at h
    split_ifs at h with he; exact he ▸ h
  le_inf r s t hs ht f v h := by
    change (if s f = t f then s f else none) = some v
    rw [hs f v h, ht f v h, if_pos rfl]

theorem inf_apply (s t : Segment) (f : Feature) : (s ⊓ t) f = if s f = t f then s f else none :=
  rfl

/-- Including a matrix with one more value is having that value and including the rest. -/
@[simp] theorem setFeature_le_iff (h : d f = none) :
    d.setFeature f v ≤ s ↔ s f = some v ∧ d ≤ s := by
  refine ⟨fun H ↦ ⟨H f v (Function.update_self ..), fun g w hg ↦ H g w ?_⟩, ?_⟩
  · exact (Function.update_of_ne (by rintro rfl; simp [h] at hg) ..).trans hg
  · rintro ⟨hf, H⟩ g w hg
    obtain rfl | hne := eq_or_ne g f
    · exact ((Function.update_self ..).symm.trans hg) ▸ hf
    · exact H g w ((Function.update_of_ne hne ..).symm.trans hg)

/-! ### Changes -/

@[simp] theorem setFeature_apply_self (s : Segment) (f : Feature) (v : Bool) :
    s.setFeature f v f = v :=
  Function.update_self _ _ _

@[simp] theorem setFeature_apply_of_ne (h : f ≠ g) (s : Segment) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

/-! ### Restriction -/

theorem restrict_apply (C : Finset Feature) (s : Segment) (f : Feature) :
    restrict C s f = if f ∈ C then s f else none := rfl

instance (s t : Segment) (C : Finset Feature) : Decidable (Set.EqOn s t ↑C) :=
  decidable_of_iff (∀ f ∈ C, s f = t f) Iff.rfl

/-- Two segments have the same restriction to a feature set exactly when they agree on it. -/
theorem restrict_eq_restrict_iff : restrict C s = restrict C t ↔ Set.EqOn s t ↑C := by
  refine ⟨fun h f hf ↦ ?_, fun h ↦ ext' fun f ↦ ?_⟩
  · simpa [restrict_apply, Finset.mem_coe.1 hf] using congrArg (· f) h
  · by_cases hf : f ∈ C
    · simp [restrict_apply, hf, h (Finset.mem_coe.2 hf)]
    · simp [restrict_apply, hf]

/-- Restricting to a feature set a segment that has taken another's values on the set keeps
the other's values. -/
theorem restrict_piecewise (s t : Segment) : restrict C (piecewise C s t) = restrict C s :=
  Segment.ext (Finset.piecewise_idem_left ..)

/-- Restricting to one feature set and then another keeps the features in both. -/
theorem restrict_restrict (s : Segment) : restrict D (restrict C s) = restrict (C ∩ D) s := by
  refine ext' fun f ↦ ?_
  by_cases hD : f ∈ D <;> by_cases hC : f ∈ C <;> simp [restrict_apply, hC, hD]

end Segment

/-! ### Distinctive feature sets -/

/-- A feature set is distinctive for an inventory when no two segments of the inventory agree
on it. -/
def IsDistinctive (C : Finset Feature) (I : Finset Segment) : Prop :=
  Set.InjOn (Segment.restrict C) (I : Set Segment)

theorem isDistinctive_iff :
    IsDistinctive C I ↔ ∀ s ∈ I, ∀ t ∈ I, Set.EqOn s t ↑C → s = t := by
  simp only [IsDistinctive, Set.InjOn, Finset.mem_coe, Segment.restrict_eq_restrict_iff]

instance : Decidable (IsDistinctive C I) :=
  decidable_of_iff (∀ s ∈ I, ∀ t ∈ I, (∀ f ∈ C, s f = t f) → s = t) isDistinctive_iff.symm

/-- A distinctive feature set stays distinctive when features are added and segments removed. -/
theorem IsDistinctive.mono (h : IsDistinctive C I) (hCD : C ⊆ D) (hJI : J ⊆ I) :
    IsDistinctive D J :=
  isDistinctive_iff.2 fun s hs t ht he ↦
    isDistinctive_iff.1 h s (hJI hs) t (hJI ht) (he.mono (Finset.coe_subset.2 hCD))

end Phonology

