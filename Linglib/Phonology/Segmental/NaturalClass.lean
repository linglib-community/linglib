module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Phonology.Segmental.Defs
import Mathlib.Data.Fintype.Powerset

/-!
# Natural classes

This file defines the natural classes of an inventory. In Hayes's definition a natural class
is any complete set of sounds of a language that share the same value for a feature or set of
features, so that /p t k/ are the voiceless stops of English and not of Persian, which has /q/
as well. A feature description is an underspecified segment `d`, a segment `x` has the values
of `d` when `d ≤ x`, and the natural class of `d` in an inventory is the set of its members
above `d`.

What the segments of a set share is their meet, the description Albright and Hayes's minimal
generalization reduces two differing segments to, and the natural class of that meet is the
smallest natural class containing the set. A set is a natural class exactly when it is that
smallest class, which makes the property decidable, and two natural classes that overlap meet
in a natural class. Ordered by inclusion and with the empty set at the bottom, the natural
classes form Broe's lattice of representations.

## Main definitions

* `Phonology.Segment.naturalClass`: the members of an inventory that have the values of a
  description.
* `Phonology.IsNaturalClass`: a nonempty set of segments is the natural class of some
  description.

## Main results

* `Phonology.Segment.subset_naturalClass_iff`: a set lies in the natural class of `d` exactly
  when it lies in the inventory and `d` is a lower bound of it, the Galois connection between
  sets of segments and descriptions.
* `Phonology.Segment.naturalClass_inf'_subset_iff`: the natural class of what a set shares is the
  smallest natural class containing the set.
* `Phonology.isNaturalClass_iff`: a set is a natural class exactly when it is the natural class
  of what its members share.
* `Phonology.IsNaturalClass.inter`: two overlapping natural classes meet in a natural class.
* `Phonology.Sonority.isNaturalClass_image_iff`: among the columns of Hayes's Table 4.1, the
  natural classes are the sets of sonority classes that are contiguous on the hierarchy.

## Implementation notes

Descriptions are ordered by subsumption and natural classes by inclusion, and the two maps
`naturalClass` and `Finset.inf'` form an antitone Galois connection, that of formal concept
analysis for the relation `d ≤ x`. The meet of the empty set would be an inconsistent
description, which `Segment` lacks, so the statements about meets are for nonempty sets, and
a natural class is nonempty by definition.

## References

* [hayes-2009]
* [albright-hayes-2003]
* [broe-1993]
-/

@[expose] public section

namespace Phonology

variable {I S T : Finset Segment} {d x : Segment}

namespace Segment

/-- The natural class of a description `d` in an inventory `I` is the complete set of segments
of `I` that have the values of `d`. -/
def naturalClass (d : Segment) (I : Finset Segment) : Finset Segment := I.filter (d ≤ ·)

@[simp] theorem mem_naturalClass : x ∈ d.naturalClass I ↔ x ∈ I ∧ d ≤ x := Finset.mem_filter

theorem naturalClass_subset (d : Segment) (I : Finset Segment) : d.naturalClass I ⊆ I :=
  Finset.filter_subset _ _

@[simp] theorem naturalClass_bot (I : Finset Segment) : (⊥ : Segment).naturalClass I = I :=
  Finset.filter_true_of_mem fun _ _ ↦ bot_le

theorem naturalClass_anti (I : Finset Segment) : Antitone (naturalClass · I) :=
  fun _ _ h ↦ Finset.monotone_filter_right I fun _ _ he ↦ h.trans he

theorem naturalClass_mono (d : Segment) : Monotone d.naturalClass :=
  fun _ _ h ↦ Finset.filter_subset_filter _ h

/-- A set lies in the natural class of `d` exactly when it lies in the inventory and `d` is
below each of its members. -/
theorem subset_naturalClass_iff :
    S ⊆ d.naturalClass I ↔ S ⊆ I ∧ d ∈ lowerBounds (S : Set Segment) := by
  simp only [Finset.subset_iff, mem_naturalClass, mem_lowerBounds, Finset.mem_coe, imp_and,
    forall_and]

theorem subset_naturalClass_iff_le_inf' (hS : S ⊆ I) (hne : S.Nonempty) :
    S ⊆ d.naturalClass I ↔ d ≤ S.inf' hne id := by
  rw [subset_naturalClass_iff, le_isGLB_iff (Finset.isGLB_inf' hne), and_iff_right hS]

theorem subset_naturalClass_inf' (hS : S ⊆ I) (hne : S.Nonempty) :
    S ⊆ (S.inf' hne id).naturalClass I :=
  (subset_naturalClass_iff_le_inf' hS hne).2 le_rfl

/-- The natural class of what a set shares is the smallest natural class containing the
set. -/
theorem naturalClass_inf'_subset_iff (hS : S ⊆ I) (hne : S.Nonempty) :
    (S.inf' hne id).naturalClass I ⊆ d.naturalClass I ↔ S ⊆ d.naturalClass I :=
  ⟨(subset_naturalClass_inf' hS hne).trans,
    fun h ↦ naturalClass_anti I ((subset_naturalClass_iff_le_inf' hS hne).1 h)⟩

end Segment

open Segment

/-- A nonempty set of segments is a natural class of the inventory `I` when it is the complete
set of segments of `I` that have the values of some description. -/
def IsNaturalClass (I S : Finset Segment) : Prop :=
  S.Nonempty ∧ ∃ d : Segment, d.naturalClass I = S

theorem IsNaturalClass.nonempty (h : IsNaturalClass I S) : S.Nonempty := h.1

theorem IsNaturalClass.subset (h : IsNaturalClass I S) : S ⊆ I := by
  obtain ⟨-, d, rfl⟩ := h; exact d.naturalClass_subset I

theorem isNaturalClass_naturalClass (h : (d.naturalClass I).Nonempty) :
    IsNaturalClass I (d.naturalClass I) :=
  ⟨h, d, rfl⟩

theorem isNaturalClass_self (h : I.Nonempty) : IsNaturalClass I I := ⟨h, ⊥, naturalClass_bot I⟩

/-- A set is a natural class exactly when it is the natural class of what its members
share. -/
theorem isNaturalClass_iff :
    IsNaturalClass I S ↔ ∃ hne : S.Nonempty, (S.inf' hne id).naturalClass I = S := by
  refine ⟨fun h ↦ ⟨h.1, ?_⟩, fun ⟨hne, h⟩ ↦ ⟨hne, _, h⟩⟩
  have hS := h.subset
  obtain ⟨hne, d, rfl⟩ := h
  exact (subset_naturalClass_inf' hS hne).antisymm'
    ((naturalClass_inf'_subset_iff hS hne).2 subset_rfl)

instance (I S : Finset Segment) : Decidable (IsNaturalClass I S) :=
  decidable_of_iff _ isNaturalClass_iff.symm

/-- Two natural classes that overlap meet in a natural class, that of what their common members
share. -/
theorem IsNaturalClass.inter (hS : IsNaturalClass I S) (hT : IsNaturalClass I T)
    (hST : (S ∩ T).Nonempty) : IsNaturalClass I (S ∩ T) := by
  obtain ⟨-, d, rfl⟩ := hS
  obtain ⟨-, e, rfl⟩ := hT
  have hI : d.naturalClass I ∩ e.naturalClass I ⊆ I :=
    Finset.inter_subset_left.trans (d.naturalClass_subset I)
  refine isNaturalClass_iff.2 ⟨hST, (subset_naturalClass_inf' hI hST).antisymm' ?_⟩
  exact Finset.subset_inter
    ((naturalClass_inf'_subset_iff hI hST).2 Finset.inter_subset_left)
    ((naturalClass_inf'_subset_iff hI hST).2 Finset.inter_subset_right)

theorem Sonority.naturalClass_description (c : Sonority) :
    c.description.naturalClass (Finset.univ.image Sonority.toSegment) = {c.toSegment} := by
  revert c
  decide +kernel

/-- Among the columns of Table 4.1, the natural classes are the contiguous sets (p. 76). -/
theorem Sonority.isNaturalClass_image_iff {S : Finset Sonority} (hS : S.Nonempty) :
    IsNaturalClass (Finset.univ.image Sonority.toSegment) (S.image Sonority.toSegment) ↔
      (S : Set Sonority).OrdConnected := by
  simp only [Set.ordConnected_iff, Finset.mem_coe, Set.subset_def, Set.mem_Icc]
  have key : ∀ S : Finset Sonority, S.Nonempty →
      (IsNaturalClass (Finset.univ.image toSegment) (S.image toSegment) ↔
        ∀ a ∈ S, ∀ b ∈ S, a ≤ b → ∀ c, a ≤ c ∧ c ≤ b → c ∈ S) := by
    decide +kernel
  exact key S hS

end Phonology
