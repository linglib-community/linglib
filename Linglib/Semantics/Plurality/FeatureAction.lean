/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sups

/-!
# Feature actions on lattices of groups

In Harbour's calculus a feature denotes a lattice of groups, the nonempty sets of some atoms,
and its values act on the lattice of its host. The groups of a set of atoms `X` are its nonempty
subsets, mathlib's interval `Finset.Ioc ∅ X`. The positive value adds the feature's lattice
pairwise, which is mathlib's pointwise join `⊻` of set families (`Finset.sups`, Harbour's `⊕`);
the negative value subtracts the feature lattice's maximum from every group. When one feature
specification denotes a proper subset of another, Lexical Complementarity confines the larger to
the difference, a set difference `\`. Toosarvandani reuses the calculus for animacy, where the
lattice of a feature added to the lattice of a larger atom set gives the groups containing one of
its atoms.

## Main definitions

* `Plurality.FeatureAction.ominus`: the negative action of a feature.
* `Plurality.FeatureAction.act`: the action of a feature with a given value.
* `Plurality.FeatureAction.containing`: the groups containing an atom of a given set.

## Main results

* `Plurality.FeatureAction.Ioc_sups_Ioc`,
  `Plurality.FeatureAction.Ioc_sups_containing`: along an entailment chain, adding a
  feature's lattice gives the groups containing one of its atoms.
* `Plurality.FeatureAction.containing_subset_containing_iff`: such denotations are ordered as
  the features' atoms are.
* `Plurality.FeatureAction.mem_containing_sdiff_containing_iff`: Lexical Complementarity
  between two such denotations.

## References

* [harbour-2016]
* [toosarvandani-2023]
-/

@[expose] public section

open scoped FinsetFamily

namespace Plurality.FeatureAction

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The actions of a feature -/

/-- The negative action of a feature lattice `F` on `G` subtracts the maximum of `F` from every
element of `G`. The empty set may result; the host head discards it. -/
def ominus (F G : Finset (Finset α)) : Finset (Finset α) := G.image (· \ F.sup id)

theorem mem_ominus_iff {F G : Finset (Finset α)} {z : Finset α} :
    z ∈ ominus F G ↔ ∃ g ∈ G, g \ F.sup id = z := mem_image

theorem ominus_subset {F G G' : Finset (Finset α)} (h : G ⊆ G') :
    ominus F G ⊆ ominus F G' :=
  image_subset_image h

/-- `act sign F G` is the action of the feature lattice `F` on `G` with the value `sign`,
positive or negative. -/
def act (sign : Bool) (F G : Finset (Finset α)) : Finset (Finset α) :=
  if sign then F ⊻ G else ominus F G

@[simp] theorem act_true (F G : Finset (Finset α)) : act true F G = F ⊻ G := rfl
@[simp] theorem act_false (F G : Finset (Finset α)) : act false F G = ominus F G := rfl

/-! ### Groups containing an atom -/

/-- `containing X Y` is the set of groups of `Y` that contain an atom of `X`. -/
def containing (X Y : Finset α) : Finset (Finset α) :=
  (Ioc ∅ Y).filter fun s ↦ (s ∩ X).Nonempty

theorem mem_containing_iff {X Y s : Finset α} :
    s ∈ containing X Y ↔ s ⊆ Y ∧ (s ∩ X).Nonempty := by
  simp only [containing, mem_filter, mem_Ioc, empty_ssubset]
  exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.mono inter_subset_left, h.1⟩, h.2⟩⟩

theorem containing_mono {X X' Y : Finset α} (h : X ⊆ X') :
    containing X Y ⊆ containing X' Y := fun _ hs ↦
  mem_containing_iff.2 ⟨(mem_containing_iff.1 hs).1,
    (mem_containing_iff.1 hs).2.mono (inter_subset_inter (Subset.refl _) h)⟩

theorem containing_subset_containing_iff {X X' Y : Finset α} (h : X ⊆ Y) :
    containing X Y ⊆ containing X' Y ↔ X ⊆ X' := by
  refine ⟨fun hc x hx ↦ ?_, containing_mono⟩
  obtain ⟨y, hy⟩ := (mem_containing_iff.1 <| hc <|
    mem_containing_iff.2 ⟨singleton_subset_iff.2 (h hx), x, by simp [hx]⟩).2
  rw [mem_inter, mem_singleton] at hy
  exact hy.1 ▸ hy.2

theorem Ioc_sups_Ioc {X Y : Finset α} (h : X ⊆ Y) :
    Ioc ∅ X ⊻ Ioc ∅ Y = containing X Y := by
  ext s
  rw [mem_sups, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [mem_Ioc, empty_ssubset] at hx hy
    exact ⟨union_subset (hx.2.trans h) hy.2, hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_Ioc.2 ⟨empty_ssubset.2 hX, inter_subset_right⟩, s,
      mem_Ioc.2 ⟨empty_ssubset.2 (hX.mono inter_subset_left), hs⟩,
      union_eq_right.2 inter_subset_left⟩

theorem Ioc_sups_containing {X Y Z : Finset α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    Ioc ∅ X ⊻ containing Y Z = containing X Z := by
  ext s
  rw [mem_sups, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [mem_Ioc, empty_ssubset] at hx
    rw [mem_containing_iff] at hy
    exact ⟨union_subset (hx.2.trans (hXY.trans hYZ)) hy.1,
      hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_Ioc.2 ⟨empty_ssubset.2 hX, inter_subset_right⟩, s,
      mem_containing_iff.2 ⟨hs, hX.mono (inter_subset_inter (Subset.refl _) hXY)⟩,
      union_eq_right.2 inter_subset_left⟩

theorem mem_containing_sdiff_containing_iff {X Y Z s : Finset α} :
    s ∈ containing Y Z \ containing X Z ↔ s ⊆ Z ∧ (s ∩ Y).Nonempty ∧ ¬ (s ∩ X).Nonempty := by
  rw [mem_sdiff, mem_containing_iff, mem_containing_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.1.2, fun hX ↦ h.2 ⟨h.1.1, hX⟩⟩,
    fun h ↦ ⟨⟨h.1, h.2.1⟩, fun h' ↦ h.2.2 h'.2⟩⟩

theorem containing_not_subset_of_disjoint {X Y Z : Finset α} (hd : Disjoint X Y)
    (hX : X.Nonempty) (hXZ : X ⊆ Z) :
    ¬ containing X Z ⊆ containing Y Z := by
  obtain ⟨x, hx⟩ := hX
  intro h
  obtain ⟨y, hy⟩ := (mem_containing_iff.1
    (h (mem_containing_iff.2 ⟨singleton_subset_iff.2 (hXZ hx), ⟨x, by simp [hx]⟩⟩))).2
  rw [mem_inter, mem_singleton] at hy
  exact disjoint_left.1 hd hx (hy.1 ▸ hy.2)

end Plurality.FeatureAction
