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

In Harbour's calculus of person features a group is a nonempty set of atoms, and a feature
denotes the lattice of groups of its atoms: for a set of atoms `X`, the nonempty subsets
`Finset.Ioc ∅ X`. A feature with a value acts on the lattice `G` of its host. The plus value joins
every group of the feature's lattice `F` with every group of `G`, the pointwise join `F ⊻ G`. The
minus value subtracts every group of `F` from every group of `G` at once, so it subtracts their
join: `G \\ {F.sup id}`. The action of a feature with a given value is `act`.

The groups of `Z` containing an atom of `Y` form the family `containing Y Z`. Adding the lattice
of `X ⊆ Z` to it keeps the groups that also contain an atom of `X` (`Ioc_sups_containing`). When
`X ⊆ Y` these are all the groups of `Z` containing an atom of `X`, so along a chain of features
the outermost, most specific one fixes the result (`Ioc_sups_containing_of_subset`), and the
lattice of `X` added to that of `Y ⊇ X` is `containing X Y` (`Ioc_sups_Ioc`).

Lexical Complementarity confines a denotation `G` to the groups of no competing denotation in `D`
that lies properly inside it: `lexComp D G = G \ {F ∈ D | F ⊂ G}.sup id`.

## References

* [harbour-2016]
* [toosarvandani-2023]
-/

@[expose] public section

open scoped FinsetFamily

namespace Plurality.FeatureAction

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The action of a feature -/

/-- The action of the feature lattice `F` with the value `sign` on the lattice `G`: the plus value
joins every group of `F` with every group of `G`, and the minus value subtracts the join of `F`
from every group of `G`, which can leave the empty set. -/
def act (sign : Bool) (F G : Finset (Finset α)) : Finset (Finset α) :=
  if sign then F ⊻ G else G \\ {F.sup id}

@[simp] theorem act_true (F G : Finset (Finset α)) : act true F G = F ⊻ G := rfl

@[simp] theorem act_false (F G : Finset (Finset α)) : act false F G = G \\ {F.sup id} := rfl

/-! ### Groups containing an atom -/

/-- `containing X Y` is the family of subsets of `Y` that contain an atom of `X`. -/
def containing (X Y : Finset α) : Finset (Finset α) := {s ∈ Y.powerset | (s ∩ X).Nonempty}

variable {X X' Y Z s : Finset α}

@[simp] theorem mem_containing_iff : s ∈ containing X Y ↔ s ⊆ Y ∧ (s ∩ X).Nonempty := by
  simp [containing]

@[gcongr] theorem containing_mono (h : X ⊆ X') : containing X Y ⊆ containing X' Y := fun _ hs ↦
  mem_containing_iff.2 ⟨(mem_containing_iff.1 hs).1,
    (mem_containing_iff.1 hs).2.mono (inter_subset_inter_left h)⟩

theorem containing_subset_containing_iff : containing X Z ⊆ containing X' Z ↔ X ∩ Z ⊆ X' := by
  refine ⟨fun h x hx ↦ ?_, fun h s hs ↦ ?_⟩
  · rw [mem_inter] at hx
    obtain ⟨y, hy⟩ := (mem_containing_iff.1 <| h <|
      mem_containing_iff.2 ⟨singleton_subset_iff.2 hx.2, x, by simp [hx.1]⟩).2
    rw [mem_inter, mem_singleton] at hy
    exact hy.1 ▸ hy.2
  · obtain ⟨hsZ, x, hx⟩ := mem_containing_iff.1 hs
    rw [mem_inter] at hx
    exact mem_containing_iff.2 ⟨hsZ, x, mem_inter.2 ⟨hx.1, h (mem_inter.2 ⟨hx.2, hsZ hx.1⟩)⟩⟩

theorem containing_ssubset_containing_iff :
    containing X Z ⊂ containing X' Z ↔ X ∩ Z ⊂ X' ∩ Z := by
  have h {X X' : Finset α} : containing X Z ⊆ containing X' Z ↔ X ∩ Z ⊆ X' ∩ Z := by
    rw [containing_subset_containing_iff, subset_inter_iff, and_iff_left inter_subset_right]
  exact and_congr h (not_congr h)

theorem containing_self (X : Finset α) : containing X X = Ioc ∅ X := by
  ext s
  simp only [mem_containing_iff, mem_Ioc, empty_ssubset]
  exact ⟨fun h ↦ ⟨h.2.mono inter_subset_left, h.1⟩,
    fun h ↦ ⟨h.2, h.1.mono (subset_inter subset_rfl h.2)⟩⟩

/-- Adding the lattice of `X ⊆ Z` to the groups of `Z` containing an atom of `Y` keeps those that
also contain an atom of `X`. -/
theorem Ioc_sups_containing (h : X ⊆ Z) :
    Ioc ∅ X ⊻ containing Y Z = containing X Z ∩ containing Y Z := by
  ext s
  simp only [mem_sups, mem_inter, mem_containing_iff, mem_Ioc, empty_ssubset]
  constructor
  · rintro ⟨x, ⟨hx, hxX⟩, y, ⟨hyZ, hyY⟩, rfl⟩
    exact ⟨⟨union_subset (hxX.trans h) hyZ, hx.mono (subset_inter subset_union_left hxX)⟩,
      union_subset (hxX.trans h) hyZ, hyY.mono (inter_subset_inter_right subset_union_right)⟩
  · rintro ⟨⟨hsZ, hX⟩, -, hY⟩
    exact ⟨s ∩ X, ⟨hX, inter_subset_right⟩, s, ⟨hsZ, hY⟩, union_eq_right.2 inter_subset_left⟩

theorem Ioc_sups_containing_of_subset (hXY : X ⊆ Y) (hXZ : X ⊆ Z) :
    Ioc ∅ X ⊻ containing Y Z = containing X Z := by
  rw [Ioc_sups_containing hXZ, inter_eq_left.2 (containing_mono hXY)]

/-- Adding the lattice of `X` to the lattice of `Y ⊇ X` gives the groups of `Y` containing an
atom of `X`. -/
theorem Ioc_sups_Ioc (h : X ⊆ Y) : Ioc ∅ X ⊻ Ioc ∅ Y = containing X Y := by
  rw [← containing_self Y, Ioc_sups_containing_of_subset h h]

/-! ### Lexical Complementarity -/

/-- Lexical Complementarity confines the denotation `G` to the groups held by no denotation of
`D` properly inside `G`. -/
def lexComp (D : Finset (Finset (Finset α))) (G : Finset (Finset α)) : Finset (Finset α) :=
  G \ {F ∈ D | F ⊂ G}.sup id

variable {D : Finset (Finset (Finset α))} {G : Finset (Finset α)}

theorem mem_lexComp_iff : s ∈ lexComp D G ↔ s ∈ G ∧ ∀ F ∈ D, F ⊂ G → s ∉ F := by
  simp [lexComp, mem_sup]

end Plurality.FeatureAction
