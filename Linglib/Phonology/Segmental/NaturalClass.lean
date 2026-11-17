module

public import Linglib.Phonology.Segmental.Basic

/-!
# Natural classes

This file defines the natural classes of an inventory. In Hayes's definition a natural class
is any complete set of sounds of a language that share the same value for a feature or set of
features, so that /p t k/ are the voiceless stops of English and not of Persian, which has /q/
as well. The [natural class](##Phonology.naturalClass) of a feature matrix in an inventory is the
set of its segments that include the matrix.

[What the segments of a set share](##Phonology.sharedSpecs) is the feature values they all
have, which Albright and Hayes's minimal generalization reduces two differing segments to, and
the segments with those values are
[the smallest natural class containing the set](##Phonology.extent_sharedSpecs_subset_iff).
A set is a natural class [exactly when it is that smallest class](##Phonology.isNaturalClass_iff),
which makes the property decidable, and
[two natural classes meet in a natural class](##Phonology.IsNaturalClass.inter). Ordered by
inclusion, the natural classes form Broe's lattice of representations.

## Implementation notes

The theory is that of formal concept analysis for the relation of a segment to the feature
values it has: [the segments with a set of values](##Phonology.extent) and `sharedSpecs` form
an [antitone Galois connection](##Phonology.subset_extent_iff) between sets of segments and
sets of feature values. A set with both values of a feature is the set of values of no feature
matrix and no segment has it, so the empty set is a natural class, the bottom of the lattice,
and what the empty set shares is every feature value.

## References

* [hayes-2009]
* [albright-hayes-2003]
* [broe-1993]
-/

@[expose] public section

namespace Phonology

variable {I J S T : Finset Segment} {A B : Finset (Feature × Bool)} {d x : Segment}
  {f : Feature} {v : Bool}

/-! ### The Galois connection -/

/-- The segments of an inventory that have every feature value in a set. -/
def extent (A : Finset (Feature × Bool)) (I : Finset Segment) : Finset Segment :=
  I.filter fun x ↦ ∀ p ∈ A, x p.1 = some p.2

@[simp] theorem mem_extent : x ∈ extent A I ↔ x ∈ I ∧ A ⊆ x.specs := by
  rw [extent, Finset.mem_filter, Segment.subset_specs_iff]

theorem extent_subset (A : Finset (Feature × Bool)) (I : Finset Segment) : extent A I ⊆ I :=
  Finset.filter_subset _ _

@[simp] theorem extent_empty (I : Finset Segment) : extent ∅ I = I :=
  Finset.filter_true_of_mem fun _ _ ↦ by simp

theorem extent_anti (I : Finset Segment) : Antitone (extent · I) := fun _ _ h _ hx ↦
  mem_extent.2 ⟨(mem_extent.1 hx).1, h.trans (mem_extent.1 hx).2⟩

theorem extent_union (A B : Finset (Feature × Bool)) (I : Finset Segment) :
    extent (A ∪ B) I = extent A I ∩ extent B I := by
  ext x
  simp only [mem_extent, Finset.mem_inter, Finset.union_subset_iff]
  tauto

/-- What the segments of a set share: the feature values they all have. -/
def sharedSpecs (S : Finset Segment) : Finset (Feature × Bool) :=
  Finset.univ.filter fun p ↦ ∀ x ∈ S, x p.1 = some p.2

@[simp] theorem mem_sharedSpecs : (f, v) ∈ sharedSpecs S ↔ ∀ x ∈ S, x f = some v := by
  simp [sharedSpecs]

/-- A set of feature values is among what a set shares exactly when each member has it. -/
theorem subset_sharedSpecs_iff : A ⊆ sharedSpecs S ↔ ∀ x ∈ S, A ⊆ x.specs := by
  simp only [Finset.subset_iff, Prod.forall, mem_sharedSpecs, Segment.mem_specs]
  exact ⟨fun h x hx f v hd ↦ h f v hd x hx, fun h f v hd x hx ↦ h x hx f v hd⟩

/-- A set of segments has a set of feature values exactly when it lies in the inventory and
its members share them. -/
theorem subset_extent_iff : S ⊆ extent A I ↔ S ⊆ I ∧ A ⊆ sharedSpecs S := by
  simp only [Finset.subset_iff (s₁ := S), mem_extent, forall_and, subset_sharedSpecs_iff]

theorem subset_extent_sharedSpecs (hS : S ⊆ I) : S ⊆ extent (sharedSpecs S) I :=
  subset_extent_iff.2 ⟨hS, subset_rfl⟩

/-- The segments with what a set shares are the smallest such class containing the set. -/
theorem extent_sharedSpecs_subset_iff (hS : S ⊆ I) :
    extent (sharedSpecs S) I ⊆ extent A I ↔ S ⊆ extent A I :=
  ⟨(subset_extent_sharedSpecs hS).trans, fun h ↦ extent_anti I (subset_extent_iff.1 h).2⟩

/-! ### Natural classes -/

/-- The natural class of a feature matrix `d` in an inventory `I` is the complete set of
segments of `I` that include `d`. -/
def naturalClass (d : Segment) (I : Finset Segment) : Finset Segment := I.filter (d ≤ ·)

@[simp] theorem mem_naturalClass : x ∈ naturalClass d I ↔ x ∈ I ∧ d ≤ x :=
  Finset.mem_filter

theorem naturalClass_eq_extent (d : Segment) (I : Finset Segment) :
    naturalClass d I = extent d.specs I := by
  ext x; rw [mem_naturalClass, mem_extent, Segment.le_iff_specs_subset]

theorem naturalClass_subset (d : Segment) (I : Finset Segment) : naturalClass d I ⊆ I :=
  Finset.filter_subset _ _

theorem naturalClass_mono (d : Segment) : Monotone (naturalClass d) :=
  fun _ _ h ↦ Finset.filter_subset_filter _ h

/-- A set lies in the natural class of `d` exactly when it lies in the inventory and its
members share the values of `d`. -/
theorem subset_naturalClass_iff : S ⊆ naturalClass d I ↔ S ⊆ I ∧ d.specs ⊆ sharedSpecs S := by
  rw [naturalClass_eq_extent, subset_extent_iff]

/-- A set of segments is a natural class of the inventory `I` when it is the complete set of
segments of `I` that have some set of feature values. -/
def IsNaturalClass (I S : Finset Segment) : Prop := ∃ A, extent A I = S

theorem IsNaturalClass.subset (h : IsNaturalClass I S) : S ⊆ I := by
  obtain ⟨A, rfl⟩ := h; exact extent_subset A I

theorem isNaturalClass_naturalClass (d : Segment) (I : Finset Segment) :
    IsNaturalClass I (naturalClass d I) :=
  ⟨d.specs, (naturalClass_eq_extent d I).symm⟩

theorem isNaturalClass_self (I : Finset Segment) : IsNaturalClass I I := ⟨∅, extent_empty I⟩

/-- A set is a natural class exactly when it is the set of segments with what its members
share. -/
theorem isNaturalClass_iff : IsNaturalClass I S ↔ extent (sharedSpecs S) I = S := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  rintro ⟨A, rfl⟩
  have hI := extent_subset A I
  exact ((extent_sharedSpecs_subset_iff hI).2 subset_rfl).antisymm (subset_extent_sharedSpecs hI)

instance (I S : Finset Segment) : Decidable (IsNaturalClass I S) :=
  decidable_of_iff _ isNaturalClass_iff.symm

/-- Two natural classes meet in a natural class, that of their feature values together. -/
theorem IsNaturalClass.inter (hS : IsNaturalClass I S) (hT : IsNaturalClass I T) :
    IsNaturalClass I (S ∩ T) := by
  obtain ⟨A, rfl⟩ := hS
  obtain ⟨B, rfl⟩ := hT
  exact ⟨A ∪ B, extent_union A B I⟩

end Phonology
