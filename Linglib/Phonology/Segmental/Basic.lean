/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Core.Data.Fintype.Sets

/-!
# Basic theory of segments

This file develops the theory of the segments defined in `Phonology/Segmental/Defs.lean`.
Natural-class membership is the bundle order of Shieber and Carpenter: having a value is lying
above the segment that has that value alone, and each named natural class is the segments above
its features. The other results concern the change of a feature and distinctive feature sets.

## Main results

* `Segment.le_iff_forall_hasValue`: a description lies below a segment iff the segment has each
  of its values.
* `Segment.ofSpecs_le_iff`: a specification list lies below a segment iff the segment has every
  listed value.
* `IsDistinctive`: a feature set on which no two segments of an inventory agree, with
  `Segment.restrict_eq_restrict_iff` relating restriction to agreement on the set.

## References

* [shieber-1986]
* [carpenter-1992]
-/

@[expose] public section

namespace Phonology

namespace Segment

variable (s : Segment)

/-! ### Natural classes are the bundle order -/

@[simp] theorem ofSpecs_apply (specs : List (Feature × Bool)) (f : Feature) :
    ofSpecs specs f = specs.lookup f := rfl

/-- A description lies below a segment exactly when the segment has every value the
description has. -/
theorem le_iff_forall_hasValue {d : Segment} : d ≤ s ↔ ∀ f v, d.HasValue f v → s.HasValue f v := by
  refine ⟨fun h f v (hv : d f = some v) ↦ ?_, fun h f ↦ ?_⟩
  · have := h f
    rw [hv] at this
    exact Flat.coe_le_iff.1 this
  · cases hf : d f with
    | bot => exact bot_le
    | coe v => exact Flat.coe_le_iff.2 (h f v hf)

/-- A specification list lies below a segment exactly when the segment has every value the
list looks up. -/
theorem ofSpecs_le_iff (specs : List (Feature × Bool)) :
    ofSpecs specs ≤ s ↔ ∀ f v, specs.lookup f = some v → s.HasValue f v :=
  le_iff_forall_hasValue s

/-- With distinct features, a specification list lies below a segment exactly when the
segment has each listed value. -/
theorem ofSpecs_le_iff_forall_mem {specs : List (Feature × Bool)}
    (h : (specs.map Prod.fst).Nodup) :
    ofSpecs specs ≤ s ↔ ∀ p ∈ specs, s.HasValue p.1 p.2 := by
  rw [ofSpecs_le_iff]
  refine ⟨fun H p hp ↦ H p.1 p.2 ?_, fun H f v hv ↦ ?_⟩
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
    refine List.lookup_eq_some_iff.2 ⟨l₁, l₂, rfl, fun q hq ↦ bne_iff_ne.2 fun hpq ↦ ?_⟩
    rw [List.map_append, List.map_cons] at h
    exact (List.nodup_append'.1 h).2.2 (List.mem_map.2 ⟨q, hq, rfl⟩)
      (by rw [← hpq]; exact List.mem_cons_self)
  · obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hv
    exact H (f, v) (List.mem_append_right _ List.mem_cons_self)

/-- Having a value is lying above the segment that specifies that value alone. -/
theorem hasValue_iff_ofSpecs_le (f : Feature) (v : Bool) :
    s.HasValue f v ↔ ofSpecs [(f, v)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by simp)]
  simp

/-- The consonants are the segments above [+consonantal]. -/
theorem isConsonant_iff_le : s.IsConsonant ↔ ofSpecs [(.consonantal, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsConsonant]

/-- The sibilants are the segments above [+strident]. -/
theorem isSibilant_iff_le : s.IsSibilant ↔ ofSpecs [(.strident, true)] ≤ s :=
  hasValue_iff_ofSpecs_le s _ _

/-! ### Changes -/

@[simp] theorem setFeature_hasValue (f : Feature) (v : Bool) : (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

@[simp] theorem setFeature_apply_of_ne {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

end Segment

/-! ### Distinctive feature sets -/

section Distinctive

variable {C D : Finset Feature} {I J : Finset Segment}

instance (s s' : Segment) (C : Finset Feature) : Decidable (Set.EqOn s s' ↑C) :=
  Set.decidableEqOnOfFintype _ _ _

/-- Two segments have the same restriction to a feature set iff they agree on it. -/
theorem Segment.restrict_eq_restrict_iff {s s' : Segment} :
    Segment.restrict C s = Segment.restrict C s' ↔ Set.EqOn s s' ↑C := by
  refine ⟨fun h f hf ↦ ?_, fun h ↦ funext fun f ↦ ?_⟩
  · simpa [Segment.restrict, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.1 hf)]
      using congrFun h f
  · by_cases hf : f ∈ C
    · simp [Segment.restrict, Finset.piecewise_eq_of_mem _ _ _ hf, h (Finset.mem_coe.2 hf)]
    · simp [Segment.restrict, Finset.piecewise_eq_of_notMem _ _ _ hf]

/-- Restricting to one feature set and then another keeps the features in both. -/
theorem Segment.restrict_restrict (s : Segment) :
    Segment.restrict D (Segment.restrict C s) = Segment.restrict (C ∩ D) s := by
  funext f
  by_cases hD : f ∈ D <;> by_cases hC : f ∈ C <;>
    simp [Segment.restrict, Finset.piecewise, hC, hD]

/-- A feature set is distinctive for an inventory when no two segments of the inventory agree
on it. -/
def IsDistinctive (C : Finset Feature) (I : Finset Segment) : Prop :=
  Set.InjOn (Segment.restrict C) (I : Set Segment)

instance : Decidable (IsDistinctive C I) :=
  decidable_of_iff
    (∀ s ∈ I, ∀ s' ∈ I, Segment.restrict C s = Segment.restrict C s' → s = s')
    ⟨fun h _ hs _ hs' ↦ h _ hs _ hs', fun h _ hs _ hs' ↦ h hs hs'⟩

/-- A larger feature set is still distinctive. -/
theorem IsDistinctive.mono (h : IsDistinctive C I) (hCD : C ⊆ D) : IsDistinctive D I :=
  fun s hs s' hs' he ↦ h hs hs' <| by
    have := congrArg (Segment.restrict C) he
    rwa [Segment.restrict_restrict, Segment.restrict_restrict,
      Finset.inter_eq_right.2 hCD] at this

/-- A distinctive feature set is distinctive for every smaller inventory. -/
theorem IsDistinctive.subset (h : IsDistinctive C I) (hJI : J ⊆ I) : IsDistinctive C J :=
  Set.InjOn.mono (Finset.coe_subset.2 hJI) h

end Distinctive

end Phonology
