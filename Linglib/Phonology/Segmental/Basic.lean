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
its features. The other results concern the change of a feature, distinctive feature sets, and
the sonority hierarchy, whose four features each cut it at one point, as in Hayes's Table 4.1.

## Main results

* `Segment.le_iff_forall_hasValue`: a description lies below a segment iff the segment has each
  of its values.
* `Segment.ofSpecs_le_iff`: a specification list lies below a segment iff the segment has every
  listed value.
* `Segment.isVowel_iff_le`, `Segment.isObstruent_iff_le`, `Segment.isNasal_iff_le`: the vowels,
  obstruents and nasals are the segments above the descriptions of their sonority classes.
* `IsDistinctive`: a feature set on which no two segments of an inventory agree, with
  `Segment.restrict_eq_restrict_iff` relating restriction to agreement on the set.
* `Sonority.ofSegment_eq_of_le`: a segment with the values of a column of Table 4.1 has that
  column's sonority.
* `Sonority.description_le_iff`: on such a segment exactly that column's description holds.
* `Sonority.ofSegment_congr`: sonority depends on a segment only through the four features,
  and not on [continuant].
* `Sonority.rise_pos`, `Sonority.rise_eq_zero`, `Sonority.rise_neg`: the sign of the sonority
  rise separates rises, plateaus and falls.

## References

* [shieber-1986]
* [carpenter-1992]
* [parker-2002]
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

/-- The vowels are the segments above the description of their class. -/
theorem isVowel_iff_le : s.IsVowel ↔ Sonority.vowel.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsVowel]

/-- The consonants are the segments above [+consonantal]. -/
theorem isConsonant_iff_le : s.IsConsonant ↔ ofSpecs [(.consonantal, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsConsonant]

theorem isObstruent_iff_le : s.IsObstruent ↔ Sonority.obstruent.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsObstruent]

theorem isNasal_iff_le : s.IsNasal ↔ Sonority.nasal.description ≤ s := by
  rw [Sonority.description, ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsNasal]

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

/-! ### Sonority -/

namespace Sonority

theorem rank_strictMono : StrictMono rank := fun _ _ h ↦ h

theorem nasal_le_iff {c : Sonority} : nasal ≤ c ↔ c.toSegment.HasValue .sonorant true := by
  cases c <;> decide

theorem liquid_le_iff {c : Sonority} : liquid ≤ c ↔ c.toSegment.HasValue .approximant true := by
  cases c <;> decide

theorem glide_le_iff {c : Sonority} : glide ≤ c ↔ c.toSegment.HasValue .consonantal false := by
  cases c <;> decide

theorem vowel_le_iff {c : Sonority} : vowel ≤ c ↔ c.toSegment.HasValue .syllabic true := by
  cases c <;> decide

/-- The features `ofSegment` reads, the four of Table 4.1. -/
def features : Finset Feature := {.sonorant, .approximant, .consonantal, .syllabic}

/-- Sonority depends on a segment only through `Sonority.features`. -/
theorem ofSegment_congr {s s' : Segment} (h : ∀ f ∈ features, s f = s' f) :
    ofSegment s = ofSegment s' := by
  simp only [ofSegment, Segment.HasValue, h _ (by decide : Feature.sonorant ∈ features),
    h _ (by decide : Feature.approximant ∈ features),
    h _ (by decide : Feature.consonantal ∈ features),
    h _ (by decide : Feature.syllabic ∈ features)]

/-- Setting a feature that sonority does not read leaves sonority unchanged. -/
theorem ofSegment_setFeature {f : Feature} (hf : f ∉ features) (s : Segment) (v : Bool) :
    ofSegment (s.setFeature f v) = ofSegment s :=
  ofSegment_congr fun g hg ↦ Segment.setFeature_apply_of_ne (s := s) (by rintro rfl; exact hf hg) v

@[simp] theorem ofSegment_toSegment (c : Sonority) : ofSegment c.toSegment = c := by
  cases c <;> decide

theorem apply_eq_toSegment_of_le {c : Sonority} {s : Segment} (h : c.toSegment ≤ s) {f : Feature}
    (hf : f ∈ features) : s f = c.toSegment f := by
  have key : ∀ c : Sonority, ∀ f ∈ features, ∃ v, c.toSegment f = some v := by decide
  obtain ⟨v, hv⟩ := key c f hf
  rw [hv]
  exact (Segment.le_iff_forall_hasValue s).1 h f v hv

/-- A segment with the values of a column of Table 4.1 has that column's sonority. -/
theorem ofSegment_eq_of_le {c : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    ofSegment s = c :=
  (ofSegment_congr fun _ hf ↦ apply_eq_toSegment_of_le h hf).trans (ofSegment_toSegment c)

/-- On a segment with the values of a column of Table 4.1, exactly that column's description
holds. -/
theorem description_le_iff {c c' : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    c'.description ≤ s ↔ c' = c := by
  have hsupp : ∀ c' : Sonority, ∀ f ∉ features, c'.description f = ⊥ := by decide
  have key : ∀ c c' : Sonority, c'.description ≤ c.toSegment ↔ c' = c := by decide
  rw [← key c c']
  refine forall_congr' fun f ↦ ?_
  by_cases hf : f ∈ features
  · rw [apply_eq_toSegment_of_le h hf]
  · simp [hsupp c' f hf]

theorem description_le_iff_ofSegment_eq {c c' : Sonority} {s : Segment} (h : c.toSegment ≤ s) :
    c'.description ≤ s ↔ ofSegment s = c' := by
  rw [description_le_iff h, ofSegment_eq_of_le h, eq_comm]

theorem ofSegment_setFeature_continuant (s : Segment) (v : Bool) :
    ofSegment (s.setFeature .continuant v) = ofSegment s :=
  ofSegment_setFeature (by decide) s v

/-- The sonority rise from `a` to `b` is positive when sonority rises, zero on a plateau,
and negative when it falls. -/
def rise (a b : Sonority) : ℤ := b.rank - a.rank

@[simp] theorem rise_self (a : Sonority) : rise a a = 0 := by simp only [rise]; omega

theorem neg_rise (a b : Sonority) : -rise a b = rise b a := by simp only [rise]; omega

theorem rise_add_rise (a b c : Sonority) : rise a b + rise b c = rise a c := by
  simp only [rise]; omega

@[simp] theorem rise_pos {a b : Sonority} : 0 < rise a b ↔ a < b := by
  change 0 < (b.rank : ℤ) - a.rank ↔ a.rank < b.rank; omega

@[simp] theorem rise_neg {a b : Sonority} : rise a b < 0 ↔ b < a := by
  change (b.rank : ℤ) - a.rank < 0 ↔ b.rank < a.rank; omega

@[simp] theorem rise_eq_zero {a b : Sonority} : rise a b = 0 ↔ a = b :=
  ⟨fun h ↦ rank_strictMono.injective (by simp only [rise] at h; omega),
    by rintro rfl; exact rise_self _⟩

end Sonority

namespace Sonority.Class

theorem parkerRank_injective : Function.Injective parkerRank := by
  intro a b h
  cases a <;> cases b <;> simp_all [parkerRank]

@[simp] theorem toSonority_ofSegment (s : Segment) :
    (ofSegment s).toSonority = Sonority.ofSegment s := by
  unfold ofSegment
  split <;> (try split_ifs) <;> simp_all [toSonority]

end Sonority.Class

end Phonology
