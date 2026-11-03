module

public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Mathlib.Data.Finset.Defs

/-!
# Position-class templates

In templatic morphology the formatives of a word fill a flat string of positions. A formative's
position can be determined by its formal category rather than by its function, and fillers of the
same position cannot co-occur. These properties tend to hold of individual formatives rather than
of the whole string, so a template may contain a position whose fillers stack, as the voice
suffixes of the Turkish verb do.

An `AffixTemplate` lists the positions of a word's prefixes and of its suffixes and marks those
that stack. It admits [the strings over its positions, in their order, in which only stacking
positions repeat](##language). Each position may be skipped, so these strings are [closed under
dropping a filler](##isSublistClosed_language) and [regular](##isRegular_language). Order and
repetition are conditions on pairs, so they are also [strictly
2-piecewise](##isStrictlyPiecewise_language). A string of exponents, each tagged with its
position, is licensed when its positions are admitted.

## Implementation notes

A template can forbid a filler but not require one, the limit of strictly piecewise grammars, so a
dependency between fillers is a further condition in the citing grammar. The template of prosodic
morphology, a CV skeleton, is `Autosegmental.Skeleton`, matched in
`Morphology/Morphotactics/TemplateMatch.lean`.

## References

* [bickel-nichols-2007]
* [aksenova-graf-moradi-2016]
-/

@[expose] public section

namespace Morphology

/-- A word's position-class template, over the positions `Slot`. Slots are tags, not exponents:
the exponents of each position live in the citing grammar. -/
structure AffixTemplate (Slot : Type*) where
  /-- The prefix positions, word-edge inward. -/
  prefixSlots : List Slot := []
  /-- The suffix positions, stem-outward. -/
  suffixSlots : List Slot := []
  /-- The positions whose fillers stack, any number of them in one word. -/
  stacking : Finset Slot := ∅

namespace AffixTemplate

variable {Slot : Type*} (t : AffixTemplate Slot)

/-- The positions in linear order, the stem left out. -/
def slots : List Slot := t.prefixSlots ++ t.suffixSlots

variable [DecidableEq Slot]

/-- The strings of positions the template admits: those over its positions, in their order, in
which only stacking positions repeat. -/
def language : Language Slot :=
  {v | (v.map t.slots.idxOf).SortedLE ∧ ∀ a ∈ v, a ∈ t.slots ∧ (a ∈ t.stacking ∨ v.count a ≤ 1)}

instance : DecidablePred (· ∈ t.language) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A string of exponents, each tagged with its position, is licensed when its positions are
admitted. -/
def Licensed {E : Slot → Type*} (w : List (Σ σ, E σ)) : Prop := w.map Sigma.fst ∈ t.language

instance {E : Slot → Type*} : DecidablePred (t.Licensed (E := E)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ t.language))

variable {t} {v : List Slot}

open List

/-- Dropping a filler keeps a string admitted. -/
theorem isSublistClosed_language : t.language.IsSublistClosed := fun _ _ hvw ⟨hs, h⟩ ↦
  ⟨(hs.pairwise.sublist (hvw.map _)).sortedLE, fun a ha ↦
    (h a (hvw.subset ha)).imp_right (Or.imp_right (hvw.count_le a).trans)⟩

theorem isRegular_language [Finite Slot] : t.language.IsRegular :=
  isSublistClosed_language.isRegular

/-- A template is a condition on pairs: a string is admitted when each of its fillers and each
ordered pair of them is. -/
theorem isStrictlyPiecewise_language : t.language.IsStrictlyPiecewise 2 := by
  refine ⟨t.language, Set.ext fun v ↦ ⟨fun h ↦ ?_, fun h s _ hs ↦ isSublistClosed_language hs h⟩⟩
  replace h : ∀ s, s.length ≤ 2 → s <+ v → s ∈ t.language := h
  refine ⟨?_, fun a ha ↦ ⟨(h [a] (by simp) (singleton_sublist.2 ha)).2 a (by simp) |>.1, ?_⟩⟩
  · rw [sortedLE_iff_pairwise, pairwise_map, pairwise_iff_forall_sublist]
    intro a b hab
    simpa [sortedLE_iff_pairwise] using (h [a, b] (by simp) hab).1
  · refine or_iff_not_imp_left.2 fun hs ↦ not_lt.1 fun hc ↦ ?_
    have h2 : replicate 2 a <+ v := replicate_sublist_iff.2 hc
    simpa [hs] using ((h _ (by simp) h2).2 a (by simp)).2

/-- Without stacking positions, a string is admitted exactly when it fills positions at most
once, in order. -/
theorem mem_language_iff_sublist (ht : t.slots.Nodup) (h : t.stacking = ∅) :
    v ∈ t.language ↔ v <+ t.slots := by
  have hle : t.slots.Pairwise (t.slots.idxOf · ≤ t.slots.idxOf ·) :=
    pairwise_iff_getElem.2 fun i j hi hj hij ↦ by
      rw [ht.idxOf_getElem, ht.idxOf_getElem]; exact hij.le
  refine ⟨fun ⟨hs, hv⟩ ↦ ?_, fun hv ↦ ⟨((pairwise_map.2 hle).sublist (hv.map _)).sortedLE,
    fun a ha ↦ ⟨hv.subset ha, .inr ((hv.count_le a).trans (nodup_iff_count_le_one.1 ht a))⟩⟩⟩
  have hnd : v.Nodup := nodup_iff_count_le_one.2 fun a ↦ by
    by_cases ha : a ∈ v
    · simpa [h] using (hv a ha).2
    · simp [count_eq_zero_of_not_mem ha]
  obtain ⟨w, hwv, hw⟩ := subperm_of_subset hnd fun a ha ↦ (hv a ha).1
  refine hwv.eq_of_pairwise (fun a b ha hb hab hba ↦ ?_) (hle.sublist hw)
    (pairwise_map.1 (sortedLE_iff_pairwise.1 hs)) ▸ hw
  exact (idxOf_inj (hw.subset ha)).1 (le_antisymm hab hba)

end AffixTemplate

end Morphology
