module

public import Linglib.Core.Computability.RegularExpressions
public import Mathlib.Data.Finset.Defs

/-!
# Position-class templates

In templatic morphology the formatives of a word fill a flat string of positions. A formative's
position is fixed by its formal category rather than by its scope, and fillers of the same
position cannot co-occur. Templatic and layered properties tend to hold of individual
formatives rather than of the whole string, so a template may contain a position whose fillers
stack, as the voice suffixes of the Turkish verb do.

An `AffixTemplate` lists the positions of a word's prefix string and of its suffix string, so
that a position's side is its place relative to the stem, and marks the positions whose
fillers stack. The strings of positions it admits, each filled at most once and in order
except the stacking ones, form a regular language. A string of exponents, each tagged with its
position, is licensed when its positions are admitted. A study that compares the positions
with a cross-linguistic order such as `Morphology.RelevanceHierarchy` maps them along a partial
map of its own.

## Main definitions

* `Morphology.AffixTemplate`: the prefix and suffix positions of a word and its stacking
  positions.
* `AffixTemplate.toRegularExpression`, `AffixTemplate.language`: the strings of positions a
  template admits.
* `AffixTemplate.Licensed`: the strings of exponents it admits.

## Main results

* `AffixTemplate.mem_language_of_sublist`: a string filling positions at most once, in order,
  is admitted.
* `AffixTemplate.mem_language_iff_sublist`: without stacking positions, those are the only
  admitted strings.

## Implementation notes

The template of prosodic morphology, a CV skeleton, is `Autosegmental.Skeleton`, matched in
`Morphology/Morphotactics/TemplateMatch.lean`.

## References

* [bickel-nichols-2007]
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

open RegularExpression in
/-- A position as a regular expression, admitting one filler at most, or any number if it
stacks. -/
def position (a : Slot) : RegularExpression Slot :=
  if a ∈ t.stacking then (char a).star else char a + 1

/-- The positions in order, each as `position`. -/
def toRegularExpression : RegularExpression Slot := t.slots.foldr (t.position · * ·) 1

/-- The strings of positions the template admits. -/
def language : Language Slot := t.toRegularExpression.matches'

instance : DecidablePred (· ∈ t.language) :=
  inferInstanceAs (DecidablePred (· ∈ t.toRegularExpression.matches'))

/-- A string of exponents, each tagged with its position, is licensed when its positions are
admitted. -/
def Licensed {E : Slot → Type*} (w : List (Σ σ, E σ)) : Prop := w.map Sigma.fst ∈ t.language

instance {E : Slot → Type*} : DecidablePred (t.Licensed (E := E)) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ t.language))

variable {t}

open List RegularExpression

private theorem nil_mem_position (a : Slot) : [] ∈ (t.position a).matches' := by
  unfold position; split_ifs
  · exact Language.nil_mem_kstar _
  · simp [Language.mem_add, Language.mem_one]

private theorem singleton_mem_position (a : Slot) : [a] ∈ (t.position a).matches' := by
  unfold position; split_ifs
  · exact Language.mem_kstar.mpr ⟨[[a]], by simp, fun y hy ↦ by
      rw [List.mem_singleton.mp hy, matches'_char]; exact Set.mem_singleton _⟩
  · rw [matches'_add, matches'_char]
    exact (Language.mem_add _ _ _).mpr (.inl (Set.mem_singleton _))

private theorem mem_foldr_of_sublist {l v : List Slot} (h : v <+ l) :
    v ∈ (l.foldr (t.position · * ·) 1).matches' := by
  induction l generalizing v with
  | nil => simpa [Language.mem_one] using h
  | cons a l ih =>
    rw [foldr_cons, matches'_mul, Language.mem_mul]
    rcases sublist_cons_iff.mp h with h | ⟨r, rfl, hr⟩
    · exact ⟨[], nil_mem_position a, v, ih h, rfl⟩
    · exact ⟨[a], singleton_mem_position a, r, ih hr, rfl⟩

/-- A string filling positions at most once, in order, is admitted. -/
theorem mem_language_of_sublist {v : List Slot} (h : v <+ t.slots) : v ∈ t.language :=
  mem_foldr_of_sublist h

/-- Without stacking positions, a string is admitted exactly when it fills positions at most
once, in order. -/
theorem mem_language_iff_sublist (h : t.stacking = ∅) {v : List Slot} :
    v ∈ t.language ↔ v <+ t.slots := by
  have : t.toRegularExpression = .sublists t.slots := by
    simp [toRegularExpression, position, h, RegularExpression.sublists]
  rw [language, this, mem_matches'_sublists]

end AffixTemplate

end Morphology
