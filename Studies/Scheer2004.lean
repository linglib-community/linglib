/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.StrictCV.Basic

/-!
# Scheer (2004): A lateral theory of phonology

Scheer's CVCV derives syllable structure from lateral relations among the positions of a strict
sequence of CV units. This file checks two of the book's patterns against the Strict CV
substrate. By Havlík's Law, every other yer of a run survives from Common Slavic into Old Czech,
counting from the right edge of the run, which proper government predicts since a governed
nucleus governs nothing. And Czech prefixes are vocalised before a root in zero grade but not
before a root that begins with a branching onset, since government passes over the empty nucleus
that a domain of infrasegmental government encloses.

## Main results

* `havlik`: in a word of yers alone, a yer survives exactly when its distance to the end is even.
* `se_psem`, `s_sevcem`: the two illustrations of Havlík's Law (304b).
* `pode_brat_podbradek`: a prefix is vocalised before *brat* and not before *bradek* (21).

## Implementation notes

A yer is a nucleus with floating melody: it is pronounced exactly when it is not governed, and,
not being empty, it is never enclosed in a domain of infrasegmental government. In Common Slavic,
Old Czech and Czech a final nucleus may be empty and does not govern. Only the nuclei of a word
are modelled.

## References

* [scheer-2004]
-/

@[expose] public section

namespace Scheer2004

open StrictCV

/-- A full vowel, whose melody is associated ((73a)). -/
def vowel : Nucleus := { melody := .associated }

/-- A yer, a vowel that alternates with zero, whose melody floats ((73b)). -/
def yer : Nucleus := { melody := .floating }

/-- A nucleus without melody ((73c)). -/
def empty : Nucleus := { melody := .empty }

/-! ### Havlík's Law -/

/-- The final nucleus of Common Slavic, Old Czech and Czech may be empty and does not govern. -/
def slavicFinal : FinalNucleus := ⟨true, false⟩

/-- In a word of yers alone, a yer survives iff its distance to the end of the word is even
((304a)). -/
theorem havlik (n : ℕ) :
    standard slavicFinal (List.replicate n yer) =
      (List.replicate n yer).mapIdx fun i x ↦ (x, decide (Even (n - i))) := by
  simpa using standard_append_of_floating (p := slavicFinal) (xs := List.replicate n yer)
    (ys := []) (fun x hx ↦ by rw [List.eq_of_mem_replicate hx]; exact ⟨rfl, rfl⟩)
    (.inr ⟨rfl, rfl, rfl⟩)

/-- Common Slavic *sъ pьs-ъmь* gives Old Czech *se psem* 'with the dog' ((304b)). -/
theorem se_psem :
    (standard slavicFinal (List.replicate 4 yer)).map Prod.snd = [true, false, true, false] := by
  decide

/-- Common Slavic *sъ šьv-ьc-ьmь* gives Old Czech *s ševcem* 'with the shoemaker' ((304b)). -/
theorem s_sevcem :
    (standard slavicFinal (List.replicate 5 yer)).map Prod.snd =
      [false, true, false, true, false] := by
  decide

/-! ### Czech prefixes -/

/-- The nuclei of *pode-brat* 'to seize from below' are *o*, the yer of the prefix, the
zero-grade yer between *b* and *r*, which could contract infrasegmental government, *a*, and
the final nucleus. -/
def podeBrat : List Nucleus := [vowel, yer, { yer with cluster := true }, vowel, empty]

/-- The nuclei of *podø-bradek* 'double chin' are *o*, the yer of the prefix, the empty nucleus of
the branching onset *br*, *a*, the yer of *-ek*, and the final nucleus. -/
def podBradek : List Nucleus := [vowel, yer, { empty with cluster := true }, vowel, yer, empty]

/-- The prefix is vocalised before *brat* but not before *bradek* ((21), §75). -/
theorem pode_brat_podbradek :
    (standard slavicFinal podeBrat).map Prod.snd = [true, true, false, true, false] ∧
      (standard slavicFinal podBradek).map Prod.snd = [true, false, false, true, true, false] := by
  decide

end Scheer2004
