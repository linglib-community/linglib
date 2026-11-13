/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.EmptyCategoryPrinciple

/-!
# Scheer (2004): A lateral theory of phonology

Scheer's CVCV derives syllable structure from lateral relations among the positions of a strict
sequence of CV units. This file checks three of the book's patterns against the Government
Phonology substrate. By Havlík's Law, [every other yer](##Scheer2004.havlik) of a run survives
from Common Slavic into Old Czech, counting from the right edge of the run, which proper
government predicts since a governed nucleus governs nothing. In Czech a final empty nucleus
governs an empty nucleus but not an alternating vowel, so that a word may
[end in two consonants](##Scheer2004.cert_pes) and yet the vowel of *pes* 'dog' is heard. And
Czech prefixes are [vocalised](##Scheer2004.pode_brat_podbradek) before a root in zero grade but
not before a root that begins with a branching onset.

## Implementation notes

A yer is a nucleus with floating melody: it is expressed exactly when it is not governed, and,
not being empty, it is never enclosed in a domain of infrasegmental government. Only the nuclei
of a word are modelled. Government is local, as the substrate has it: where the book lets the
vowel after a branching onset govern over the domain of infrasegmental government, here the
enclosed empty nucleus governs the nucleus before it. The two agree on which nuclei are
expressed in the forms of this file. Licensing plays no part in these alternations, and the
licensing abilities of the two settings are left off.

## References

* [scheer-2004]
* [brun-trigaud-scheer-2010]
-/

@[expose] public section

namespace Scheer2004

open GovernmentPhonology

/-- A full vowel, whose melody is associated ((73a)). -/
def vowel : Nucleus := { melody := .associated }

/-- A yer, a vowel that alternates with zero, whose melody floats ((73b)). -/
def yer : Nucleus := { melody := .floating }

/-- A nucleus without melody ((73c)). -/
def empty : Nucleus := { melody := .empty }

/-- Old Czech: an expressed yer governs another ((411)), and a final empty nucleus governs only
nuclei without melody ((378)). -/
def oldCzech : Actorship := .ltp ↑Melody.floating ↑Melody.empty false false false

/-- Modern Czech: an expressed yer does not govern ((411)), and a final empty nucleus governs
only nuclei without melody ((378)). -/
def czech : Actorship := .ltp ⊥ ↑Melody.empty false false false

/-! ### Havlík's Law -/

/-- In a word of yers alone, a yer survives iff its distance to the end of the word is even
((304a)). -/
theorem havlik (n i : ℕ) :
    (∃ x ∈ (obligatory oldCzech ∅ (List.replicate n yer))[i]?, x.expressed = true) ↔
      i < n ∧ Even (n - i) := by
  have h := expressed_obligatory_iff_even (A := oldCzech) (l := List.replicate n yer) (i := i)
    (fun x hx ↦ by rw [List.eq_of_mem_replicate hx]; rfl) rfl
    (fun x hm he ↦ by
      simpa [oldCzech, Actorship.ltp, he] using (by decide : Melody.empty < Melody.floating))
    (fun x hm he ↦ by simp [oldCzech, Actorship.ltp, he, hm])
  simpa using h

-- (304b): Common Slavic *sъ pьs-ъmь* gives Old Czech *se psem* 'with the dog'
theorem se_psem : (obligatory oldCzech ∅ (List.replicate 4 yer)).map (·.expressed) =
    [true, false, true, false] := by
  decide

-- (304b): Common Slavic *sъ šьv-ьc-ьmь* gives Old Czech *s ševcem* 'with the shoemaker'
theorem s_sevcem : (obligatory oldCzech ∅ (List.replicate 5 yer)).map (·.expressed) =
    [false, true, false, true, false] := by
  decide

/-! ### Final empty nuclei -/

/-- A final empty nucleus governs the empty nucleus of *čert* 'devil' but not the yer of *pes*
'dog' ((377)). -/
theorem cert_pes :
    (obligatory czech ∅ [vowel, empty, empty]).map (·.expressed) = [true, false, false] ∧
      (obligatory czech ∅ [yer, empty]).map (·.expressed) = [true, false] ∧
      Governs czech (obligatory czech ∅ [vowel, empty, empty]) 2 1 ∧
      ¬ Governs czech (obligatory czech ∅ [yer, empty]) 1 0 := by
  decide

/-! ### Czech prefixes -/

/-- The nuclei of *pode-brat* 'to seize from below' are *o*, the yer of the prefix, the
zero-grade yer between *b* and *r*, which could contract infrasegmental government, *a*, and
the final nucleus. -/
def podeBrat : List Nucleus := [vowel, yer, { yer with cluster := true }, vowel, empty]

/-- The nuclei of *podø-bradek* 'double chin' are *o*, the yer of the prefix, the empty nucleus of
the branching onset *br*, *a*, the yer of *-ek*, and the final nucleus. -/
def podBradek : List Nucleus := [vowel, yer, { empty with cluster := true }, vowel, yer, empty]

/-- The prefix is vocalised before *brat* but not before *bradek*: the zero-grade yer of *brat*
is governed and so governs nothing, while the empty nucleus of *br* is enclosed and governs the
yer of the prefix ((21), §75). -/
theorem pode_brat_podbradek :
    (obligatory czech ∅ podeBrat).map (·.expressed) = [true, true, false, true, false] ∧
      (obligatory czech ∅ podBradek).map (·.expressed) =
        [true, false, false, true, true, false] ∧
      Governs czech (obligatory czech ∅ podeBrat) 3 2 ∧
      ¬ Governed czech (obligatory czech ∅ podeBrat) 1 ∧
      Enclosed czech (obligatory czech ∅ podBradek) 2 ∧
      Governs czech (obligatory czech ∅ podBradek) 2 1 := by
  decide

end Scheer2004
