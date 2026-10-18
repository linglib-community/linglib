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

/-! ### Havlík's Law -/

/-- The final nucleus of Common Slavic, Old Czech and Czech may be empty and does not govern. -/
def slavicFinal : FinalNucleus := ⟨true, false⟩

/-- In a word of yers alone, a yer survives iff its distance to the end of the word is even, so that
every other yer survives, counting from the right edge of the sequence ((304a)). -/
theorem havlik {n : ℕ} (x : Fin n) :
    x ∈ standard slavicFinal ({ full := ∅ } : Profile n) ↔ Even (n - x.val) :=
  mem_standard_iff_even_of_final (b := ⟨0, Nat.zero_lt_of_lt x.isLt⟩) rfl rfl
    (fun _ _ ↦ ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _⟩)
    (Fin.le_def.2 (Nat.zero_le _))

/-- Common Slavic *sъ pьs-ъmь* gives Old Czech *se psem* 'with the dog', in which the second and
fourth of its four yers from the right survive ((304b)). -/
theorem se_psem : standard slavicFinal ({ full := ∅ } : Profile 4) = {0, 2} := by
  decide

/-- Common Slavic *sъ šьv-ьc-ьmь* gives Old Czech *s ševcem* 'with the shoemaker', in which the
second and fourth of its five yers from the right survive ((304b)). -/
theorem s_sevcem : standard slavicFinal ({ full := ∅ } : Profile 5) = {1, 3} := by
  decide

/-! ### Czech prefixes -/

/-- The nuclei of *pode-brat* 'to seize from below' are *o*, the yer of the prefix, the zero-grade
yer between *b* and *r*, *a*, and the final nucleus. -/
def podeBrat : Profile 5 := { full := {0, 3} }

/-- The nuclei of *podø-bradek* 'double chin' are *o*, the yer of the prefix, the empty nucleus of
the branching onset *br*, *a*, the yer of *-ek*, and the final nucleus. -/
def podBradek : Profile 6 := { full := {0, 3}, cluster := {2} }

/-- Before *brat* the prefix is vocalised, since the root's zero-grade yer needs government from
*a*, which therefore cannot reach the prefix. Before *bradek* it is not, since the empty nucleus of
*br* is enclosed in a domain of infrasegmental government, government passes over it, and *a*
governs the prefix ((21), §75). -/
theorem pode_brat_podbradek :
    standard slavicFinal podeBrat = {0, 1, 3} ∧ standard slavicFinal podBradek = {0, 3, 4} := by
  decide

end Scheer2004
