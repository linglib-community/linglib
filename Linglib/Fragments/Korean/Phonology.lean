module

public import Linglib.Data.PHOIBLE.Inventories.Korean
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Korean stop nasalization

A Korean stop becomes the nasal of its place before a nasal, so that morpheme-final /p t k/
and /m n ŋ/, which contrast in *pak* 'gourd' and *paŋ* 'room', are pronounced alike before a
nasal: *tɕakɨn-pak nɛmsɛ-ka* 'the smell of a small gourd' and *tɕakɨn-paŋ nɛmsɛ-ka* 'the
smell of a small room' are the same string of sounds, Hayes's illustration of neutralization.
Hayes writes the rule as the change of a non-affricate stop to a voiced nasal sonorant before
a nasal, leaving its place alone, and that is how it is written here.

The phonemes are the ones the rule needs, and each takes its feature values from its glyph in
the PHOIBLE chart. There a stop and the nasal of its place differ in the three features the
rule writes and in [delayed release], which is minus on a stop and not applicable on a nasal.
The rule's output is therefore the nasal on every feature but [delayed release], and no two
phonemes differ in that feature alone.

## Main definitions

* `Korean.p`, `Korean.ŋ` and the like: the phonemes of the illustration, as segments.
* `Korean.inventory`: the set of them.
* `Korean.stopNasalization`: a non-affricate stop becomes a voiced nasal sonorant before a
  nasal.

## Main results

* `Korean.subset_kor`: the phonemes are segments of PHOIBLE's Korean inventory.
* `Korean.pak_paŋ_neutralized`: *pak* and *paŋ* before *n* derive the same string, the one
  with the velar nasal on every feature but [delayed release]; *pak* alone is unchanged.
* `Korean.derive_pak_ne_paŋ`: the derived string is not literally the one with the velar
  nasal, since the rule leaves [−delayed release] in place.
* `Korean.isDistinctive_compl_delayedRelease`: the features other than [delayed release]
  distinguish the phonemes.

## References

* [hayes-2009]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace Korean

/-! ### Phonemes -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiceless alveolar stop /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal /n/. -/
def n : Segment := .ofChart .«n»

/-- The velar nasal /ŋ/. -/
def ŋ : Segment := .ofChart .«ŋ»

/-- The low vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The phonemes of Hayes's illustration are the plain stops, the nasals, three vowels and the
lateral, and they are pairwise distinct. -/
def inventory : Finset Segment := ⟨↑[p, t, k, m, n, ŋ, a, i, u, l], by decide⟩

theorem subset_kor : inventory ⊆ Inventories.Korean.kor.segments :=
  Inventory.subset_segments_iff.2 (by decide)

/-! ### The rule -/

/-- A non-affricate stop becomes a voiced nasal sonorant before a nasal. -/
def stopNasalization : Rule where
  target := Segment.ofSpecs [(.delayedRelease, false)]
  effect := .changeFeatures (Segment.ofSpecs [(.nasal, true), (.voice, true), (.sonorant, true)])
  rightContext := [.seg (Segment.ofSpecs [(.nasal, true)])]

/-- The features other than [delayed release]. -/
def exceptDelayedRelease : Finset Phonology.Feature := {.delayedRelease}ᶜ

theorem isDistinctive_compl_delayedRelease :
    IsDistinctive exceptDelayedRelease inventory := by
  decide

theorem pak_paŋ_neutralized :
    (derive [stopNasalization] [p, a, k, n]).map (Segment.restrict exceptDelayedRelease) =
        [p, a, ŋ, n].map (Segment.restrict exceptDelayedRelease) ∧
      derive [stopNasalization] [p, a, ŋ, n] = [p, a, ŋ, n] ∧
      derive [stopNasalization] [p, a, k] = [p, a, k] := by
  decide

theorem derive_pak_ne_paŋ :
    derive [stopNasalization] [p, a, k, n] ≠ [p, a, ŋ, n] := by
  decide

end Korean
