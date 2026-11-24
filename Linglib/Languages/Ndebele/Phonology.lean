module

public import Linglib.Data.PHOIBLE.Inventories.Ndebele
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Ndebele phonemes

This file lists the phonemes of Northern Ndebele that the agreement prefixes are built from and
gives each its segment. The language has the five vowels /i e a o u/ of the Nguni group; of its
consonants only /s/ and /l/ are here. The feature values of a phoneme are not listed. Each
phoneme names its glyph in the PHOIBLE chart, and its segment is the segment of that chart entry.

## Main definitions

* `Ndebele.a`, `Ndebele.s` and the like: the phonemes, as segments of their chart entries.
* `Ndebele.inventory`: the set of them.

## Main results

* `Ndebele.subset_nde`: the phonemes are segments of PHOIBLE's Ndebele inventory.
* `Ndebele.isVowel_iff`: the five vowels are the vowels.

## Implementation notes

PHOIBLE's inventory writes the low vowel `ɑ`, and that is the chart entry taken here.

## TODO

* The remaining consonants of the inventory, the clicks and the prenasalized series among them.

## References

* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Ndebele

/-! ### Phonemes -/

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The low vowel /a/, the glyph `ɑ` of the Ndebele inventory. -/
def a : Segment := .ofChart .«ɑ»

/-- The mid back rounded vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The high back rounded vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The lateral /l/. -/
def l : Segment := .ofChart .«l»

/-- The Ndebele phonemes of the agreement prefixes, pairwise distinct. -/
def inventory : Finset Segment := ⟨↑[i, e, a, o, u, s, l], by decide⟩

/-- The phonemes are segments of PHOIBLE's Ndebele inventory. -/
theorem subset_nde : inventory ⊆ Inventories.Ndebele.nde.segments :=
  Inventory.subset_segments_iff.2 (by decide)

theorem isVowel_iff :
    ∀ x ∈ inventory, x.IsVowel ↔ x ∈ ({i, e, a, o, u} : Finset Segment) := by
  decide

end Ndebele
