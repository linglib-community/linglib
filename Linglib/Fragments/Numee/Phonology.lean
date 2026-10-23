/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Drubea.Phonology

/-!
# Numèè segments

The consonants and vowels of Numèè (Glottocode nucl1484), the Goro-dialect sister of Drubea
in the Far South of Grande Terre, as [lionnet-2025] tabulates them after [rivierre-1973].
The two inventories are the same but for two points: Numèè has the labialised velar nasal
/ŋw/ where Drubea has /gw/, and it adds three front rounded vowel qualities, which occur
long only. The shared segments are those of `Fragments/Drubea/Phonology`.

## Main definitions

* `Numee.ŋw`, `Numee.ü`, `Numee.ø`, `Numee.øNasal`: the segments Drubea lacks.
* `Numee.consonants`, `Numee.vowels`, `Numee.inventory`.

## Main results

* `Numee.consonants_eq`, `Numee.vowels_eq`: the inventories differ from Drubea's by exactly
  the segments named.

## References

* [lionnet-2025]
* [rivierre-1973]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE Drubea

namespace Numee

/-- /ŋw/, the labialised velar nasal; Numèè only, where Drubea has /gw/. -/
def ŋw : Segment := .ofChart .«ŋ» labialized

/-- /ü/, phonetically [y]; long only. -/
def ü : Segment := .ofChart .«y»

/-- /ø/, long only. -/
def ø : Segment := .ofChart .«ø»

/-- /ø̃/, long only. -/
def øNasal : Segment := .ofChart .«ø̃»

/-- The consonants ((1) of [lionnet-2025]). -/
def consonants : Finset Segment :=
  ⟨↑[p, pw, t, tRetroflex, c, k, kw, b, bw, d, dRetroflex, j, g, m, mw, n, nRetroflex,
      nPalatal, ŋ, ŋw, v, x, rRetroflex, y, w], by decide⟩

/-- The vowels ((2) of [lionnet-2025]). -/
def vowels : Finset Segment :=
  ⟨↑[i, ü, u, e, smallCapitalI, upsilon, openE, ø, o, a, iNasal, uNasal, eNasal, øNasal,
      oNasal, aNasal], by decide⟩

/-- The phonemes. -/
def inventory : Finset Segment := consonants ∪ vowels

/-- The consonants are Drubea's with /ŋw/ for /gw/. -/
theorem consonants_eq : consonants = insert ŋw (Drubea.consonants.erase gw) := by decide

/-- The vowels are Drubea's with the three front rounded qualities. -/
theorem vowels_eq : vowels = Drubea.vowels ∪ {ü, ø, øNasal} := by decide

end Numee
