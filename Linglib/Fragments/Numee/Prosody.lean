/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Numee.Phonology
public import Linglib.Fragments.Drubea.Prosody

/-!
# Numèè register

The stems of Numèè with their register tiers, as [lionnet-2025] transcribes them after
[rivierre-1973] and the Haudricourt–Rivierre recordings, in the representation of
`Fragments/Drubea/Prosody`: syllables, and on each mora the downstep it bears or nothing.
Numèè shares Drubea's register system; the two diverge only at the utterance-final
boundary, whose Numèè condition is stated in `Studies/Lionnet2025`. The entries are the
stems, affixes and pronouns of the utterances the source transcribes with pitch levels;
each docstring gives the example number.

## Main results

* `Numee.stems_aligned`, `Numee.affixes_aligned`: every tier has one entry per mora.

## References

* [lionnet-2025]
* [rivierre-1973]
-/

@[expose] public section

open Phonology Tone
open Prosody (Syllable)
open Drubea (cv cvv a e i o u openE upsilon iNasal eNasal oNasal aNasal b c d g j k kw m mw n
  nPalatal nRetroflex p rRetroflex t v w y)

namespace Numee

/-! ### Stems -/

/-- /jaa/ 'juice' ((24), (25)). -/
def jaaJuice : Registered Syllable := ⟨[cvv [j] a], [[], []]⟩

/-- /ɲĩ/ 'coconut' ((24)). -/
def niCoconut : Registered Syllable := ⟨[cv [nPalatal] iNasal], [[]]⟩

/-- /ꜜɲĩ/ 'breast' ((25)). -/
def niBreast : Registered Syllable := ⟨[cv [nPalatal] iNasal], [[.downstep]]⟩

/-- /ɲĩ/ 3SG.SBJ ((29)). -/
def ni3sg : Registered Syllable := ⟨[cv [nPalatal] iNasal], [[]]⟩

/-- /dɛ.ɳu/ 'jaw' ((22); (26) prints the second vowel as /ʊ/). -/
def denuJaw : Registered Syllable := ⟨[cv [d] openE, cv [nRetroflex] u], [[], []]⟩

/-- /a/ REL ((22), (26)). -/
def aRel : Registered Syllable := ⟨[cv [] a], [[]]⟩

/-- /ɳa/ 'up' ((22)). -/
def naUp : Registered Syllable := ⟨[cv [nRetroflex] a], [[]]⟩

/-- /mii/ 'low' ((26)). -/
def miiLow : Registered Syllable := ⟨[cvv [m] i], [[], []]⟩

/-- /ꜜtẽẽ/ 'girl' ((28)). -/
def teeGirl : Registered Syllable := ⟨[cvv [t] eNasal], [[.downstep], []]⟩

/-- /nõ/ 'grill' ((28)). -/
def noGrill : Registered Syllable := ⟨[cv [n] oNasal], [[]]⟩

/-- /bɛ.ꜜtĩĩ/ 'three' ((28)). -/
def betiiThree : Registered Syllable :=
  ⟨[cv [b] openE, cvv [t] iNasal], [[], [.downstep], []]⟩

/-- /ku/ 'yam' ((28)). -/
def kuYam : Registered Syllable := ⟨[cv [k] u], [[]]⟩

/-- /yʊʊ/ 'berth' ((29)). -/
def yuuBerth : Registered Syllable := ⟨[cvv [y] upsilon], [[], []]⟩

/-- /ꜜpaa/ 'up' ((29)). -/
def paaUp : Registered Syllable := ⟨[cvv [p] a], [[.downstep], []]⟩

/-- /kwẽ/ 'sand' ((29)). -/
def kweSand : Registered Syllable := ⟨[cv [kw] eNasal], [[]]⟩

/-- /yaꜜa/ NEG ((52)). -/
def yaaNeg : Registered Syllable := ⟨[cvv [y] a], [[], [.downstep]]⟩

/-- /ꜜmẽ/ 'that' ((52)). -/
def meThat : Registered Syllable := ⟨[cv [m] eNasal], [[.downstep]]⟩

/-- /geꜜe/ 1PL.EXCL.SBJ ((52)). -/
def gee1plExcl : Registered Syllable := ⟨[cvv [g] e], [[], [.downstep]]⟩

/-- /ꜜmẽ/ FUT ((52)). -/
def meFut : Registered Syllable := ⟨[cv [m] eNasal], [[.downstep]]⟩

/-- /ɲa.ꜜi/ 'arrive' ((52)), a disyllable whose downstep is not displaced. -/
def nyaiArrive : Registered Syllable := ⟨[cv [nPalatal] a, cv [] i], [[], [.downstep]]⟩

/-- /ꜜɳe/ 3PL.SBJ ((18)). -/
def ne3pl : Registered Syllable := ⟨[cv [nRetroflex] e], [[.downstep]]⟩

/-- /ꜜmwa/ PFV ((18); (38) prints it nasalised). -/
def mwaPfv : Registered Syllable := ⟨[cv [mw] a], [[.downstep]]⟩

/-- /ꜜve/ 'go' ((18)). -/
def veGo : Registered Syllable := ⟨[cv [v] e], [[.downstep]]⟩

/-- /ꜜcĩĩ.bu/ 'rat' ((38)). -/
def ciibuRat : Registered Syllable :=
  ⟨[cvv [c] iNasal, cv [b] u], [[.downstep], [], []]⟩

/-- /ꜜku/ 'flee' ((38)). -/
def kuFlee : Registered Syllable := ⟨[cv [k] u], [[.downstep]]⟩

/-- /mwo.ɽo/ 'alive' ((38)). -/
def mworoAlive : Registered Syllable :=
  ⟨[cv [mw] o, cv [rRetroflex] o], [[], []]⟩

/-- /gu/ 2SG.SBJ ((62)). -/
def gu2sg : Registered Syllable := ⟨[cv [g] u], [[]]⟩

/-- /ꜜca.pɛ/ 'raise' ((62)). -/
def capeRaise : Registered Syllable := ⟨[cv [c] a, cv [p] openE], [[.downstep], []]⟩

/-- /ꜜpa.ɳaa/ 'mast' ((62)). -/
def panaaMast : Registered Syllable :=
  ⟨[cv [p] a, cvv [nRetroflex] a], [[.downstep], [], []]⟩

/-- /ꜜko/ 'on' ((62)). -/
def koOn : Registered Syllable := ⟨[cv [k] o], [[.downstep]]⟩

/-- /ɲʊ/ 'boat' ((62)). -/
def nyuBoat : Registered Syllable := ⟨[cv [nPalatal] upsilon], [[]]⟩

/-- /ꜜwii/ 'down' ((62)). -/
def wiiDown : Registered Syllable := ⟨[cvv [w] i], [[.downstep], []]⟩

/-- /to/ 'there' ((62)). -/
def toThere : Registered Syllable := ⟨[cv [t] o], [[]]⟩

/-! ### Affixes -/

/-- The suffix -ꜜẽ PROX ((28)), transcribed downstepped. -/
def eProx : Registered Syllable := ⟨[cv [] eNasal], [[.downstep]]⟩

/-- The prefix a- LOC ((29)). -/
def aLoc : Registered Syllable := ⟨[cv [] a], [[]]⟩

/-! ### The lists -/

/-- The stems. -/
def stems : List (Registered Syllable) :=
  [jaaJuice, niCoconut, niBreast, ni3sg, denuJaw, aRel, naUp, miiLow, teeGirl, noGrill,
    betiiThree, kuYam, yuuBerth, paaUp, kweSand, yaaNeg, meThat, gee1plExcl, meFut, nyaiArrive,
    ne3pl, mwaPfv, veGo, ciibuRat, kuFlee, mworoAlive, gu2sg, capeRaise, panaaMast, koOn,
    nyuBoat, wiiDown, toThere]

/-- The affixes. -/
def affixes : List (Registered Syllable) := [eProx, aLoc]

/-- Every stem's tier has one entry per mora. -/
theorem stems_aligned : ∀ s ∈ stems, s.IsAligned Prosody.Syllable.pnatMoraCount := by decide

theorem affixes_aligned : ∀ s ∈ affixes, s.IsAligned Prosody.Syllable.pnatMoraCount := by decide

end Numee
