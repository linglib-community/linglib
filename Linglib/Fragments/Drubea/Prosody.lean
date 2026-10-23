/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Drubea.Phonology
public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Phonology.Tone.Register

/-!
# Drubea register

The stems of Drubea with their register tiers, as [lionnet-2025] transcribes them after
[rivierre-1973] and [shintani-paita-1990b]. A stem is its syllables and, on each mora, the
register nodes it bears: none, or the downstep `[-raised]` (`Tone.TRN.downstep`, the
source's `l`). No stem bears a tone feature or an upstep. The postlexical upstep, the
boundary features, register copying and the three stem patterns the tiers instantiate are
the analysis and live in `Studies/Lionnet2025`.

The entries are the source's minimal pairs and triplets, its illustrations of stem shape,
and the stems, affixes and function words of the glossed utterances it transcribes with
pitch levels; each docstring gives the example number. Where one syllable string carries
several tiers, the entries are named by gloss. The stem is the source's free-standing
monomorphemic lexical item, so pronouns and markers are stems and affixes are listed apart;
compounds are built from their members in the study. Loanwords, whose syllable-internal
downstep falls in a non-final syllable, are listed apart. Unlike vowels in sequence are
heterosyllabic and like vowels a long vowel, following the source. `cv` and `cvv` are a
light and a heavy open syllable.

## Main results

* `Drubea.stems_aligned`, `Drubea.affixes_aligned`, `Drubea.loans_aligned`: every tier has
  one entry per mora.
* `Drubea.smallCapitalI_heavy`: the lax front vowel heads only bimoraic syllables.

## References

* [lionnet-2025]
* [rivierre-1973]
* [shintani-paita-1990b]
-/

@[expose] public section

open Phonology Tone
open Prosody (Syllable)

namespace Drubea

/-- A light open syllable, (C)V. -/
abbrev cv (onset : List Segment) (v : Segment) : Prosody.Syllable := .ofVowel onset v

/-- A heavy open syllable, (C)VV, its long vowel two morae. -/
abbrev cvv (onset : List Segment) (v : Segment) : Prosody.Syllable := .ofLongVowel onset v

/-! ### Monosyllabic minimal pairs ((4)) -/

/-- /ĩ/ 'extremity, tip' ((3a), (4a)). -/
def iTip : Registered Syllable := ⟨[cv [] iNasal], [[]]⟩

/-- /ꜜĩ/ 'piece, bit' ((4a)). -/
def iPiece : Registered Syllable := ⟨[cv [] iNasal], [[.downstep]]⟩

/-- /ɪɪ/ 'indigenous bamboo' ((4b)). -/
def iiBamboo : Registered Syllable := ⟨[cvv [] smallCapitalI], [[], []]⟩

/-- /ꜜɪɪ/ 'Elaeocarpus angustifolius, tree sp.' ((4b)). -/
def iiElaeocarpus : Registered Syllable := ⟨[cvv [] smallCapitalI], [[.downstep], []]⟩

/-- /be/ 'death; to die' ((3a), (4c)). -/
def beDie : Registered Syllable := ⟨[cv [b] e], [[]]⟩

/-- /ꜜbe/ 'Melaleuca quinquenervia, niaouli' ((4c)). -/
def beNiaouli : Registered Syllable := ⟨[cv [b] e], [[.downstep]]⟩

/-- /ɖoo/ 'bag, envelope' ((4d)). -/
def dooBag : Registered Syllable := ⟨[cvv [dRetroflex] o], [[], []]⟩

/-- /ꜜɖoo/ 'Cordyline spp., plant sp.' ((4d)). -/
def dooCordyline : Registered Syllable := ⟨[cvv [dRetroflex] o], [[.downstep], []]⟩

/-- /cu/ 'to wipe' ((4e)). -/
def cuWipe : Registered Syllable := ⟨[cv [c] u], [[]]⟩

/-- /ꜜcu/ 'to knock down with a pole' ((4e)). -/
def cuKnock : Registered Syllable := ⟨[cv [c] u], [[.downstep]]⟩

/-- /ɲi/ 'coconut tree' ((4f)). -/
def niCoconut : Registered Syllable := ⟨[cv [nPalatal] i], [[]]⟩

/-- /ꜜɲi/ 'breast' ((4f)). -/
def niBreast : Registered Syllable := ⟨[cv [nPalatal] i], [[.downstep]]⟩

/-- /kee/ 'husband' ((4g), (45d)). -/
def keeHusband : Registered Syllable := ⟨[cvv [k] e], [[], []]⟩

/-- /ꜜkee/ 'Broussonetia papyrifera, paper mulberry' ((4g), (45d)). -/
def keeMulberry : Registered Syllable := ⟨[cvv [k] e], [[.downstep], []]⟩

/-! ### CVꜜV triplets ((45)) -/

/-- /beꜜe/ NEGATION ((45a), (46)). -/
def beeNeg : Registered Syllable := ⟨[cvv [b] e], [[], [.downstep]]⟩

/-- /bee/ 'fish' ((45a), (19)). -/
def beeFish : Registered Syllable := ⟨[cvv [b] e], [[], []]⟩

/-- /ꜜbee/ 'descendance' ((45a)). -/
def beeDescendance : Registered Syllable := ⟨[cvv [b] e], [[.downstep], []]⟩

/-- /pwaꜜa/ 'group of men' ((45b), (50)). -/
def pwaaMen : Registered Syllable := ⟨[cvv [pw] a], [[], [.downstep]]⟩

/-- /pwaa/ 'white' ((45b)). -/
def pwaaWhite : Registered Syllable := ⟨[cvv [pw] a], [[], []]⟩

/-- /ꜜpwaa/ 'packet' ((45b)). -/
def pwaaPacket : Registered Syllable := ⟨[cvv [pw] a], [[.downstep], []]⟩

/-- /koꜜo/ 'place, field' ((45c), (53)). -/
def kooPlace : Registered Syllable := ⟨[cvv [k] o], [[], [.downstep]]⟩

/-- /koo/ 'fish sp.' ((45c)). -/
def kooFish : Registered Syllable := ⟨[cvv [k] o], [[], []]⟩

/-- /ꜜkoo/ 'egg' ((45c)). -/
def kooEgg : Registered Syllable := ⟨[cvv [k] o], [[.downstep], []]⟩

/-- /keꜜe/ 1PL.SBJ ((45d), (21)). -/
def kee1pl : Registered Syllable := ⟨[cvv [k] e], [[], [.downstep]]⟩

/-- /kãꜜã/ PROSPECTIVE ((45e), (10)). -/
def kaaProspective : Registered Syllable := ⟨[cvv [k] aNasal], [[], [.downstep]]⟩

/-- /kãã/ 'parent, friend' ((45e)). -/
def kaaParent : Registered Syllable := ⟨[cvv [k] aNasal], [[], []]⟩

/-- /ꜜkãã/ 'big' ((45e)). -/
def kaaBig : Registered Syllable := ⟨[cvv [k] aNasal], [[.downstep], []]⟩

/-! ### Stem shapes ((3)) and the disyllabic triplet ((34)) -/

/-- /boo/ 'blind' ((3b)). -/
def booBlind : Registered Syllable := ⟨[cvv [b] o], [[], []]⟩

/-- /ʊʊ/ 'net' ((3b)). -/
def uuNet : Registered Syllable := ⟨[cvv [] upsilon], [[], []]⟩

/-- /ku.ɽe/ 'forest, bush' ((3c), (34a)): registerless, type 1. -/
def kureForest : Registered Syllable := ⟨[cv [k] u, cv [rRetroflex] e], [[], []]⟩

/-- /ꜜku.ɽe/ 'end' ((34b)): downstepped initial syllable, type 2. -/
def kureEnd : Registered Syllable := ⟨[cv [k] u, cv [rRetroflex] e], [[.downstep], []]⟩

/-- /ku.ꜜɽe/ 'crayfish' ((34c)): downstepped second syllable, type 3. -/
def kureCrayfish : Registered Syllable := ⟨[cv [k] u, cv [rRetroflex] e], [[], [.downstep]]⟩

/-- /i.ꜜya/ 'to fish' ((3c)). -/
def iyaFish : Registered Syllable := ⟨[cv [] i, cv [y] a], [[], [.downstep]]⟩

/-- /kwi.e/ 'wind' ((3c)). -/
def kwieWind : Registered Syllable := ⟨[cv [kw] i, cv [] e], [[], []]⟩

/-- /i.a/ 'declare war' ((3c)). -/
def iaWar : Registered Syllable := ⟨[cv [] i, cv [] a], [[], []]⟩

/-- /pwẽẽ.ɖi/ 'youngest son' ((3d)). -/
def pweendiSon : Registered Syllable := ⟨[cvv [pw] eNasal, cv [dRetroflex] i], [[], [], []]⟩

/-- /ũũ.ɽe/ 'moon' ((3d)). -/
def uureMoon : Registered Syllable := ⟨[cvv [] uNasal, cv [rRetroflex] e], [[], [], []]⟩

/-- /wã.ɽee/ 'liana' ((3e)). -/
def wareeLiana : Registered Syllable := ⟨[cv [w] aNasal, cvv [rRetroflex] e], [[], [], []]⟩

/-- /u.tii/ 'go home' ((3e)). -/
def utiiHome : Registered Syllable := ⟨[cv [] u, cvv [t] i], [[], [], []]⟩

/-- /be.ii/ 'be jealous' ((3e)). -/
def beiiJealous : Registered Syllable := ⟨[cv [b] e, cvv [] i], [[], [], []]⟩

/-- /vẽẽ.too/ 'fish sp.' ((3f)). -/
def veentooFish : Registered Syllable := ⟨[cvv [v] eNasal, cvv [t] o], [[], [], [], []]⟩

/-! ### Verbs and nouns of the glossed utterances -/

/-- /veto/ 'put' ((35)). -/
def vetoPut : Registered Syllable := ⟨[cv [v] e, cv [t] o], [[], []]⟩

/-- /te.a/ 'to go up' ((36)). -/
def teaGoUp : Registered Syllable := ⟨[cv [t] e, cv [] a], [[], []]⟩

/-- /mweɽe/ 'again' ((36)). -/
def mwereAgain : Registered Syllable := ⟨[cv [mw] e, cv [rRetroflex] e], [[], []]⟩

/-- /kapwa/ 'corrugated iron' ((37)). -/
def kapwaIron : Registered Syllable := ⟨[cv [k] a, cv [pw] a], [[], []]⟩

/-- /ꜜʈobe/ 'wake up' ((39)). -/
def tobeWake : Registered Syllable := ⟨[cv [tRetroflex] o, cv [b] e], [[.downstep], []]⟩

/-- /ꜜŋɛɽɛ/ 'think' ((40)). -/
def ngereThink : Registered Syllable := ⟨[cv [ŋ] openE, cv [rRetroflex] openE], [[.downstep], []]⟩

/-- /ꜜbeɽu/ 'swim' ((13)). -/
def beruSwim : Registered Syllable := ⟨[cv [b] e, cv [rRetroflex] u], [[.downstep], []]⟩

/-- /ꜜkeɽee/ 'eat' ((14)). -/
def kereeEat : Registered Syllable := ⟨[cv [k] e, cvv [rRetroflex] e], [[.downstep], [], []]⟩

/-- /ꜜmwaɽii/ 'plant' ((41), (42)). -/
def mwariiPlant : Registered Syllable := ⟨[cv [mw] a, cvv [rRetroflex] i], [[.downstep], [], []]⟩

/-- /veꜜyuu/ 'to be sick, to die' ((43), (44)). -/
def veyuuSick : Registered Syllable := ⟨[cv [v] e, cvv [y] u], [[], [.downstep], []]⟩

/-- /kaꜜgwee/ 'like' ((43)). -/
def kagweeLike : Registered Syllable := ⟨[cv [k] a, cvv [gw] e], [[], [.downstep], []]⟩

/-- /uɽu/ 'cut' ((56a)). -/
def uruCut : Registered Syllable := ⟨[cv [] u, cv [rRetroflex] u], [[], []]⟩

/-- /ꜜti.e/ 'tear' ((56b), (57)). -/
def tieTear : Registered Syllable := ⟨[cv [t] i, cv [] e], [[.downstep], []]⟩

/-- /ꜜmi.e/ 'wet' ((32), (33)). -/
def mieWet : Registered Syllable := ⟨[cv [m] i, cv [] e], [[.downstep], []]⟩

/-- /goo/ 'Hibbertia pancheri, plant sp.' ((32)). -/
def gooHibbertia : Registered Syllable := ⟨[cvv [g] o], [[], []]⟩

/-- /ꜜgoo/ 'tree' ((33)). -/
def gooTree : Registered Syllable := ⟨[cvv [g] o], [[.downstep], []]⟩

/-- /ꜜtaa/ 'one' ((7), (19), (20)). -/
def taaOne : Registered Syllable := ⟨[cvv [t] a], [[.downstep], []]⟩

/-- /dɪɪ/ 'small' ((6), (19)). -/
def diiSmall : Registered Syllable := ⟨[cvv [d] smallCapitalI], [[], []]⟩

/-- /pwi/ 'cooked' ((20)). -/
def pwiCooked : Registered Syllable := ⟨[cv [pw] i], [[]]⟩

/-- /kaa/ 'smoke' ((9)). -/
def kaaSmoke : Registered Syllable := ⟨[cvv [k] a], [[], []]⟩

/-- /ꜜʈã/ 'fire(wood)' ((9), (10), (16)). -/
def taFire : Registered Syllable := ⟨[cv [tRetroflex] aNasal], [[.downstep]]⟩

/-- /ꜜvi/ 'take' ((10)). -/
def viTake : Registered Syllable := ⟨[cv [v] i], [[.downstep]]⟩

/-- /kwɛ/ 'dance' ((53a)). -/
def kweDance : Registered Syllable := ⟨[cv [kw] openE], [[]]⟩

/-- /ꜜkwe/ 'eat' ((48), (53b)). -/
def kweEat : Registered Syllable := ⟨[cv [kw] e], [[.downstep]]⟩

/-- /tɪɪ/ 'look at' ((30)). -/
def tiiLook : Registered Syllable := ⟨[cvv [t] smallCapitalI], [[], []]⟩

/-- /ŋa/ 'work' ((46)). -/
def ngaWork : Registered Syllable := ⟨[cv [ŋ] a], [[]]⟩

/-- /ꜜmwa/ 'house' ((37), (55a)). -/
def mwaHouse : Registered Syllable := ⟨[cv [mw] a], [[.downstep]]⟩

/-- /ꜜʊʊ/ 'mat' ((55b)). -/
def uuMat : Registered Syllable := ⟨[cvv [] upsilon], [[.downstep], []]⟩

/-- /ũ/ 'hair' ((55b)). -/
def uHair : Registered Syllable := ⟨[cv [] uNasal], [[]]⟩

/-- /pooꜜka/ 'animal' ((55b)). -/
def pookaAnimal : Registered Syllable := ⟨[cvv [p] o, cv [k] a], [[], [], [.downstep]]⟩

/-- /ꜜko/ 'manner' ((55c)). -/
def koManner : Registered Syllable := ⟨[cv [k] o], [[.downstep]]⟩

/-- /ꜜvuu/ 'speak' ((55c)). -/
def vuuSpeak : Registered Syllable := ⟨[cvv [v] u], [[.downstep], []]⟩

/-- /a.bo.ɽu/ 'person' ((7)), a trisyllable. -/
def aboruPerson : Registered Syllable :=
  ⟨[cv [] a, cv [b] o, cv [rRetroflex] u], [[], [], []]⟩

/-! ### Pronouns and markers -/

/-- /ko/ 1SG.SBJ ((8), (13), (30)). -/
def ko1sg : Registered Syllable := ⟨[cv [k] o], [[]]⟩

/-- /ɲi/ 3SG.SBJ ((36), (46)). -/
def ni3sg : Registered Syllable := ⟨[cv [nPalatal] i], [[]]⟩

/-- /ꜜɳi/ 3PL.SBJ ((11), (47)). -/
def ni3pl : Registered Syllable := ⟨[cv [nRetroflex] i], [[.downstep]]⟩

/-- /te/ DESCR ((7), (13), (30)). -/
def teDescr : Registered Syllable := ⟨[cv [t] e], [[]]⟩

/-- /ꜜmwa/ PFV ((8), (11), (39)). -/
def mwaPfv : Registered Syllable := ⟨[cv [mw] a], [[.downstep]]⟩

/-- /ꜜɳii/ 'say' ((11), (12)). -/
def niiSay : Registered Syllable := ⟨[cvv [nRetroflex] i], [[.downstep], []]⟩

/-- /ꜜme/ 'that' ((11), (12)). -/
def meThat : Registered Syllable := ⟨[cv [m] e], [[.downstep]]⟩

/-! ### Affixes -/

/-- The suffix -ɽe ACT ((13), (30), (53), (57)). -/
def reAct : Registered Syllable := ⟨[cv [rRetroflex] e], [[]]⟩

/-- The prefix a- STAT ((15), (21)). -/
def aStat : Registered Syllable := ⟨[cv [] a], [[]]⟩

/-- The verbal classifier prefix ʈa- 'VERB with one's hand' ((56), (57)), registerless of
itself and copying the register of the verb's initial syllable. -/
def taHand : Registered Syllable := ⟨[cv [tRetroflex] a], [[]]⟩

/-! ### Loanwords ((54)) -/

/-- /oꜜo.ci/ 'horse', from English. -/
def oociHorse : Registered Syllable := ⟨[cvv [] o, cv [c] i], [[], [.downstep], []]⟩

/-- /piꜜi.ki/ 'pig', from English. -/
def piikiPig : Registered Syllable := ⟨[cvv [p] i, cv [k] i], [[], [.downstep], []]⟩

/-- /poꜜo.ci/ 'pouch, pocket', from French. -/
def poociPouch : Registered Syllable := ⟨[cvv [p] o, cv [c] i], [[], [.downstep], []]⟩

/-- /taꜜa.ci/ 'bowl', from French. -/
def taaciBowl : Registered Syllable := ⟨[cvv [t] a, cv [c] i], [[], [.downstep], []]⟩

/-- /coꜜo.ɽo/ 'salt', from English. -/
def cooroSalt : Registered Syllable := ⟨[cvv [c] o, cv [rRetroflex] o], [[], [.downstep], []]⟩

/-- /kaꜜa.ʈɛ/ 'car', from English. -/
def kaateCar : Registered Syllable := ⟨[cvv [k] a, cv [tRetroflex] openE], [[], [.downstep], []]⟩

/-! ### The lists -/

/-- The native stems. -/
def stems : List (Registered Syllable) :=
  [iTip, iPiece, iiBamboo, iiElaeocarpus, beDie, beNiaouli, dooBag, dooCordyline, cuWipe,
    cuKnock, niCoconut, niBreast, keeHusband, keeMulberry, beeNeg, beeFish, beeDescendance,
    pwaaMen, pwaaWhite, pwaaPacket, kooPlace, kooFish, kooEgg, kee1pl, kaaProspective,
    kaaParent, kaaBig, booBlind, uuNet, kureForest, kureEnd, kureCrayfish, iyaFish, kwieWind,
    iaWar, pweendiSon, uureMoon, wareeLiana, utiiHome, beiiJealous, veentooFish, vetoPut,
    teaGoUp, mwereAgain, kapwaIron, tobeWake, ngereThink, beruSwim, kereeEat, mwariiPlant,
    veyuuSick, kagweeLike, uruCut, tieTear, mieWet, gooHibbertia, gooTree, taaOne, diiSmall,
    pwiCooked, kaaSmoke, taFire, viTake, kweDance, kweEat, tiiLook, ngaWork, mwaHouse, uuMat,
    uHair, pookaAnimal, koManner, vuuSpeak, aboruPerson, ko1sg, ni3sg, ni3pl, teDescr, mwaPfv,
    niiSay, meThat]

/-- The affixes. -/
def affixes : List (Registered Syllable) := [reAct, aStat, taHand]

/-- The loanwords. -/
def loans : List (Registered Syllable) :=
  [oociHorse, piikiPig, poociPouch, taaciBowl, cooroSalt, kaateCar]

/-- Every stem's tier has one entry per mora. -/
theorem stems_aligned : ∀ s ∈ stems, s.IsAligned Prosody.Syllable.pnatMoraCount := by decide

theorem affixes_aligned : ∀ s ∈ affixes, s.IsAligned Prosody.Syllable.pnatMoraCount := by decide

theorem loans_aligned : ∀ s ∈ loans, s.IsAligned Prosody.Syllable.pnatMoraCount := by decide

/-- The lax front vowel occurs long only: every syllable it heads is bimoraic. -/
theorem smallCapitalI_heavy :
    ∀ s ∈ stems, ∀ σ ∈ s.syllables,
      σ.nucleusSegments = [smallCapitalI] → σ.moraCount = 2 := by
  decide

end Drubea
