module

public import Linglib.Morphology.Root.Consonantal
public import Linglib.Languages.Hebrew.Phonology

/-!
# Modern Hebrew consonantal roots

This file defines the Modern Hebrew consonantal roots of the templatic-morphology studies as
roots of segments. A radical that alternates between a stop and a fricative is the archisegment
`Phonology.B`, `Phonology.K` or `Phonology.P`; the /k/ of ק is the plain `Phonology.k`, so a root
is the same root in Arad's transcription (√qlt) and in Faust's (√klt). Roots are named in a
transliteration that writes ח as x, ש as š and צ as c.

## Main definitions

* `Hebrew.klt`, `Hebrew.kl`, `Hebrew.klj`: the roots of Faust's QaTaT–QaTa triplet.
* `Hebrew.dmj`, `Hebrew.bnj`, `Hebrew.glj`, `Hebrew.rmj`, `Hebrew.skt`, `Hebrew.ktv`: the
  roots of his taQTiL nouns and their bases.
* `Hebrew.lmd`, …, `Hebrew.ʔdm`: Arad's roots of the binyanim, the geminate slot, roots across
  patterns and conjugation classes.

## References

* [arad-2005]
* [faust-2026]
-/

@[expose] public section

open Morphology Phonology Hebrew.Phonology

namespace Hebrew

/-! ### The QaTaT–QaTa triplet -/

/-- √klt (קלט), the root of *kalat* 'received', *klita* and *kalut*, and of *hiqlit* 'record',
which Arad writes √qlt. -/
def klt : ConsonantalRoot Segment := ⟨[k, l, t]⟩

/-- √kl (כלל), the biradical root of *kalal* 'included', *klila* and *kalul*, whose identical
final consonants arise by template satisfaction. -/
def kl : ConsonantalRoot Segment := ⟨[K, l]⟩

/-- √klj (קלה), the root of *kala* 'roasted', *klija* and *kaluj*, whose final *j* surfaces only
outside the past tense. -/
def klj : ConsonantalRoot Segment := ⟨[k, l, j]⟩

/-! ### The taQTiL nouns -/

/-- √dmj (דמה), the root of *dimuj* 'simile' and the feminine *tadmit* '(public) image'. -/
def dmj : ConsonantalRoot Segment := ⟨[d, m, j]⟩

/-- √bnj (בנה), the root of *banuj* 'built' and the feminine *tavnit* 'mold'. -/
def bnj : ConsonantalRoot Segment := ⟨[B, n, j]⟩

/-- √glj (גלה), the root of *galuj* 'apparent' and the feminine *taglit* 'discovery'. -/
def glj : ConsonantalRoot Segment := ⟨[«ɡ», l, j]⟩

/-- √rmj (רמה), the root of *remija* 'cheating' and the feminine *tarmit* 'hoax'. -/
def rmj : ConsonantalRoot Segment := ⟨[«ʁ», m, j]⟩

/-- √skt (סכת), the *t*-final root of the masculine *taskit* 'radio drama'. -/
def skt : ConsonantalRoot Segment := ⟨[s, K, t]⟩

/-- √ktv (כתב), the root of *katuv* 'written', *kituv* 'script' and *ktiva* 'writing'. -/
def ktv : ConsonantalRoot Segment := ⟨[K, t, B]⟩

/-! ### The binyanim -/

/-- √lmd (למד), the root of *lamad* 'learn' and its passive *nilmad*. -/
def lmd : ConsonantalRoot Segment := ⟨[l, m, d]⟩

/-- √spr (ספר), the root of *siper* 'tell' and its passive *supar*. -/
def spr : ConsonantalRoot Segment := ⟨[s, P, «ʁ»]⟩

/-- √pll (פלל), the root of *hitpalel* 'pray'. -/
def pll : ConsonantalRoot Segment := ⟨[P, l, l]⟩

/-- √npc (נפץ), the root of *nipec* 'shatter' and its passive *nupac*. -/
def npc : ConsonantalRoot Segment := ⟨[n, P, ts]⟩

/-- √xlq (חלק), the root of *xileq* 'divide' and its passive *xulaq*. -/
def xlq : ConsonantalRoot Segment := ⟨[x, l, k]⟩

/-- √str (סתר), the root of *histir* 'hide' and its passive *hustar*. -/
def str : ConsonantalRoot Segment := ⟨[s, t, «ʁ»]⟩

/-- √pqd (פקד), the root of *hifqid* 'deposit' and its passive *hufqad*. -/
def pqd : ConsonantalRoot Segment := ⟨[P, k, d]⟩

/-- √šmr (שמר), the root of *šamar* 'guard'. -/
def «šmr» : ConsonantalRoot Segment := ⟨[«ʃ», m, «ʁ»]⟩

/-! ### The geminate slot -/

/-- √trgm (תרגם), the quadriliteral root of *tirgem* 'translate', whose fourth consonant takes
the geminate slot. -/
def trgm : ConsonantalRoot Segment := ⟨[t, «ʁ», «ɡ», m]⟩

/-- √qbl (קבל), the root of *qibel* 'receive', where the geminate *b* does not spirantize. -/
def qbl : ConsonantalRoot Segment := ⟨[k, B, l]⟩

/-- √rkk (רכך), the root of *hitrakex* 'become soft', where the geminate *k* does not
spirantize. -/
def rkk : ConsonantalRoot Segment := ⟨[«ʁ», K, K]⟩

/-! ### Roots across patterns -/

/-- √šmn (שמן), the root of *šemen* 'oil', *šamenet* 'cream', *hišmin* 'fatten' and *šimen*
'grease'. -/
def «šmn» : ConsonantalRoot Segment := ⟨[«ʃ», m, n]⟩

/-- √xšb (חשב), the root of *xašav* 'think', *xišev* 'calculate', *maxšev* 'computer' and
*xešbon* 'arithmetic'. -/
def «xšb» : ConsonantalRoot Segment := ⟨[x, «ʃ», B]⟩

/-- √sgr (סגר), the root of *sagar* 'close', *hisgir* 'extradite', *seger* 'closure' and
*misgeret* 'frame'. -/
def sgr : ConsonantalRoot Segment := ⟨[s, «ɡ», «ʁ»]⟩

/-! ### The conjugation classes -/

/-- √ptx (פתח), the root of *patax* 'open' and its inchoative *niftax*. -/
def ptx : ConsonantalRoot Segment := ⟨[P, t, x]⟩

/-- √qpʔ (קפא), the root of *qafaʔ* 'freeze' and its causative *hiqpiʔ*. -/
def «qpʔ» : ConsonantalRoot Segment := ⟨[k, P, «ʔ»]⟩

/-- √mss (מסס), the root of *namas* 'melt' and its causative *hemes*. -/
def mss : ConsonantalRoot Segment := ⟨[m, s, s]⟩

/-- √xmm (חמם), the root of *ximem* 'heat' and its inchoative *hitxamem*. -/
def xmm : ConsonantalRoot Segment := ⟨[x, m, m]⟩

/-- √bhr (בהר), the root of *hivhir* 'make clear' and its inchoative *hitbaher*. -/
def bhr : ConsonantalRoot Segment := ⟨[B, h, «ʁ»]⟩

/-- √ʔdm (אדם), the root of *heʔedim* 'redden, be red'. -/
def «ʔdm» : ConsonantalRoot Segment := ⟨[«ʔ», d, m]⟩

end Hebrew
