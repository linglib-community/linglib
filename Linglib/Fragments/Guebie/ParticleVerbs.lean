/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Guebie.Phonology

/-!
# Guébie particle verbs

A Guébie particle verb is a phrasal idiom of a prefixing particle and a verb, with a meaning that
is not compositional. This file lists the particle verbs of Sande, Clem and Dabkowski over the
vowels of `Fragments/Guebie/Phonology.lean`; the vowels of a morpheme agree in [ATR].

## Main definitions

* `Guebie.Morpheme`, `Guebie.Morpheme.atr`: a morpheme and its lexical [ATR] value.
* `Guebie.particleVerbs`: the sample (10) with the pairs of (11) and (12).

## References

* [sande-clem-dabkowski-2026]
-/

@[expose] public section

namespace Guebie

/-- A Guébie morpheme has a transcription, a vowel skeleton and an optional gloss. -/
structure Morpheme where
  form   : String
  vowels : List Phonology.Segment
  gloss  : Option String := none
  deriving DecidableEq

/-- A morpheme's lexical [ATR] value is the value of its agreeing vowels. The rare vowelless
morphemes count as [−ATR] and neither trigger nor block harmony (kɔ-ɲ 'give' surfaces −ATR,
(10)). -/
def Morpheme.atr (m : Morpheme) : Bool :=
  (m.vowels.head?.map Guebie.atr).getD false

/-- Morpheme-internal vowels agree in ATR ([sande-clem-dabkowski-2026] §2.1). -/
def Morpheme.ATRUniform (m : Morpheme) : Prop :=
  ∀ v ∈ m.vowels, Guebie.atr v = m.atr

instance (m : Morpheme) : Decidable m.ATRUniform := by
  unfold Morpheme.ATRUniform; infer_instance

theorem Morpheme.ATRUniform.map_withATR {m : Morpheme} (h : m.ATRUniform) :
    m.vowels.map (withATR · m.atr) = m.vowels :=
  (List.map_congr_left (g := id) fun v hv ↦ by rw [← h v hv, withATR_atr, id]).trans
    (List.map_id _)

/-! ### Particles ([sande-clem-dabkowski-2026] (10)–(12))

Underlying forms; surface ATR alternates under harmony (e.g. /mɛ/ → [me] before
a +ATR root, /jɔkʊ/ → [joku]). `dakɔ` and `jɔkʊ` have no independent gloss. -/

def mE : Morpheme := ⟨"mɛ", [epsilon], some "in"⟩
def kO : Morpheme := ⟨"kɔ", [openO], some "at/to"⟩
def dakO : Morpheme := ⟨"dakɔ", [a, openO], none⟩
def jOkU : Morpheme := ⟨"jɔkʊ", [openO, upsilon], none⟩

/-! ### Verbs appearing in the particle-verb inventory -/

def tE : Morpheme := ⟨"tɛ", [epsilon], some "be strong"⟩
def trO : Morpheme := ⟨"trɔ", [openO], some "be long/tall"⟩
def para : Morpheme := ⟨"para", [a, a], none⟩
def salI : Morpheme := ⟨"salɪ", [a, smallCapitalI], none⟩
def nu : Morpheme := ⟨"nu", [u], some "hear"⟩
def silije : Morpheme := ⟨"silije", [i, i, e], none⟩
def djE : Morpheme := ⟨"ɟɛ", [epsilon], none⟩
def pUlU : Morpheme := ⟨"pʊlʊ", [upsilon, upsilon], some "be fast"⟩
def ny : Morpheme := ⟨"ɲ", [], none⟩
def ggO : Morpheme := ⟨"ggɔ", [openO], none⟩
def wa : Morpheme := ⟨"wa", [a], none⟩
def ni : Morpheme := ⟨"ni", [i], some "see"⟩
def ngwOsa : Morpheme := ⟨"ŋʷɔsa", [openO, a], some "scrape"⟩

/-! ### Particle verbs -/

/-- A particle verb pairs a particle with a verb in a phrasal idiom
([sande-clem-dabkowski-2026] (10)). -/
structure ParticleVerb where
  particle : Morpheme
  verb     : Morpheme
  gloss    : String
  deriving DecidableEq

/-- The (10) inventory, plus the (11)–(12) /jɔkʊ/+/ni/ and /jɔkʊ/+/ŋʷɔsa/ pairs. -/
def particleVerbs : List ParticleVerb :=
  [⟨mE, tE, "be strong"⟩, ⟨mE, trO, "be long"⟩, ⟨mE, para, "enter"⟩,
   ⟨mE, salI, "tell"⟩, ⟨mE, nu, "understand"⟩,
   ⟨kO, silije, "straighten"⟩, ⟨kO, trO, "be tall"⟩, ⟨kO, salI, "diminish"⟩,
   ⟨kO, djE, "take"⟩, ⟨kO, pUlU, "hurry"⟩, ⟨kO, ny, "give"⟩,
   ⟨dakO, ggO, "move"⟩, ⟨dakO, wa, "hide"⟩,
   ⟨jOkU, ni, "see"⟩, ⟨jOkU, ngwOsa, "scrape"⟩]

theorem particleVerbs_ATRUniform :
    ∀ pv ∈ particleVerbs, pv.particle.ATRUniform ∧ pv.verb.ATRUniform := by decide

end Guebie
