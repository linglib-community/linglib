module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Languages.Turkish.Morphotactics

/-!
# Turkish verbs

This file defines the Turkish verbs that the studies of [qing-uegaki-2025] and of
[goksel-kerslake-2005] read. A `Turkish.Verb` is the root entry together with the segments of
its root and the voice suffixes that build its stem. `Verb.inflect` is its surface form under a
string of inflectional suffixes, derived by `Turkish.realize`.

The preferential attitudes *kork-* 'fear', *um-* 'hope' and *endişelen-* 'worry' take a
nominalized clause, in the ablative under *kork-* and *endişelen-* and in the accusative under
*um-*, and *kork-* and *endişelen-* take it as a question as well. *dolan-* 'walk around' is
intransitive. The causatives *öldür-* 'kill' and *yaptır-* 'have done' are built on *öl-* 'die'
and *yap-* 'do' by the voice suffix -DIr.

## References

* [goksel-kerslake-2005]
* [qing-uegaki-2025]
-/

@[expose] public section

open Phonology

namespace Turkish

open ArgumentStructure Turkish.Phonology

/-- A Turkish verb is the root entry, whose `form` is the spelled stem, together with the
segments of its root and the voice suffixes that build its stem. -/
structure Verb extends _root_.Verb where
  /-- The segments of the root. -/
  rootSegments : List Segment
  /-- The voice suffixes of the stem, in order. -/
  voice : List (Verb.Exponent .voice) := []
  deriving BEq

namespace Verb

/-- `v.suffixes sfx` is the suffix string of the verb under the inflectional suffixes `sfx`,
its voice suffixes followed by `sfx`. -/
def suffixes (v : Verb) (sfx : List (Σ σ, Exponent σ)) : List (Σ σ, Exponent σ) :=
  v.voice.map (⟨.voice, ·⟩) ++ sfx

/-- `v.inflect sfx` is the surface form of the verb under the inflectional suffixes `sfx`,
which with no suffixes is the stem. -/
def inflect (v : Verb) (sfx : List (Σ σ, Exponent σ)) : List Segment :=
  realize v.rootSegments (forms (v.suffixes sfx))

end Verb

/-- The frame of a verb that takes a nominalized clause as a question. -/
def nominalizedQuestion : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .nominalized) (types := .interrogatives)]⟩

/-! ### Preferential attitudes -/

/-- *kork-* 'fear', a negative preference. -/
def kork : Verb where
  morphs := [.root "kork"]
  rootSegments := [k, o, r, k]
  valency := .ofFrames [ArgumentFrame.gerund, nominalizedQuestion]
  opaqueContext := true
  attitude := some (.preferential .negative)

/-- *um-* 'hope', a positive preference. -/
def um : Verb where
  morphs := [.root "um"]
  rootSegments := [u, m]
  valency := .ofFrame ArgumentFrame.gerund
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *endişelen-* 'worry', a negative preference. -/
def endişelen : Verb where
  morphs := [.root "endişelen"]
  rootSegments := [e, n, d, i, ş, e, l, e, n]
  valency := .ofFrames [ArgumentFrame.gerund, nominalizedQuestion]
  opaqueContext := true
  attitude := some (.preferential .negative)

/-! ### Motion -/

/-- *dolan-* 'walk around', intransitive. -/
def dolan : Verb where
  morphs := [.root "dolan"]
  rootSegments := [d, o, l, a, n]
  valency := .ofFrame ArgumentFrame.intransitive

/-! ### Causatives -/

/-- *öldür-* 'kill', the causative of *öl-* 'die'. -/
def öldür : Verb where
  morphs := [.root "öldür"]
  rootSegments := [ö, l]
  voice := [.causative]
  valency := .ofFrame ArgumentFrame.np

/-- *yaptır-* 'have done, make do', the causative of *yap-* 'do, make'. -/
def yaptır : Verb where
  morphs := [.root "yaptır"]
  rootSegments := [y, a, p]
  voice := [.causative]
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)

/-- `verbs` lists the entries. -/
def verbs : List Verb := [kork, um, endişelen, dolan, öldür, yaptır]

end Turkish
