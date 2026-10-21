module

public import Linglib.Morphology.Morphotactics.AffixTemplate
public import Linglib.Fragments.Japanese.Negation
public import Linglib.Fragments.Japanese.Voice

/-!
# Japanese verb suffixes

The suffixes of the Japanese verb and the order in which they appear, from the stem outward:
the verbalizer *-su* (*suru*) of Sino-Japanese verbal nouns, the causative *-(s)ase*, the
passive and the potential in *-(r)are*, the polite *-mas*, the desiderative *-ta(i)*, the
negative *-(a)na* and the inflection that closes the word, non-past *-(r)u*, past *-ta*,
hortative *-(y)oo* or gerund *-te*. A verb form takes at most one suffix of each position, and
the positions appear in this order. The final position is Narrog's class of inflections: no
inflection follows another, so the tense, mood and nonfinite endings share one slot.

The suffixes and their positions are those Hahn, Degen and Futrell extract from the Universal
Dependencies segmentation and document from the grammar of Kaiser and colleagues. The
polite suffix precedes the desiderative there on the strength of corpus forms such as
*mi-mashi-tai* 'I want to see'; the two rarely share a word, since the desiderative inflects as
an adjective and takes the polite copula instead. Narrog finds the causative on either
side of the desiderative and counts the potential as modality rather than voice, so the fixed
order is an idealization of the verbal complex, not a description of it.

## Main definitions

* `Japanese.Verb.Slot`, `Japanese.Verb.Exponent`: the suffix positions and the suffixes of each.
* `Japanese.Verb.template`: the suffix positions in order.
* `Japanese.Verb.Exponent.morphs`: the morphs of a suffix, the passive's those of
  `Japanese.directPassive` and the negative's those of `Japanese.Negation.na`.

## Implementation notes

The positions are language-internal. Their comparison with a cross-linguistic inventory of
categories is the apparatus of the study that draws it, `Studies/HahnDegenFutrell2021.lean`,
and lives there. The passive and the potential share the slot, and for vowel-stem verbs the
form; the imperative and the conditional endings of the inflection slot are not entered.

## References

* [M. Hahn, J. Degen, R. Futrell, *Modeling Word and Morpheme Order in Natural Language as an
  Efficient Trade-Off of Memory and Surprisal* (2021)][hahn-degen-futrell-2021]
* [S. Kaiser, Y. Ichikawa, N. Kobayashi, H. Yamamoto, *Japanese: A Comprehensive Grammar*
  (2013)][kaiser-ichikawa-kobayashi-yamamoto-2013]
* [H. Narrog, *The Order of Meaningful Elements in the Japanese Verbal Complex*
  (2010)][narrog-2010b]
-/

@[expose] public section

namespace Japanese.Verb

open Morphology (Morph)

/-- The suffix positions of the verb, stem-outward. -/
inductive Slot where
  /-- The verbalizer *-su* (*suru*) of Sino-Japanese verbal nouns. -/
  | derivation
  /-- The causative *-(s)ase*. -/
  | valence
  /-- The passive and the potential, both *-(r)are*. -/
  | voice
  /-- The polite *-mas*. -/
  | politeness
  /-- The desiderative *-ta(i)*. -/
  | desiderative
  /-- The negative *-(a)na*. -/
  | negation
  /-- The inflection that closes the word. -/
  | inflection
  deriving DecidableEq, Repr

/-- The suffixes of each position. -/
inductive Exponent : Slot → Type where
  /-- *-su*, the stem of *suru* 'do'. -/
  | su : Exponent .derivation
  /-- The causative *-(s)ase*. -/
  | sase : Exponent .valence
  /-- The passive *-(r)are*, the marker of `Japanese.directPassive`. -/
  | rare : Exponent .voice
  /-- The potential, *-(r)are* or *-e* by conjugation class. -/
  | potential : Exponent .voice
  /-- The polite *-mas*, *-mashi* before the past and *-mase* before the negative. -/
  | mas : Exponent .politeness
  /-- The desiderative *-ta(i)*, inflecting as an adjective, *-taku* before the negative. -/
  | tai : Exponent .desiderative
  /-- The negative *-(a)na*, `Japanese.Negation.na`, and *-n* after the polite suffix. -/
  | na : Exponent .negation
  /-- The non-past *-(r)u*. -/
  | u : Exponent .inflection
  /-- The past *-ta*. -/
  | ta : Exponent .inflection
  /-- The hortative *-(y)oo*. -/
  | yoo : Exponent .inflection
  /-- The gerund *-te*. -/
  | te : Exponent .inflection
  deriving DecidableEq

variable {σ : Slot}

/-- The morphs of a suffix in citation form, the segment whose presence depends on the stem
in brackets. -/
def Exponent.morphs : Exponent σ → List Morph
  | .su => [.suff "su"]
  | .sase => [.suff "(s)ase"]
  | .rare => directPassive.marker
  | .potential => [.suff "(r)are"]
  | .mas => [.suff "mas"]
  | .tai => [.suff "ta"]
  | .na => Japanese.Negation.na.morphs
  | .u => [.suff "(r)u"]
  | .ta => [.suff "ta"]
  | .yoo => [.suff "(y)oo"]
  | .te => [.suff "te"]

/-- The suffix positions in their order from the stem outward. -/
def template : Morphology.AffixTemplate Slot where
  suffixSlots :=
    [.derivation, .valence, .voice, .politeness, .desiderative, .negation, .inflection]

end Japanese.Verb
