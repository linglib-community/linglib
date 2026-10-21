module

public import Linglib.Morphology.Morphotactics.AffixTemplate

/-!
# Sesotho verb affixes

The affixes of the Sesotho (Southern Sotho) verb and the order in which they appear. Before
the stem, word-edge inward, come the subject marker, the negative *-sa-*, a tense, aspect or
mood marker and the object marker or the reflexive; after it, stem-outward, the reversive
*-oll-*, the extensions that change valence (the causative *-is-*, the neuter *-eh-*, the
applicative *-el-*, the completive *-ell-*, which reduplicates the applicative, and the
reciprocal *-an-*), the perfect *-il-*, the passive *-w-*, the mood vowel and the
interrogative or relative *-ng*. A form takes at most one affix of each position except the
extensions, which stack.

The order is Demuth's schema (14) of the verbal complex, subject marker, tense or
aspect, object marker, stem, extensions, perfect, passive, mood, in which the passive is added
last when an extension, the perfect and the passive co-occur, as in *pheh-ets-w-e* 'was cooked
(food)' (44), and the relative *-ng* follows the mood vowel, *pheh-il-e-ng* (29). The
inventory within the positions is the one Hahn, Degen and Futrell extract from Demuth's corpus
and document from the grammar of Doke and Mofokeng; their own order places the passive before
the perfect, against (44). The corpus fuses some neighbouring markers, a tense prefix
with the following object marker in particular, and treats the interrogative *-ng*, a clitic
form of *eng* 'what', as a suffix.

## Main definitions

* `Sesotho.Verb.Slot`, `Sesotho.Verb.Exponent`: the affix positions and the affixes of each.
* `Sesotho.Verb.template`: the positions before and after the stem, the extension position
  stacking.

## Implementation notes

The affixes are cited in their docstrings and not entered as morphs: the subject and object
markers are paradigms over person, number and noun class, and the perfect and the mood endings
vary with their context, which a paradigm layer would carry. The infinitive prefix *ho-* is not
entered.

## References

* [M. Hahn, J. Degen, R. Futrell, *Modeling Word and Morpheme Order in Natural Language as an
  Efficient Trade-Off of Memory and Surprisal* (2021)][hahn-degen-futrell-2021]
* [K. Demuth, *Acquisition of Sesotho* (1992)][demuth-1992]
* [C. M. Doke, S. M. Mofokeng, *Textbook of Southern Sotho Grammar* (1967)][doke-mofokeng-1967]
-/

@[expose] public section

namespace Sesotho.Verb

/-- The affix positions of the verb, the prefix positions word-edge inward and then the suffix
positions stem-outward. -/
inductive Slot where
  /-- The subject marker. -/
  | subject
  /-- The negative *-sa-*. -/
  | negation
  /-- The tense, aspect and mood prefixes. -/
  | tam
  /-- The object marker or the reflexive. -/
  | object
  /-- The reversive *-oll-*. -/
  | reversive
  /-- The extensions that change valence. -/
  | extension
  /-- The perfect *-il-*. -/
  | tense
  /-- The passive *-w-*. -/
  | voice
  /-- The mood vowel. -/
  | mood
  /-- The interrogative and the relative *-ng*. -/
  | interrogativeRelative
  deriving DecidableEq, Repr

/-- The affixes of each position. -/
inductive Exponent : Slot → Type where
  /-- The subject marker of a main clause. -/
  | subject : Exponent .subject
  /-- The subject marker of a relative clause. -/
  | relativeSubject : Exponent .subject
  /-- The negative *-sa-*. -/
  | negative : Exponent .negation
  /-- The future *-tla-*, *-tlo-*, *-ilo-*. -/
  | future : Exponent .tam
  /-- The present *-a-*. -/
  | present : Exponent .tam
  /-- The potential *-ka-*. -/
  | potential : Exponent .tam
  /-- The persistive *-sa-*. -/
  | persistive : Exponent .tam
  /-- The recent past *-tswa-*. -/
  | recentPast : Exponent .tam
  /-- The object marker. -/
  | object : Exponent .object
  /-- The reflexive. -/
  | reflexive : Exponent .object
  /-- The reversive *-oll-*: *tlama* 'bind', *tlamolla* 'loosen'. -/
  | reversive : Exponent .reversive
  /-- The causative *-is-*. -/
  | causative : Exponent .extension
  /-- The neuter *-eh-*, *-ahal-*, which removes an argument. -/
  | neuter : Exponent .extension
  /-- The applicative *-el-*, which adds one. -/
  | applicative : Exponent .extension
  /-- The completive *-ell-*, a reduplicated applicative. -/
  | completive : Exponent .extension
  /-- The reciprocal *-an-*. -/
  | reciprocal : Exponent .extension
  /-- The passive *-w-*. -/
  | passive : Exponent .voice
  /-- The perfect *-il-*, fusing with a preceding applicative as *-ets-*. -/
  | perfect : Exponent .tense
  /-- The indicative ending, *-a* or *-e*. -/
  | indicative : Exponent .mood
  /-- The subjunctive ending, *-e* or *-a*, plural *-eng*. -/
  | subjunctive : Exponent .mood
  /-- The imperative *-e*. -/
  | imperative : Exponent .mood
  /-- The plural imperative *-ang*. -/
  | imperativePlural : Exponent .mood
  /-- The interrogative *-ng*. -/
  | interrogative : Exponent .interrogativeRelative
  /-- The relative *-ng*. -/
  | relative : Exponent .interrogativeRelative
  deriving DecidableEq

/-- The subject, negative, tense or aspect and object positions before the stem, word-edge
inward, and after it, stem-outward, the reversive, the stacking extensions, the perfect, the
passive, the mood vowel and *-ng*. -/
def template : Morphology.AffixTemplate Slot where
  prefixSlots := [.subject, .negation, .tam, .object]
  suffixSlots := [.reversive, .extension, .tense, .voice, .mood, .interrogativeRelative]
  stacking := {.extension}

end Sesotho.Verb
