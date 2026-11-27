module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# German polarity-sensitive items

This file defines the German polarity-sensitive items. These are the indefinite *irgendein*, the
modal *brauchen* 'need', *ausstehen können* 'can stand', *auch nur irgendetwas* 'anything at all',
*sonderlich* 'very', and the punctual *erst* 'only then'. The licensing theory of
`Semantics/PolarityItem/Licenser.lean` predicts which environments license each item.

*Irgendein* is an existential indefinite with free-choice effects under modals. Kratzer and
Shimoyama attest it under possibility and necessity modals, under negative quantifiers such as
*niemand* 'nobody' and *auf keinen Fall* 'in no case', under *bezweifeln* 'doubt', and in an
embedded question. They find it ungrammatical under the inflectional negation *nicht* unless
*irgend* is stressed. Their sentences are rows of `Data/Examples/KratzerShimoyama2002.json`.
*Irgendein* is also acceptable in an episodic sentence, where it signals the ignorance or
indifference of the speaker, although such a sentence is not a licensing environment. *Brauchen*
with a *zu*-infinitive occurs only with a negative or with *nur* or *bloß* 'only'. Zwarts classes
*brauchen* and *ausstehen können* as weak negative polarity items, which are acceptable under
*höchstens* 'at most' and *nur wenige* 'only a few'. He classes *auch nur irgendetwas* and
*sonderlich* as strong negative polarity items, which are acceptable only in an anti-additive
context such as *keiner* 'no one'. `Studies/Zwarts1998.lean` checks the four items against his
examples. Büring and Gunlogson, and Schaebbicke, Seeliger, and Repp in a rating study, find
*brauchen* licensed by *niemand* and *kein* and unacceptable in a positive polar question. *Erst*
is the positive polarity *until* of Karttunen's chart.

## TODO

The rating study finds *vielleicht* 'maybe' no better a host than a positive assertion, and finds
items that are acceptable only under *nicht* and in a question. Its sixty items and their median
ratings are not entered here. Van Rooy ties an item in a question to a questioner who expects the
negative answer.

## References

* [zwarts-1998]
* [kratzer-shimoyama-2002]
* [durrell-2011]
* [buring-gunlogson-2000]
* [schaebbicke-seeliger-repp-2021]
* [van-rooy-2003a]
* [karttunen-1974]
-/

@[expose] public section

namespace German.PolarityItems

open PolarityItem

/-- *Irgendein* is an existential indefinite with free-choice effects. It stands in an embedded
polar question, *Der Lehrer hat gefragt, ob Hans irgendein Buch gelesen hat* 'The teacher asked
whether Hans read any book' ([kratzer-shimoyama-2002] (22)). -/
def irgendein : PolarityItem :=
  { form := "irgendein"
  , attested := {.polarQuestion} }

/-! ### NPI -/

/-- *Brauchen* 'need' with a *zu*-infinitive, a weak negative polarity item, as in *Höchstens eine
Frau wird sich zu verantworten brauchen* 'At most one woman need justify herself' and *Keiner wird
solch eine Prüfung durchzustehen brauchen* 'No one need go through such an ordeal' ([zwarts-1998]
(3a), (3b)). The rating study of Schaebbicke, Seeliger, and Repp finds it intermediate under the
merely downward-entailing *kaum*, with a median of 4 of 7, between 5.5 under *kein* and 1.5 in a
positive question. It is out in a positive assertion, *Sie braucht eine Entschuldigung
mitzubringen* 'She needs to bring an excuse', and in a positive polar question, *Braucht sie eine
Entschuldigung mitzubringen?*, and fine under *niemand* ([buring-gunlogson-2000] (15)). -/
def brauchen : PolarityItem :=
  { form := "brauchen"
  , attested := {.nobody, .atMost}
  , excluded := {.positiveAssertion, .polarQuestion} }

/-- *Ausstehen können* 'can stand', a weak negative polarity item ([zwarts-1998]). -/
def ausstehenKoennen : PolarityItem :=
  { form := "ausstehen können"
  , attested := {.few, .nobody} }

/-- *Auch nur irgendetwas* 'anything at all', a strong negative polarity item, which requires an
anti-additive context ([zwarts-1998]). -/
def auchNurIrgendetwas : PolarityItem :=
  { form := "auch nur irgendetwas"
  , attested := {.nobody}
  , excluded := {.atMost} }

/-- *Sonderlich* 'very', a strong negative polarity item ([zwarts-1998]). -/
def sonderlich : PolarityItem :=
  { form := "sonderlich"
  , attested := {.nobody}
  , excluded := {.few} }

/-! ### PPI -/

/-- *Erst* 'only then', the punctual *until* of a positive clause, as in *die Prinzessin wachte
erst um 9 Uhr auf* 'the princess did not wake up until nine'. The sentence entails a waking at
nine, and *erst* does not combine with negation. -/
def erst : PolarityItem :=
  { form := "erst" }

end German.PolarityItems
