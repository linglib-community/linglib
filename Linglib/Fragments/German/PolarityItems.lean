module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# German polarity-sensitive items

This file defines the German polarity-sensitive items: the indefinite *irgendein*, the modal
*brauchen* 'need', *ausstehen können* 'can stand', *auch nur irgendetwas* 'anything at all',
*sonderlich* 'very' and the punctual *erst* 'only then'. The licensing theory of
`Semantics/PolarityItem/Basic.lean` predicts which environments license each.

*Irgendein* is an existential indefinite with free-choice effects under modals. Kratzer and
Shimoyama attest it under possibility and necessity modals, under negative quantifiers such as
*niemand* 'nobody' and *auf keinen Fall* 'in no case', under *bezweifeln* 'doubt' and in an
embedded question, and they find it ungrammatical under the inflectional negation *nicht* unless
*irgend* is stressed; their sentences are rows of `Data/Examples/KratzerShimoyama2002.json`. It is
also fine in an episodic sentence, where it signals the speaker's ignorance or indifference, which
is not a licensing environment. *Brauchen* with a *zu*-infinitive occurs only with a negative or
with *nur* or *bloß* 'only'. Zwarts classes it and *ausstehen können* as weak negative polarity
items, fine under *höchstens* 'at most' and *nur wenige* 'only a few', and *auch nur irgendetwas*
and *sonderlich* as strong ones, fine only under an anti-additive context such as *keiner* 'no
one'; `Studies/Zwarts1998.lean` checks the four against his examples. Büring and Gunlogson, and
Schaebbicke, Seeliger and Repp in a rating study, find *brauchen* licensed by *niemand* and *kein*
and out in a positive polar question. *Erst* is the positive polarity *until* of Karttunen's chart.

## TODO

The licensing theory licenses every weak negative polarity item in a question, after van Rooy, so
it admits *brauchen* in the positive polar question that Büring and Gunlogson star; the rating
study reserves questions for superweak items.

## References

* [zwarts-1998]
* [kratzer-shimoyama-2002]
* [durrell-2011]
* [buring-gunlogson-2000]
* [schaebbicke-seeliger-repp-2021]
* [van-rooy-2003-npi]
* [karttunen-1974]
-/

@[expose] public section

namespace German.PolarityItems

open PolarityItem

/-- *Irgendein* is an existential indefinite with free-choice effects. -/
def irgendein : PolarityItem :=
  { form := "irgendein"
  , licensor := some .weak
  , freeChoice := true }

/-! ### NPI -/

/-- *Brauchen* 'need' with a *zu*-infinitive, a weak negative polarity item: *Höchstens eine Frau
wird sich zu verantworten brauchen* 'At most one woman need justify herself', *Keiner wird solch
eine Prüfung durchzustehen brauchen* 'No one need go through such an ordeal' ([zwarts-1998] (3a),
(3b)). The rating study of Schaebbicke, Seeliger and Repp finds it intermediate under the merely
downward-entailing *kaum*, with a median of 4 of 7 between 5.5 under *kein* and 1.5 in a positive
question. -/
def brauchen : PolarityItem :=
  { form := "brauchen"
  , licensor := some .weak }

/-- *Ausstehen können* 'can stand', a weak negative polarity item ([zwarts-1998]). -/
def ausstehenKoennen : PolarityItem :=
  { form := "ausstehen können"
  , licensor := some .weak }

/-- *Auch nur irgendetwas* 'anything at all', a strong negative polarity item, needing an
anti-additive context ([zwarts-1998]). -/
def auchNurIrgendetwas : PolarityItem :=
  { form := "auch nur irgendetwas"
  , licensor := some .antiAdditive }

/-- *Sonderlich* 'very', a strong negative polarity item ([zwarts-1998]). -/
def sonderlich : PolarityItem :=
  { form := "sonderlich"
  , licensor := some .antiAdditive }

/-! ### PPI -/

/-- *Erst* 'only then' is the punctual *until* of a positive clause, as in *die Prinzessin wachte
erst um 9 Uhr auf* 'the princess did not wake up until nine', which entails a waking at nine and
does not combine with negation. -/
def erst : PolarityItem :=
  { form := "erst"
  , antiLicensor := some .antiMorphic }

end German.PolarityItems
