module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.German.TemporalConnectives

/-!
# German polarity-sensitive items

This file defines the German polarity-sensitive items: the indefinite *irgendein*, the modal
*brauchen* 'need' and the punctual *erst* 'only then'. The licensing theory of
`Semantics/Polarity/Licensing.lean` predicts which environments license each.

*Irgendein* is an existential indefinite with free-choice effects under modals. Kratzer and
Shimoyama attest it under possibility and necessity modals, under negative quantifiers such as
*niemand* 'nobody' and *auf keinen Fall* 'in no case', under *bezweifeln* 'doubt' and in an
embedded question, and they find it ungrammatical under the inflectional negation *nicht* unless
*irgend* is stressed; their sentences are rows of `Data/Examples/KratzerShimoyama2002.json`. It is
also fine in an episodic sentence, where it signals the speaker's ignorance or indifference, which
is not a licensing environment. *Brauchen* with a *zu*-infinitive
occurs only with a negative or with *nur* or *bloß* 'only'. It is a weak negative polarity item,
licensed by *höchstens eine* 'at most one' as by *keiner* 'no one' ([zwarts-1998] (3)); Büring and
Gunlogson, and Schaebbicke, Seeliger and Repp in a rating study, find it licensed by *niemand* and
*kein* and out in a positive polar question. *Erst* is the positive polarity *until* of Karttunen's
chart, the connective `German.TemporalConnectives.erst`.

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
  , licensor := some .weak
  , licensingContexts := [.atMost, .nobody] }

/-! ### PPI -/

/-- *Erst* 'only then' is the punctual *until* of a positive clause. -/
def erst : PolarityItem :=
  { form := TemporalConnectives.erst.form
  , antiLicensor := some .antiMorphic }

/-! ### Licensing -/

theorem brauchen_licensing_sound :
    ∀ c ∈ brauchen.licensingContexts, c.licenser.Admits brauchen := by
  decide

end German.PolarityItems
