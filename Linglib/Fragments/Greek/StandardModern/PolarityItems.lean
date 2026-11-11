module

public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Fragments.Greek.StandardModern.Indefinites

/-!
# Greek polarity items

The polarity items of Modern Greek. *Para monon*, literally 'but only', renders English punctual
*until* in a negated clause. It is a strong negative polarity item: negation and *xoris* 'without'
license it, while *amfivalo* 'I doubt' and a rhetorical question do not. The sentences that attest
it and star it are rows of `Data/Examples/Giannakidou2002.json`. The members of the
*tipota*-series are n-words under emphatic accent, which the literature writes in capitals:
emphatic *TIPOTA* 'nothing' needs negation or *xoris*, and is out in the questions, conditionals,
imperatives and complements of intensional verbs that admit the unaccented pronoun.

## Implementation notes

* Giannakidou draws the line between antiveridical and merely nonveridical triggers. The library
  licenses by Zwarts's strengths of negation, and an anti-additive licensor draws the same line
  through the contexts of both entries.
* The accent is not part of an entry's form, which is the pronoun's. The unaccented pronoun has
  no entry here: its distribution is a region of Haspelmath's map, not a strength of negation.

## TODO

* An emphatic n-word needs its licenser in its own clause, *dhen ipe oti idhe tipota* admitting
  only the unaccented pronoun. A `PolarityItem` records a strength and no locality, so
  `emphaticTipota` is also licensed by an anti-additive context outside its clause.

## References

* [giannakidou-2002]
* [giannakidou-2000]
* [giannakidou-1998]
* [haspelmath-1997]
* [zwarts-1998]
-/

@[expose] public section

namespace Greek.StandardModern.PolarityItems

open PolarityItem

/-- *para monon* (παρά μόνον) 'but only', the punctual *until* of a negated clause, as in *i
prigipisa dhen eftase para monon ta mesanixta* 'the princess did not arrive until midnight'. It is
out under *amfivalo an* 'I doubt whether' and in a rhetorical question. -/
def paraMonon : PolarityItem :=
  { form := "para monon"
  , licensor := some .antiAdditive }

/-- Emphatic *TIPOTA* (τίποτα) 'nothing', the pronoun *tipota* under emphatic accent, as in *dhen
ipa TIPOTA* 'I said nothing'. Negation and *xoris* 'without' license it; a question, a
conditional, an imperative and *elpizo* 'I hope' do not. -/
def emphaticTipota : PolarityItem :=
  { form := Indefinites.tipota.form
  , licensor := some .antiAdditive }

end Greek.StandardModern.PolarityItems
