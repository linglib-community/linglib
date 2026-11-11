module

public import Linglib.Semantics.PolarityItem.Basic

/-!
# Greek polarity items

The polarity items of Modern Greek. *Para monon*, literally 'but only', renders English punctual
*until* in a negated clause. It is a strong negative polarity item: negation and *xoris* 'without'
license it, while *amfivalo* 'I doubt' and a rhetorical question do not. The sentences that attest
it and star it are rows of `Data/Examples/Giannakidou2002.json`. The n-words come in pairs told
apart by emphatic accent, written in capitals. An emphatic n-word such as *TIPOTA* 'nothing' needs
negation or *xoris*, and is out in the questions, conditionals, imperatives and complements of
intensional verbs that admit its non-emphatic counterpart.

## Implementation notes

* Giannakidou draws the line between antiveridical and merely nonveridical triggers. The library
  licenses by Zwarts's strengths of negation, and an anti-additive licensor draws the same line
  through the contexts of both entries.

## References

* [giannakidou-2002]
* [giannakidou-2000]
* [giannakidou-1998]
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

/-- *TIPOTA* (τίποτα, with emphatic accent) 'nothing', an emphatic n-word, as in *dhen ipa TIPOTA*
'I said nothing'. Negation and *xoris* 'without' license it; a question, a conditional, an
imperative and *elpizo* 'I hope' do not. -/
def tipota : PolarityItem :=
  { form := "TIPOTA"
  , licensor := some .antiAdditive }

end Greek.StandardModern.PolarityItems
