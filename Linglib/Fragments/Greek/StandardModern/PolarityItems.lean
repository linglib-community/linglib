module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Greek polarity items

The polarity items of Modern Greek. *Para monon*, literally 'but only', renders English punctual
*until* in a negated clause. It is a strong negative polarity item: negation and *xoris* 'without'
license it, while *amfivalo* 'I doubt' and a rhetorical question do not, and the attested and
excluded contexts [agree with the licensing theory](##paraMonon_licensing_sound).

## Implementation notes

* Giannakidou draws the line between antiveridical and merely nonveridical triggers. The library
  licenses by Zwarts's strengths of negation, and the entry's anti-additive licensor draws the same
  line through these four contexts.

## References

* [giannakidou-2002]
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
  , licensor := some .antiAdditive
  , licensingContexts := [.negation, .withoutClause]
  , excludedContexts := [.doubtVerb, .question] }

/-- The contexts *para monon* is attested in admit it, and those it is attested to be out in do
not. -/
theorem paraMonon_licensing_sound :
    (∀ c ∈ paraMonon.licensingContexts, c.licenser.Admits paraMonon) ∧
      ∀ c ∈ paraMonon.excludedContexts, ¬ c.licenser.Admits paraMonon := by
  decide

end Greek.StandardModern.PolarityItems
