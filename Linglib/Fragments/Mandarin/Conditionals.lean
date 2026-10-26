module

public import Linglib.Semantics.Conditionals.Typology

/-!
# Mandarin conditional markers

The Mandarin conditional marker *rúguǒ* 如果 'if', typed by `Conditional.Marker`. Li and Thompson
list it with *jiǎrú*, *jiǎshǐ* and *yàoshi* as the 'if' of an adverbial forward-linking clause,
which stands clause-initially or after the topic or subject. Mandarin marks no grammatical
distinction among real, imagined and counterfactual conditionals, so a single *rúguǒ* clause can
take each of those readings in different contexts.

## References

* [li-thompson-1981]
* [mizuno-2024]
-/

@[expose] public section

namespace Mandarin.Conditionals

/-- *rúguǒ* 如果 'if' is attested in hypothetical conditionals, real, imagined and counterfactual
([li-thompson-1981] pp. 635, 646–648), among them the future-less-vivid and Anderson conditionals
of [mizuno-2024] (11) and (13a). The sources record nothing on a premise reading. -/
def ruguo : Conditional.Marker where
  morphs := [.free "rúguǒ"]
  script := some "如果"
  readings := ⟨({.hypothetical}, ⊤), le_top⟩

end Mandarin.Conditionals
