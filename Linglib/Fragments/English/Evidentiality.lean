module

public import Linglib.Semantics.Evidential.Defs

/-!
# English evidentiality

English has no grammatical evidentials: information source is conveyed lexically, by adverbs
(*apparently*, *reportedly*) and parenthetical hedges, never by obligatory morphology.

## References

* [aikhenvald-2004]
* [de-haan-2013]
-/

@[expose] public section

namespace English.Evidentiality

/-- English has no evidentials. -/
def evidentials : List Evidential := []

end English.Evidentiality
