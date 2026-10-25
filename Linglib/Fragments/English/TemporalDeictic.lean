module

public import Linglib.Semantics.Tense.Perspective

/-!
# English temporal deictic adverbs

English *then* is the distal temporal deictic adverb: it refers to a time disjoint from its anchor,
in the past or the future when the anchor is the utterance time, and often to a time the preceding
discourse has established, as in Anand and Toosarvandani's *The janitor turned off the lights.
The room was empty then.* Conditional *then* is a different item.

## References

* [anand-toosarvandani-2019]
* [tsilia-zhao-2026]
* [iatridou-1993]
-/

@[expose] public section

namespace English.TemporalDeictic

open scoped Denotes

open Tense

/-- *then*, a time before or after the deictic centre. -/
def then_ : DeicticAdverb := { form := "then", cell := ⟦present⟧ᶜ }

end English.TemporalDeictic
