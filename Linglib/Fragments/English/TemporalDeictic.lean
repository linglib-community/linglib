module

public import Linglib.Semantics.Tense.Perspective

/-!
# English temporal deictic adverbs

English *then* is the distal temporal deictic adverb: it refers to a past or future time away
from the deictic centre, typically one established in the preceding discourse, as in *The
janitor turned off the lights. The room was empty then.* The description follows
[tsilia-zhao-2026].

## References

* [tsilia-zhao-2026]
-/

@[expose] public section

namespace English.TemporalDeictic

open scoped Denotes

open Tense

/-- *then*, a time before or after the deictic centre. -/
def then_ : DeicticAdverb := { form := "then", cell := ⟦present⟧ᶜ }

end English.TemporalDeictic
