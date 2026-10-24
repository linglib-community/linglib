module

public import Linglib.Semantics.Tense.Perspective

/-!
# Hebrew temporal deictic adverbs

Modern Hebrew *az* 'then' is the distal temporal deictic adverb, referring to a past or future
time away from the deictic centre. Like English *then* it cannot modify a present tense, even
the embedded present of an attitude report read as simultaneous with the past attitude:
*lifney alpayim šana, Yosef xašav še Miriam ohevet oto (*az)* '2,000 years ago, Yosef thought
that Miriam loved him then' is out with the adverb, the observation Tsilia and Zhao take from
Ogihara and Sharvit. The example is Tsilia and Zhao's.

## References

* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Hebrew.TemporalDeictic

open scoped Denotes

open Tense

/-- *az* (אז) 'then', a time before or after the deictic centre. -/
def az : DeicticAdverb := { form := "az", cell := ⟦present⟧ᶜ }

end Hebrew.TemporalDeictic
