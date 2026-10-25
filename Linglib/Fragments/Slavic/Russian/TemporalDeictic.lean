module

public import Linglib.Semantics.Tense.Perspective

/-!
# Russian temporal deictic adverbs

Russian locates a time relative to the deictic centre with the adverbs *togda* 'then' and
*sejčas* 'now'. *Togda* is distal, referring to a past or future time away from the centre;
*sejčas* refers to a time that includes the centre. The examples are Tsilia and Zhao's.

## References

* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Russian.TemporalDeictic

open scoped Denotes

open Tense

/-- *togda* (тогда) 'then', a time before or after the deictic centre: *V 2016 godu Tanja
skazala, čto togda Putin byl prezidentom Rossii* 'In 2016 Tanja said that Putin was president of
Russia then'. -/
def togda : DeicticAdverb := { form := "togda", cell := ⟦present⟧ᶜ }

/-- *sejčas* (сейчас) 'now', a time including the deictic centre. -/
def sejchas : DeicticAdverb := { form := "sejčas", cell := ⟦present⟧ }

end Russian.TemporalDeictic
