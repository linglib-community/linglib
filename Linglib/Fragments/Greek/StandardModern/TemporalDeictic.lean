module

public import Linglib.Semantics.Tense.Perspective

/-!
# Greek temporal deictic adverbs

Modern Greek *tote* 'then' is the distal temporal deictic adverb, referring to a past or future
time away from the deictic centre. It is a single adverb, distinct from the periphrastic
anaphoric expression *ekino ton kero* 'at that time'. The examples are those of
[tsilia-zhao-2026].

## References

* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Greek.StandardModern.TemporalDeictic

open scoped Denotes

open Tense

/-- *tote* (τότε) 'then', a time before or after the deictic centre: *To 2000, o Yanis ithele i
Maria na mini egkios tote* 'In 2000, Yanis wanted Maria to get pregnant then'. -/
def tote : DeicticAdverb := { form := "tote", cell := ⟦present⟧ᶜ }

end Greek.StandardModern.TemporalDeictic
