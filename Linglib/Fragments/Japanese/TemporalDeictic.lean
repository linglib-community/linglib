module

public import Linglib.Semantics.Tense.Perspective

/-!
# Japanese temporal deictic adverbs

Japanese *tōji* 'then, at that time' refers to a time before the deictic centre. Unlike English
*then* it is used only of past times: for a future meeting one says *sonotoki ai-mashou* 'see you
then', not *tooji ai-mashou*. The description and examples follow [tsilia-zhao-2026].

## References

* [tsilia-zhao-2026]
-/

@[expose] public section

namespace Japanese.TemporalDeictic

open scoped Denotes

open Tense

/-- *tōji* 当時 'then', a time before the deictic centre. -/
def tooji : DeicticAdverb := { form := "tōji", cell := ⟦past⟧ }

end Japanese.TemporalDeictic
