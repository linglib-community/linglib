module

public import Linglib.Semantics.Tense.Connective

/-!
# Dutch temporal connectives

The lexical entry for the Dutch *until* word, the durative *tot*, which does not combine with
negation. The place of a punctual *until* falls to *pas* 'only then', a focus particle rather than
a connective, entered in `Dutch.PolarityItems`, which contributes *not before* without a negation,
by Giannakidou's (47). Karttunen treats the parallel German *erst* alike.

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

@[expose] public section

namespace Dutch.TemporalConnectives

open Tense

/-- *tot* is the durative 'until', *Marie wachtte tot 9 uur* 'Marie waited until nine'. -/
def tot : Connective := { form := "tot", relation := .until_ }

end Dutch.TemporalConnectives
