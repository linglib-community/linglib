module

public import Linglib.Semantics.Tense.Connective

/-!
# German temporal connectives

The lexical entry for the German *until* word of Karttunen's chart (37), the durative *bis*, which
has no punctual negative-polarity use with a phrase (his footnote records an incipient one before
a clause). The punctual *until*'s presupposition of lateness falls to *erst* 'only then' (his
(38)), a focus particle rather than a connective, entered in `German.PolarityItems`. Giannakidou
finds Dutch *tot* and *pas* patterning the same way.

## References

* [karttunen-1974]
* [giannakidou-2002]
-/

@[expose] public section

namespace German.TemporalConnectives

open Tense

/-- *bis* is the durative 'until', as in *die Prinzessin schlief bis 9 Uhr* 'the princess slept
until nine'. -/
def bis : Connective := { form := "bis", relation := .until_ }

end German.TemporalConnectives
