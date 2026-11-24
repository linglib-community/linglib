module

public import Linglib.Semantics.Tense.Connective

/-!
# Icelandic temporal connectives

Lexical entries for the Icelandic *until* words, which Giannakidou takes to lexicalize
Karttunen's two *until*s without overt aspect on the verb (her (43)–(46), from Gunnar Hansson):
the durative *(þangað) til*, and *fyrr en*, literally 'earlier than', the punctual *until* that
needs the negation *ekki*.

## References

* [giannakidou-2002]
* [karttunen-1974]
-/

@[expose] public section

namespace Icelandic.TemporalConnectives

open Tense

/-- *(þangað) til* is the durative 'until', as in *prinsessan svaf þangað til klukkan fimm* 'the
princess slept until five'. -/
def thangadTil : Connective := { form := "þangað til", relation := .until_ }

/-- *fyrr en* 'earlier than' is the punctual 'until' of a negated clause, as in *prinsessan kom
ekki fyrr en klukkan fimm* 'the princess did not arrive until five'. -/
def fyrrEn : Connective := { form := "fyrr en", relation := .until_ }

end Icelandic.TemporalConnectives
