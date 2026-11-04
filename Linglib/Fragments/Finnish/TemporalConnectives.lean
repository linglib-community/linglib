module

public import Linglib.Semantics.Tense.Connective

/-!
# Finnish temporal connectives

Lexical entries for the Finnish temporal connectives: *ennen* and *ennen kuin* 'before',
*jälkeen* 'after', *kun* 'when' with its compounds *sillä aikaa kun* 'while', *aina kun*
'whenever' and *heti kun* 'as soon as', and the durative *kunnes* and *saakka* 'until'. Finnish
separates Karttunen's two *until*s and, uniquely in his sample, has both polarities of the
punctual one: the negated *ennen kuin*, whose form is that of *before*, and the positive polarity
item *vasta* 'only then', the twin of German *erst* (his (37) and (39)), which is a focus particle
rather than a connective and is entered in `Finnish.PolarityItems`.

## References

* [heinamaki-1974]
* [karttunen-1974]
-/

@[expose] public section

namespace Finnish.TemporalConnectives

open Tense

/-- *ennen* 'before', the preposition. -/
def ennen : Connective := { form := "ennen", relation := .before }

/-- *ennen kuin* 'before', literally 'before than', the conjunction; negated, it is the punctual
*until* of *prinsessa ei herännyt ennen kuin yhdeksältä* 'the princess did not wake up until
nine'. -/
def ennenKuin : Connective := { form := "ennen kuin", relation := .before }

/-- *jälkeen* 'after'. -/
def jälkeen : Connective := { form := "jälkeen", relation := .after }

/-- *kun* 'when'. -/
def kun : Connective := { form := "kun", relation := .when_ }

/-- *sillä aikaa kun* 'while', literally 'in that time when'. -/
def silläAikaaKun : Connective := { form := "sillä aikaa kun", relation := .while_ }

/-- *aina kun* 'whenever', literally 'always when'. -/
def ainaKun : Connective := { form := "aina kun", relation := .whenever }

/-- *heti kun* 'as soon as', literally 'immediately when'. -/
def hetiKun : Connective := { form := "heti kun", relation := .asSoonAs }

/-- *kunnes*, the durative 'until', the conjunction. -/
def kunnes : Connective := { form := "kunnes", relation := .until_ }

/-- *saakka*, the durative 'until', the postposition. -/
def saakka : Connective := { form := "saakka", relation := .until_ }

end Finnish.TemporalConnectives
