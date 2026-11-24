module

public import Linglib.Syntax.Negation

/-!
# Italian negation

Italian negates a clause with the preverbal particle *non*, and nothing else in the clause changes,
in any person or tense: *canto* 'I sing', *non canto* 'I do not sing'. Object clitics stand between
*non* and the verb. The same *non* occurs expletively, contributing no negation, under *prima che*
'before', *dubitare* 'doubt', *appena* 'hardly', *per poco* 'nearly', *di quanto* 'than', *a meno
che* 'unless', *finché* 'until' and *senza che* 'without', the triggers Jin and Koenig record for
the language. The colloquial *mica*, from the Latin minimizer *micam* 'crumb', co-occurs with *non*,
*Gianni non ha mica la macchina* 'Gianni hasn't got a car', or replaces it before the verb, *Mica fa
freddo* 'It's not cold'. It is felicitous only when the positive counterpart of the sentence is
assumed in the discourse, a presuppositional negative marker in Zanuttini's analysis, and before the
verb only when that expectation is the addressee's, as Maiden and Robustelli note; it also occurs in
polar questions, as Frana and Rawlins discuss. N-words and the other polarity-sensitive items are
entered in `Languages/Romance/Italian/PolarityItems.lean`. Miestamo's *cantare* paradigms are rows
of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
* [jin-koenig-2021]
* [zanuttini-1997]
* [maiden-robustelli-2007]
* [frana-rawlins-2019]
-/

@[expose] public section

open Negation

namespace Italian.Negation

/-- *non*, the standard negator. -/
def non : Marker := { pieces := [[.free "non"]] }

/-- The standard negators. -/
def standard : List Marker := [non]

end Italian.Negation
