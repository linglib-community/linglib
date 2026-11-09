module

public import Linglib.Fragments.Romance.Spanish.PolarityItems
public import Linglib.Semantics.PolarityItem.LicensingContext
public import Linglib.Data.Examples.ButtEtAl2019
public import Linglib.Data.Examples.Readers

/-!
# Butt, Benjamin and Moreira Rodríguez (2019): Spanish negative words with positive meaning

The Spanish negative words *nadie*, *nada*, *ninguno*, *nunca*, and *jamás* require a negative
before the verb when they follow it. They also have the positive meanings 'anyone', 'anything', and
'ever' after comparisons, under expressions of doubt, denial, and impossibility, in questions that
expect the answer 'no', and after *antes de*, *antes que*, and *sin*. However, *jamás* never
follows a comparison. Each example is linked to the lexical entry it contains and to the named
context in which it stands. The licensing theory [admits every acceptable
example](##ButtEtAl2019.acceptable_admitted). It [also admits *jamás* after a
comparison](##ButtEtAl2019.jamás_comparative), a restriction that no strength class expresses.

## Implementation notes

* A comparison with a noun phrase after *que* is linked to the clausal comparative, which is where
  the licensing theory routes a surface *than NP*. *Negarse a* 'refuse' is linked to *deny*.
* The examples after *imposible*, *no tolerar*, and *no saber* stand in no named context and are
  not linked.

## References

* [butt-benjamin-2019]
-/

@[expose] public section

namespace ButtEtAl2019

open PolarityItem Spanish.PolarityItems Examples

/-- A link from an example to the lexical entry it contains and to the named context in which it
stands. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The context in which the item stands. -/
  context : LicensingContext

/-- The links of the examples. -/
def links : List (Datum × Link) :=
  [(noDiceNada, ⟨nada, .negation⟩), (nadieDijoNada, ⟨nada, .nobody⟩),
    (noLaHeVisto, ⟨nunca, .negation⟩), (noLaHeVisto, ⟨nadie, .negation⟩),
    (masQueNada, ⟨nada, .clausalComparative⟩), (meIrrite, ⟨nada, .clausalComparative⟩),
    (esfera, ⟨nunca, .superlative⟩), (temprano, ⟨nunca, .clausalComparative⟩),
    (tempranoJamas, ⟨jamás, .clausalComparative⟩), (capataz, ⟨jamás, .superlative⟩),
    (complicado, ⟨ninguno, .clausalComparative⟩), (lista, ⟨ninguno, .clausalComparative⟩),
    (tonteria, ⟨nadie, .superlative⟩), (dudoso, ⟨nadie, .doubtVerb⟩),
    (haceMucho, ⟨nadie, .sinceTemporal⟩), (sinNadaNiNadie, ⟨nada, .withoutClause⟩),
    (sinNadaNiNadie, ⟨nadie, .withoutClause⟩), (seNego, ⟨nadie, .denyVerb⟩),
    (demasiado, ⟨nadie, .tooTo⟩), (pocos, ⟨nada, .few⟩), (horrible, ⟨nadie, .adversative⟩),
    (preguntado, ⟨nada, .question⟩), (quienHaVisto, ⟨nadie, .question⟩),
    (despedirme, ⟨nada, .question⟩), (despedirme, ⟨nadie, .question⟩),
    (pensar, ⟨nada, .question⟩), (julia, ⟨nunca, .question⟩), (juliaJamas, ⟨jamás, .question⟩),
    (sinNada, ⟨nada, .withoutClause⟩), (sinNadie, ⟨nadie, .withoutClause⟩),
    (antesQueNadie, ⟨nadie, .beforeClause⟩), (antesDe, ⟨nada, .beforeClause⟩),
    (insincero, ⟨ninguno, .conditionalAntecedent⟩), (noSaleNunca, ⟨nunca, .negation⟩),
    (noSaleJamas, ⟨jamás, .negation⟩), (seVio, ⟨jamás, .question⟩)]

-- The item of each link is a word of its example, so a link to the wrong item fails.
theorem links_attested :
    ∀ p ∈ links, p.2.item.form.toList ∈ Datum.wordsOf p.1.primaryText := by
  decide +kernel

/-- The licensing theory admits the item of every acceptable example in the context in which it
stands. -/
theorem acceptable_admitted :
    ∀ p ∈ links, p.1.judgment = .acceptable → p.2.context.licenser.Admits p.2.item := by
  decide +kernel

/-- *Jamás* cannot follow a comparison. The licensing theory nevertheless admits it there, since it
admits every weak negative polarity item in an anti-additive context. -/
theorem jamás_comparative :
    tempranoJamas.judgment = .ungrammatical ∧
      LicensingContext.clausalComparative.licenser.Admits jamás := by
  decide

end ButtEtAl2019
