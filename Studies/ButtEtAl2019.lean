module

public import Linglib.Languages.Romance.Spanish.PolarityItems
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
context in which it stands, and [the entry lists that context as the example
shows](##ButtEtAl2019.entries_agree). [The entries of four of the words are compatible with the
class of weak negative polarity items](##ButtEtAl2019.compatible_weak). *Jamás* follows a
superlative and not a comparison, and [its entry is compatible with no
class](##ButtEtAl2019.jamás_comparative).

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
    (preguntado, ⟨nada, .constituentQuestion⟩), (quienHaVisto, ⟨nadie, .constituentQuestion⟩),
    (despedirme, ⟨nada, .constituentQuestion⟩), (despedirme, ⟨nadie, .constituentQuestion⟩),
    (pensar, ⟨nada, .constituentQuestion⟩), (julia, ⟨nunca, .constituentQuestion⟩),
    (juliaJamas, ⟨jamás, .constituentQuestion⟩),
    (sinNada, ⟨nada, .withoutClause⟩), (sinNadie, ⟨nadie, .withoutClause⟩),
    (antesQueNadie, ⟨nadie, .beforeClause⟩), (antesDe, ⟨nada, .beforeClause⟩),
    (insincero, ⟨ninguno, .conditionalAntecedent⟩), (noSaleNunca, ⟨nunca, .negation⟩),
    (noSaleJamas, ⟨jamás, .negation⟩), (seVio, ⟨jamás, .polarQuestion⟩)]

-- The item of each link is a word of its example, so a link to the wrong item fails.
theorem links_attested :
    ∀ p ∈ links, p.2.item.form.toList ∈ Datum.wordsOf p.1.primaryText := by
  decide +kernel

/-- The entry of each item lists the context of an acceptable example among those in which the
item is attested, and the context of a starred example among those from which it is excluded. -/
theorem entries_agree :
    ∀ p ∈ links, (p.1.judgment = .acceptable → p.2.context ∈ p.2.item.attested) ∧
      (p.1.judgment = .ungrammatical → p.2.context ∈ p.2.item.excluded) := by
  decide +kernel

-- Each context that an entry lists is the context of an example of the item.
theorem contexts_linked :
    ∀ e ∈ items, ∀ c ∈ e.attested ∪ e.excluded,
      ∃ p ∈ links, p.2.item.form = e.form ∧ p.2.context = c := by
  decide +kernel

/-- The entries of *nadie*, *nada*, *ninguno*, and *nunca* are compatible with the class of weak
negative polarity items. -/
theorem compatible_weak :
    ∀ e ∈ [nadie, nada, ninguno, nunca], e.Compatible (.npi .weak) := by
  decide +kernel

/-- *Jamás* follows a superlative and cannot follow a comparison, so its entry is compatible with
no class: a class that is possible after a superlative is possible after a comparison. -/
theorem jamás_comparative :
    tempranoJamas.judgment = .ungrammatical ∧ ∀ k, ¬ jamás.Compatible k := by
  decide +kernel

end ButtEtAl2019
