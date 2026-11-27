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
context in which it stands, and [the entry says of that context what the example
shows](##ButtEtAl2019.verdict_eq_verdictOf). The questions aside, [the verdicts on four of the
words are those of the weak class](##ButtEtAl2019.classVerdict_weak). *Jamás* follows a superlative
and not a comparison, and [no strength class has both
verdicts](##ButtEtAl2019.jamás_comparative).

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

/-- The verdict that the judgment of an example gives on its context. -/
def verdictOf : Judgment → Option Obligatoriness
  | .acceptable => some .optional
  | .ungrammatical => some .excluded
  | _ => none

/-- The entry of each item says of each context what the example in that context shows. -/
theorem verdict_eq_verdictOf :
    ∀ p ∈ links, p.2.item.verdict p.2.context = verdictOf p.1.judgment := by
  decide +kernel

-- Each context that an entry lists is the context of an example of the item.
theorem contexts_linked :
    ∀ e ∈ items, ∀ q ∈ e.contexts, ∃ p ∈ links, p.2.item.form = e.form ∧ p.2.context = q.1 := by
  decide +kernel

/-- The questions aside, the verdicts on *nadie*, *nada*, *ninguno*, and *nunca* are those of the
weak class. A question places no operator over the item. -/
theorem classVerdict_weak :
    ∀ e ∈ [nadie, nada, ninguno, nunca], ∀ q ∈ e.contexts,
      q.1 ∉ [.polarQuestion, .constituentQuestion] → q.2 = q.1.classVerdict .weak := by
  decide +kernel

/-- *Jamás* follows a superlative and cannot follow a comparison. No strength class has both
verdicts, since a class that takes the superlative is the weak class, which takes the
comparison. -/
theorem jamás_comparative :
    tempranoJamas.judgment = .ungrammatical ∧
      ∀ s, ∃ q ∈ jamás.contexts, q.1 ∉ [.polarQuestion, .constituentQuestion] ∧
        q.2 ≠ q.1.classVerdict s := by
  refine ⟨rfl, fun s ↦ ?_⟩
  cases s <;> decide +kernel

end ButtEtAl2019
