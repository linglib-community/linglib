module

public import Eval.Basic
public import Eval.Suppletion.Theory
public import Studies.SmithMoskalEtAl2019

/-!
# Scoring theories of root suppletion on Smith, Moskal, Xu, Kang and Bobaljik (2019)

The data are the pronoun paradigms the paper analyzes, read from `Data/Forms/SmithMoskalEtAl2019`
(`SmithMoskalEtAl2019.paradigm`). Over the case hierarchy the Wardaman third singular and the
Khinalugh second singular are AAB, the Icelandic and Russian first singular ABB and the Lezgian
first singular AAA; over the number hierarchy the Awtuw first person is ABB and the Yagua second
person, the Wambaya first inclusive and the Dehu third masculine are AAB. The theories of
`Eval.Suppletion.Theory`, stated for any three-cell containment hierarchy, are scored on them as on
the grades of [bobaljik-2012].

Paradigm by paradigm (`pronounCase`, `pronounNumber`), a theory is right on an attested paradigm it generates
and wrong on one it does not: grounded containment, which excludes AAB, is wrong on the five AAB
paradigms, and the other theories are right on all nine. Pattern by pattern (`pronounPatterns`), with the
asymmetric linking hypothesis of the degree experiment, grounded containment is wrong that no
pronoun is AAB, where it is right for degree, and both containment theories are right that none of
these paradigms is ABA.

## References

* [smith-moskal-xu-kang-bobaljik-2019]
* [bobaljik-2012]
-/

@[expose] public section

namespace Eval.Suppletion.SmithMoskalEtAl2019

open Morphology
open _root_.SmithMoskalEtAl2019 (wardaman3sg khinalugh2sg icelandic1sg russian1sg lezgian1sg awtuw1
  yagua2 wambaya1incl dehu3m)

/-- The pronoun paradigms over the case hierarchy. -/
def caseParadigms : List (Paradigm 3 ℕ) :=
  [wardaman3sg, khinalugh2sg, icelandic1sg, russian1sg, lezgian1sg]

/-- The pronoun paradigms over the number hierarchy. -/
def numberParadigms : List (Paradigm 3 ℕ) := [awtuw1, yagua2, wambaya1incl, dehu3m]

/-- Each case paradigm of [smith-moskal-xu-kang-bobaljik-2019] scored by whether a theory
generates its pattern. -/
def pronounCase : Experiment Theory (Paradigm 3 ℕ) Bool where
  observed p := if p ∈ caseParadigms then some true else none
  predicted T p := some (decide (T.Fits id p))

/-- Each number paradigm of [smith-moskal-xu-kang-bobaljik-2019] scored by whether a theory
generates its pattern. -/
def pronounNumber : Experiment Theory (Paradigm 3 ℕ) Bool where
  observed p := if p ∈ numberParadigms then some true else none
  predicted T p := some (decide (T.Fits id p))

/-- Each root pattern scored by whether a pronoun paradigm of
[smith-moskal-xu-kang-bobaljik-2019] shows it, with the asymmetric linking hypothesis: a theory
predicts the absence of each pattern it cannot generate. -/
def pronounPatterns : Experiment Theory (Paradigm 3 ℕ) Bool where
  observed c :=
    some (decide (∃ p ∈ caseParadigms ++ numberParadigms, Setoid.ker p = Setoid.ker c))
  predicted T c := if T.Generates c then none else some false

theorem pronounCase_observed :
    pronounCase.observed wardaman3sg = some true ∧ pronounCase.observed khinalugh2sg = some true ∧
      pronounCase.observed icelandic1sg = some true ∧ pronounCase.observed russian1sg = some true ∧
      pronounCase.observed lezgian1sg = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem pronounNumber_observed :
    pronounNumber.observed awtuw1 = some true ∧ pronounNumber.observed yagua2 = some true ∧
      pronounNumber.observed wambaya1incl = some true ∧ pronounNumber.observed dehu3m = some true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Every theory generates the ABB and AAA case paradigms. -/
theorem verdict_pronounCase_contiguous (T : Theory) :
    pronounCase.verdict T icelandic1sg = .correct ∧ pronounCase.verdict T russian1sg = .correct ∧
      pronounCase.verdict T lezgian1sg = .correct := by
  cases T <;> refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The AAB case paradigms refute grounded containment alone. -/
theorem verdict_pronounCase_aab :
    pronounCase.verdict .elsewhere wardaman3sg = .correct ∧
      pronounCase.verdict .grounded wardaman3sg = .wrong ∧
      pronounCase.verdict .free wardaman3sg = .correct ∧
      pronounCase.verdict .elsewhere khinalugh2sg = .correct ∧
      pronounCase.verdict .grounded khinalugh2sg = .wrong ∧
      pronounCase.verdict .free khinalugh2sg = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Every theory generates the ABB number paradigm, and the AAB ones refute grounded containment
alone. -/
theorem verdict_pronounNumber :
    pronounNumber.verdict .elsewhere awtuw1 = .correct ∧ pronounNumber.verdict .grounded awtuw1 = .correct ∧
      pronounNumber.verdict .free awtuw1 = .correct ∧
      pronounNumber.verdict .elsewhere yagua2 = .correct ∧ pronounNumber.verdict .grounded yagua2 = .wrong ∧
      pronounNumber.verdict .free yagua2 = .correct ∧
      pronounNumber.verdict .elsewhere wambaya1incl = .correct ∧
      pronounNumber.verdict .grounded wambaya1incl = .wrong ∧
      pronounNumber.verdict .free wambaya1incl = .correct ∧
      pronounNumber.verdict .elsewhere dehu3m = .correct ∧ pronounNumber.verdict .grounded dehu3m = .wrong ∧
      pronounNumber.verdict .free dehu3m = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Some pronoun paradigm is AAB, and none of these is ABA. -/
theorem pronounPatterns_observed :
    pronounPatterns.observed Paradigm.aab = some true ∧ pronounPatterns.observed Paradigm.aba = some false := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Grounded containment is wrong that no pronoun is AAB, where Elsewhere insertion predicts
nothing; both are right that none is ABA; the theory without containment predicts nothing. -/
theorem verdict_pronounPatterns :
    pronounPatterns.verdict .grounded Paradigm.aab = .wrong ∧
      pronounPatterns.verdict .elsewhere Paradigm.aab = .silent ∧
      pronounPatterns.verdict .free Paradigm.aab = .silent ∧
      pronounPatterns.verdict .grounded Paradigm.aba = .correct ∧
      pronounPatterns.verdict .elsewhere Paradigm.aba = .correct ∧
      pronounPatterns.verdict .free Paradigm.aba = .silent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Eval.Suppletion.SmithMoskalEtAl2019
