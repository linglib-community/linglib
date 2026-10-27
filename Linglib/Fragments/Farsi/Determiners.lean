module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Farsi indefinite determiners

Farsi marks an indefinite noun phrase with the numeral *yek* 'one', *ye* in the informal
register, with the enclitic *-i* on the noun, or with both, which Alonso-Ovalle and Moghiseh
call *yek-i* DPs. Mirrazi's examples alternate *ye* with the plural *čand-ta* 'some', the
quantity word *čand* with the classifier *-ta*. Forms are romanized, with the Persian spelling
in the docstrings.

## Main definitions

* `Farsi.Determiners.yek`, `Farsi.Determiners.ye`, `Farsi.Determiners.i`,
  `Farsi.Determiners.candTa`: the indefinite determiners.

## References

* [alonso-ovalle-moghiseh-2025a]
* [mirrazi-2024]
-/

@[expose] public section

namespace Farsi.Determiners

/-- *yek* یک 'one' marks an indefinite. -/
def yek : Article :=
  { form := "yek", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- *ye* یه is the informal form of *yek*. -/
def ye : Article :=
  { form := "ye", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- The enclitic *-i* ـی marks an indefinite on the noun. -/
def i : Article :=
  { form := "-i", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- *čand-ta* چندتا 'some', the quantity word *čand* with the classifier *-ta*, marks a plural
indefinite. -/
def candTa : Article :=
  { form := "čand-ta", definiteness := .indefinite, exponent := .numeralClassifier,
    numberRestriction := some .plural }

end Farsi.Determiners
