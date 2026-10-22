module

public import Linglib.Semantics.Conditionals.Reading
public import Linglib.Semantics.Modality.XMarking

/-!
# Japanese conditional markers

The Japanese conditional markers *-ra* ~ *-tara*, *nara* and *-(e)ba*, typed by
`Conditional.Marker`, and the language's X-marking exponent. Lassiter finds that *-ra* marks only
hypothetical conditionals and *nara*, which doubles as a topic marker, either reading. Mizuno
records *-(e)ba* heading counterfactual, Anderson and future-less-vivid conditionals, which the
consequent's tense rather than the marker distinguishes.

## References

* [lassiter-2025]
* [mizuno-2024]
* [ogihara-2014]
* [mizuno-kaufmann-2019]
-/

@[expose] public section

namespace Japanese.Conditionals

/-- Japanese *-ra* ~ *-tara* marks only hypothetical conditionals: it is unacceptable once the
antecedent has been asserted (17) and as the main marker of a bare left-nested conditional
(19) ([lassiter-2025]). -/
def ra : Conditional.Marker where
  morphs := [.suff "ra"]
  readings := .pure {.hypothetical}

/-- Japanese *nara* marks either reading: it takes the premise reading when the antecedent
has been asserted (16) and heads a bare left-nested conditional (18) ([lassiter-2025]). -/
def nara : Conditional.Marker where
  morphs := [.encl "nara"]
  readings := .pure {.hypothetical, .premise}

/-- Japanese *-(e)ba* attaches to sentence radicals and is attested in hypothetical conditionals:
the counterfactual (3), the Anderson conditional (4a), and the future-less-vivid conditional (9a)
of [mizuno-2024]. The source records nothing on a premise reading. -/
def eba : Conditional.Marker where
  morphs := [.suff "(e)ba"]
  readings := ⟨({.hypothetical}, ⊤), le_top⟩

/-- Japanese X-marking is the fake past *-ta* ([ogihara-2014], [mizuno-kaufmann-2019];
[mizuno-2024] ex. 3). -/
def xMarking : Option Modality.XMarking.XMarkingExponent := some ⟨"-ta", [.past]⟩

end Japanese.Conditionals
