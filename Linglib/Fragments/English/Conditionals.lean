module

public import Linglib.Semantics.Conditionals.Typology
public import Linglib.Semantics.Modality.XMarking

/-!
# English conditional markers

The English conditional marker *if*, typed by `Conditional.Marker`, and the language's
X-marking exponent, the fake past.

## References

* [iatridou-2000]
* [von-fintel-iatridou-2023]
-/

@[expose] public section

namespace English.Conditionals

/-- English *if* marks either reading; context decides between the hypothetical and the
premise reading. -/
def if_ : Conditional.Marker where
  morphs := [.free "if"]
  readings := .pure {.hypothetical, .premise}

/-- English X-marking is the fake past ([iatridou-2000]), with *woll* added in the consequent
([von-fintel-iatridou-2023] §2). -/
def xMarking : Option Modality.XMarking.XMarkingExponent := some ⟨"Past", [.past, .future]⟩

end English.Conditionals
