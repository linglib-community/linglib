module

public import Linglib.Semantics.Conditionals.Typology

/-!
# English conditional markers

The English conditional marker *if*, typed by `Conditional.Marker`.

## References

* [lassiter-2025]
-/

@[expose] public section

namespace English.Conditionals

/-- English *if* marks either reading; context decides between the hypothetical and the
premise reading ([lassiter-2025]). -/
def if_ : Conditional.Marker where
  morphs := [.free "if"]
  readings := .pure {.hypothetical, .premise}

end English.Conditionals
