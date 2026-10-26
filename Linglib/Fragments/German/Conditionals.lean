module

public import Linglib.Semantics.Conditionals.Typology

/-!
# German conditional markers

The German conditional markers *wenn* and *falls*, typed by `Conditional.Marker`. Lassiter finds
that *wenn* marks either reading and *falls* only hypothetical conditionals.

## References

* [lassiter-2025]
-/

@[expose] public section

namespace German.Conditionals

/-- German *falls* 'in case' marks only hypothetical conditionals: it is unacceptable once the
antecedent has been asserted (22) and as the main marker of a bare left-nested conditional
(24) ([lassiter-2025]). -/
def falls : Conditional.Marker where
  morphs := [.free "falls"]
  readings := .pure {.hypothetical}

/-- German *wenn* 'if, when' marks either reading, and heads a bare left-nested conditional
(23) ([lassiter-2025]). -/
def wenn : Conditional.Marker where
  morphs := [.free "wenn"]
  readings := .pure {.hypothetical, .premise}

end German.Conditionals
