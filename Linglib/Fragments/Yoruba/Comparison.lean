module

public import Linglib.Syntax.Comparative

/-!
# Yoruba comparison

Yoruba compares with *X Adj ju Y lọ*, an exceed comparative in the atlas: the exceed verb
*ju … lọ* takes the standard as its object, between its two pieces. The adjective carries no
degree marking, and the superlative exceeds a universal standard.

## References

* [stassen-2013]
-/

@[expose] public section

namespace Yoruba.Comparison

open Comparative

/-- The *ju … lọ* comparative, whose exceed verb takes the standard as its object. -/
def ju : Comparative :=
  { standardMarker := [.free "ju", .free "lo"]
  , standard := .directObject }

end Yoruba.Comparison
