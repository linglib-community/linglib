module

public import Linglib.Syntax.Comparative

/-!
# Thai comparison

Thai compares with *X Adj kwàa Y*, an exceed comparative in the atlas: *kwàa* 'exceed' takes the
standard as its object after the predicate. The adjective carries no degree marking, and the
superlative exceeds a universal standard.

## References

* [stassen-2013]
-/

@[expose] public section

namespace Thai.Comparison

open Comparative

/-- The *kwàa*-comparative, whose marker takes the standard as its object. -/
def kwaa : Comparative :=
  { standardMarker := [.free "kwaa"]
  , standard := .directObject }

/-- The superlative exceeds a universal standard. -/
def superlative : SuperlativeStrategy := .exceedAll

end Thai.Comparison
