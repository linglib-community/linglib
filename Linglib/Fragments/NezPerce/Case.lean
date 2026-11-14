module

public import Linglib.Syntax.Case.Basic

/-!
# Nez Perce case

This file defines the cases of the Nez Perce relative-pronoun paradigm, the nominative, the
ergative and the accusative ([deal-2016a], reproduced in [deal-2026] (22)).

## Implementation notes

The cases are the three of the paradigm; the other cases of the language are not recorded.

## References

* [deal-2016a]
* [deal-2026]
-/

@[expose] public section

namespace NezPerce

/-- The cases of the relative-pronoun paradigm. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The ergative. -/
  | erg
  /-- The accusative. -/
  | acc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | erg => .erg
  | acc => .acc

end NezPerce
