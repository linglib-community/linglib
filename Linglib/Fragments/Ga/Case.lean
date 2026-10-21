module

public import Linglib.Syntax.Case.Basic

/-!
# Gã case

This file defines the three cases of [allotey-2021]'s Table 3, the subjective, the objective and
the possessive, which the table labels nominative, accusative and genitive.

## References

* [allotey-2021]
-/

@[expose] public section

namespace Ga

/-- The cases of [allotey-2021]'s Table 3. -/
inductive Case where
  /-- The subjective. -/
  | subjective
  /-- The objective. -/
  | objective
  /-- The possessive. -/
  | possessive
  deriving DecidableEq, Fintype, Repr

/-- The comparative value Table 3 gives each case. -/
def Case.label : Case → _root_.Case
  | subjective => .nom
  | objective => .acc
  | possessive => .gen

end Ga
