module

public import Linglib.Syntax.Case.Basic

/-!
# Sorbian cases

This file defines the cases of Upper and of Lower Sorbian: "Upper Sorbian has seven cases
(nominative, vocative, accusative, genitive, dative, instrumental and locative). Lower Sorbian,
having lost the vocative, has only six cases" ([stone-1993-sorbian], p. 614). Even in Upper Sorbian
only masculine nouns have a separate vocative form, and only in the singular, save *mać* 'mother',
vocative *maći*. In both languages the instrumental has lost its prepositionless function.

## References

* [stone-1993-sorbian]
-/

@[expose] public section

namespace Sorbian.Upper

/-- The seven Upper Sorbian cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The vocative. -/
  | voc
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The instrumental. -/
  | inst
  /-- The locative. -/
  | loc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | inst => .inst
  | loc => .loc

end Sorbian.Upper

namespace Sorbian.Lower

/-- The six Lower Sorbian cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The instrumental. -/
  | inst
  /-- The locative. -/
  | loc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | inst => .inst
  | loc => .loc

end Sorbian.Lower
