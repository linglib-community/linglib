module

public import Linglib.Syntax.Case.Basic

/-!
# Cassubian case

This file defines the seven Cassubian cases: "The seven cases are the same as in Polish, but the
tendency for the nominative to replace the vocative is greater than in Polish. The locative never
occurs without a preposition, and there is a strong tendency for the instrumental to acquire the
preposition z(s)/ze(se) 'with', when used with its basic function as an expression of instrument
(but not in the complement of the copula)" ([stone-1993-cassubian], p. 768).

## References

* [stone-1993-cassubian]
-/

@[expose] public section

namespace Cassubian

/-- The seven Cassubian cases. -/
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

end Cassubian
