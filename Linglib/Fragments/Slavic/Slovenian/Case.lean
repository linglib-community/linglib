module

public import Linglib.Syntax.Case.Basic

/-!
# Slovene case

This file defines the Slovene cases, the six the Slavic languages share: "There are six cases:
nominative, accusative, genitive, dative, instrumental and locative. There is no separate vocative
case" ([priestly-1993], p. 399). The locative and the instrumental occur only in prepositional
phrases. The directory is named for Slovenian; Priestly's chapter is "Slovene".

## References

* [priestly-1993]
-/

@[expose] public section

namespace Slovenian

/-- The six Slovene cases. -/
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

end Slovenian
