module

public import Linglib.Syntax.Case.Basic

/-!
# Ukrainian case

This file defines the seven Ukrainian cases: "Ukrainian preserves the original set of cases:
nominative, accusative, genitive, dative, instrumental and locative. In addition, the vocative is
preserved even though the vocative singular in colloquial speech is occasionally replaced by the
nominative and in the plural the vocative has no forms of its own, except in the word панове/panove
'gentlemen'" ([shevelov-1993], p. 956).

## References

* [shevelov-1993]
-/

@[expose] public section

namespace Ukrainian

/-- The seven Ukrainian cases. -/
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

end Ukrainian
