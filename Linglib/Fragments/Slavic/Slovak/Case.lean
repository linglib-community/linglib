module

public import Linglib.Syntax.Case.Basic

/-!
# Slovak case

This file defines the Slovak cases, the six the Slavic languages share: "The case system has shrunk
from seven members to six, the vocative being replaced by the nominative. Some vocative forms
survive, but are not considered part of their respective paradigms" ([short-1993-slovak], p. 540).

## References

* [short-1993-slovak]
-/

@[expose] public section

namespace Slovak

/-- The six Slovak cases. -/
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

end Slovak
