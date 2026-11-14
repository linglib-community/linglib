module

public import Linglib.Syntax.Case.Basic

/-!
# Russian case

This file defines the Russian cases, the six the Slavic languages share. [timberlake-1993] (p. 836)
takes Russian to have "six primary cases and two secondary cases (second genitive and second
locative), the secondary cases being available for a decreasing number of masculines", and finds the
historical vocative moribund. The cases here are the six primary ones; the secondary cases have
forms of their own in some masculines only, and are left out.

## References

* [timberlake-1993]
-/

@[expose] public section

namespace Russian

/-- The six Russian cases. -/
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

end Russian
