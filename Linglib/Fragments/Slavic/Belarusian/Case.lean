module

public import Linglib.Syntax.Case.Basic

/-!
# Belarusian case

This file defines the Belarusian cases, the six the Slavic languages share. "Modern standard
Belorussian has two numbers, six cases and three genders", and "The vocative case can no longer be
regarded as a living category in the standard language, which has only the remnants божа/boža from
бог/boh 'god' (as an exclamation) and браце/brace from брат/brat 'brother', дружа/druža from
друг/druh 'friend' and сынку/synku (with stress shift) from сынок/synók 'son' (as modes of address)"
([mayo-1993], p. 900).

## References

* [mayo-1993]
-/

@[expose] public section

namespace Belarusian

/-- The six Belarusian cases. -/
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

end Belarusian
