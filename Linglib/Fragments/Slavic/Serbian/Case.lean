module

public import Linglib.Syntax.Case.Basic

/-!
# Serbo-Croat case

This file defines the seven Serbo-Croat cases: "There are seven cases: nominative, vocative,
accusative, genitive, dative, instrumental, locative. Dative and locative have merged; only certain
inanimate monosyllabic nouns distinguish them accentually in the singular" ([browne-1993], p. 318).
The directory is named for Serbian; Browne's chapter describes the Serbo-Croat standard.

## References

* [browne-1993]
-/

@[expose] public section

namespace Serbian

/-- The seven Serbo-Croat cases. -/
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

end Serbian
