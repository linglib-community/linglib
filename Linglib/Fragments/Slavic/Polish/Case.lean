module

public import Linglib.Syntax.Case.Basic

/-!
# Polish case

This file defines the seven Polish cases: "Polish has preserved the full inherited case system,
including the vocative, but there is a growing tendency to use the nominative instead of the
vocative for personal names. The vocative is consistently used with titles and with personal names
when they are used as part of a vocative phrase" ([rothstein-1993], p. 696), as in *panie Janku* and
*kochana Basiu* 'dear Basia'.

## References

* [rothstein-1993]
-/

@[expose] public section

namespace Polish

/-- The seven Polish cases. -/
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

end Polish
