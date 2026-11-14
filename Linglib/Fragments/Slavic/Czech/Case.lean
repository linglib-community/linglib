module

public import Linglib.Syntax.Case.Basic

/-!
# Czech case

This file defines the seven Czech cases: "The full seven cases survive" (Short, p. 465). About half
the singular noun paradigms have a vocative "shared by no other case", and "no adjectival,
pronominal, numeral or plural noun paradigms have distinct vocative forms (vocative = nominative)"
(p. 465). A singular noun paradigm without a distinct vocative may share it with a case other than
the nominative, as *muži* 'man' and *stroji* 'machine' do with the dative and the locative (p. 466).

## References

* [short-1993-czech]
-/

@[expose] public section

namespace Czech

/-- The seven Czech cases. -/
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

end Czech
