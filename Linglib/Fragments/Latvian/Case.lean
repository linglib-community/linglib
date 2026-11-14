module

public import Linglib.Syntax.Case.Basic

/-!
# Latvian case

Latvian has seven cases, the nominative, genitive, dative, accusative, instrumental, locative and
vocative, encoded by endings ([kalnaca-lokmane-2021] §2.1.4, p. 104). The instrumental has
become homonymous with the accusative in the singular and with the dative in the plural, and
only the preposition *ar* 'with' tells them apart (p. 118). It is the standard example of a case
value with no form of its own, kept so that a preposition governs one case whatever the number
([corbett-2015] §3.6).

## Main definitions

* `Latvian.Case`, `Latvian.Case.label`: the seven cases, and the comparative value each is named
  for.

## References

* [kalnaca-lokmane-2021]
* [corbett-2015]
-/

@[expose] public section

namespace Latvian

/-- The seven cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The accusative. -/
  | acc
  /-- The instrumental, the case the preposition *ar* 'with' governs. -/
  | inst
  /-- The locative. -/
  | loc
  /-- The vocative. -/
  | voc
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | gen => .gen
  | dat => .dat
  | acc => .acc
  | inst => .inst
  | loc => .loc
  | voc => .voc

end Latvian
