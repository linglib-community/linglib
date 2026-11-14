module

public import Linglib.Syntax.Case.Basic

/-!
# German case

This file defines the German cases and the forms of a German case paradigm. German has four
cases, the nominative, the accusative, the genitive and the dative. The noun itself shows
little of them: a regular noun adds *-(e)s* in the genitive singular of the masculine and the
neuter and *-n* in the dative plural, and nothing else. Case is marked chiefly on the determiners
and the adjectives of the noun phrase, together with its gender and number, as Durrell describes
(`German.Determiners`, `German.Adjectives`). Blake gives the system as the four-case stage of his
hierarchy.

## Main definitions

* `German.Case`, `German.Case.label`: the four cases, and the comparative value each is named for.
* `German.Case.forms`: the forms of the four in the order of the school paradigms.

## References

* [durrell-2011]
* [blake-1994]
-/

@[expose] public section

namespace German

/-- The four cases, in the order of the school paradigms. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- `forms nom acc gen dat` assigns each case its form. -/
def forms {α : Type*} (nom acc gen dat : α) : Case → α
  | .nom => nom
  | .acc => acc
  | .gen => gen
  | .dat => dat

end Case

end German
