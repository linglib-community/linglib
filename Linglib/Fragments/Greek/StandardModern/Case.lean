module

public import Linglib.Syntax.Case.Basic

/-!
# Modern Greek case

Standard Modern Greek has four cases: nominative, accusative, genitive and vocative. The dative
of Ancient Greek (`Greek.Ancient.Case`) is gone, and the indirect object of a ditransitive is a
genitive, beside a prepositional phrase in *se* with the accusative. Blake counts the system,
vocative aside, as a nominative–accusative–genitive system. The endings that distinguish the four
cases are in `Greek.StandardModern.Declension`.

## Main definitions

* `Greek.StandardModern.Case`: the four cases.
* `Greek.StandardModern.Case.label`, `Greek.StandardModern.Case.functions`: the comparative value
  each case is named for, and the values it expresses.

## References

* [blake-2001]
* [michelioudakis-sitaridou-2010]
* [ralli-2000]
* [sims-2006]
-/

@[expose] public section

namespace Greek.StandardModern

/-- The four cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The vocative. -/
  | voc
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | voc => .voc

/-- The comparative values a case expresses: the genitive also expresses the indirect object
([michelioudakis-sitaridou-2010] (1a)). -/
def functions : Case → Finset _root_.Case
  | gen => {.gen, .dat}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

theorem biUnion_functions_eq_insert_dat :
    Finset.univ.biUnion functions = insert .dat (Finset.univ.image label) := by
  decide

end Case

end Greek.StandardModern
