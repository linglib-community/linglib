module

public import Linglib.Syntax.Case.Function

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
  each case is named for, and the functions it marks.

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

/-- The functions a case marks: the genitive also expresses the indirect object
([michelioudakis-sitaridou-2010] (1a)). -/
def functions : Case → Finset _root_.Case.Function
  | gen => {.possessor, .argument .R}
  | c => c.label.functions

theorem label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

end Case

end Greek.StandardModern
