module

public import Linglib.Syntax.Case.Basic

/-!
# Ancient Greek case

Ancient Greek has five cases: nominative, vocative, accusative, genitive and dative. Its dative
does not correspond closely to the Latin dative. Greek has no ablative, and of the functions of
the Latin ablative the genitive expresses source, while the dative expresses location and
instrument beside the indirect object, so that the Greek dative is the more comprehensive case.
Blake gives the system, vocative aside, as the four-case stage of his hierarchy.

## Main definitions

* `Greek.Ancient.Case`: the five cases.
* `Greek.Ancient.Case.label`, `Greek.Ancient.Case.functions`: the comparative value each case is
  named for, and the values it expresses.

## References

* [blake-1994]
-/

@[expose] public section

namespace Greek.Ancient

/-- The five cases. -/
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
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- The comparative values a case expresses: the genitive also expresses source, and the dative
location and instrument as well as the indirect object. -/
def functions : Case → Finset _root_.Case
  | gen => {.gen, .abl}
  | dat => {.dat, .loc, .inst}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

end Case

end Greek.Ancient
