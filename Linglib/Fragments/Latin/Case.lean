module

public import Linglib.Syntax.Case.Basic

/-!
# Latin case

The traditional description of Latin has six cases: nominative, vocative, accusative, genitive,
dative and ablative. The vocative is a form of address standing outside the clause, and it is
distinct from the nominative only in the singular of non-neuter second-declension nouns
(`Latin.Declension`).

The ablative continues three cases that were once distinct, an ablative, a locative and an
instrumental, and it expresses source, location and instrument accordingly. A separate locative
survives for names of towns and a few nouns such as *domī* 'at home'. The goal of motion is
expressed by the accusative, there being no allative. Blake takes Latin as his running example
of an inflectional case system.

## Main definitions

* `Latin.Case`: the six cases, in the order of the school paradigms.
* `Latin.Case.label`, `Latin.Case.functions`: the comparative value each case is named for, and
  the values it expresses.

## References

* [blake-1994]
-/

@[expose] public section

namespace Latin

/-- The six cases, in the order of the school paradigms. -/
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
  /-- The ablative. -/
  | abl
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | voc => .voc
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | abl => .abl

/-- The comparative values a case expresses: the accusative also expresses the goal of motion,
and the ablative location and instrument as well as source. -/
def functions : Case → Finset _root_.Case
  | acc => {.acc, .all}
  | abl => {.abl, .loc, .inst}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

end Case

end Latin
