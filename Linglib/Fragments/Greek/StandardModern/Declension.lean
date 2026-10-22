module

public import Linglib.Fragments.Greek.StandardModern.Case
public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod

/-!
# Modern Greek nominal declensions

The eight nominal inflection classes of Modern Greek by their case–number endings, after
Ralli's description as Ackerman and Malouf simplify it (stem alternations and stress set aside),
as a paradigm system whose classes are the paper's rows 1–8 and whose cells pair a number with
one of the four cases.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Greek.StandardModern.Declension

open Morphology

/-- The rows of the cells: the singular and the plural. -/
inductive Row where
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

/-- The number of a row. -/
def Row.number : Row → Number
  | .sg => .singular
  | .pl => .plural

/-- The nominative singular. -/
abbrev nomSg : Row × Case := (.sg, .nom)
/-- The genitive singular. -/
abbrev genSg : Row × Case := (.sg, .gen)
/-- The accusative singular. -/
abbrev accSg : Row × Case := (.sg, .acc)
/-- The vocative singular. -/
abbrev vocSg : Row × Case := (.sg, .voc)
/-- The nominative plural. -/
abbrev nomPl : Row × Case := (.pl, .nom)
/-- The genitive plural. -/
abbrev genPl : Row × Case := (.pl, .gen)
/-- The accusative plural. -/
abbrev accPl : Row × Case := (.pl, .acc)
/-- The vocative plural. -/
abbrev vocPl : Row × Case := (.pl, .voc)

/-- The endings of the eight declensions, rows 1–8 of the paper's Table 1, *-∅* the zero
ending. -/
def nominal : ParadigmSystem (Fin 8) (Row × Case) String := ![
  fun | (.sg, .nom) => "-os" | (.sg, .gen) => "-u" | (.sg, .acc) => "-on" | (.sg, .voc) => "-e"
      | (.pl, .gen) => "-on" | (.pl, .acc) => "-us" | (.pl, _) => "-i",
  fun | (.sg, .nom) => "-s" | (.sg, _) => "-∅" | (.pl, .gen) => "-on" | (.pl, _) => "-es",
  fun | (.sg, .gen) => "-s" | (.sg, _) => "-∅" | (.pl, .gen) => "-on" | (.pl, _) => "-es",
  fun | (.sg, .gen) => "-s" | (.sg, _) => "-∅" | (.pl, .gen) => "-on" | (.pl, _) => "-is",
  fun | (.sg, .gen) => "-u" | (.sg, _) => "-o" | (.pl, .gen) => "-on" | (.pl, _) => "-a",
  fun | (.sg, .gen) => "-u" | (.sg, _) => "-∅" | (.pl, .gen) => "-on" | (.pl, _) => "-a",
  fun | (.sg, .gen) => "-us" | (.sg, _) => "-os" | (.pl, .gen) => "-on" | (.pl, _) => "-i",
  fun | (.sg, .gen) => "-os" | (.sg, _) => "-∅" | (.pl, .gen) => "-on" | (.pl, _) => "-a"]

end Greek.StandardModern.Declension
