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
as a paradigm system whose classes are the rows 1–8 of their Table 1 and whose cells pair a number
with one of the four cases.

Only the first declension, of nouns in *-os* such as *anθropos* 'man', gives each case its own
ending, and only in the singular: every plural has the vocative of its nominative. The paradigms
therefore separate the four cases of `Greek.StandardModern.Case`.

## Main statements

* `injective_iff`: a declension gives each case of a number its own ending exactly when it is the
  first declension and the number is the singular (Ralli p. 205).
* `nominal_vocPl`, `injOn_pl`: every plural has the vocative of its nominative, and the first
  declension distinguishes the other three cases in the plural (Ralli p. 205).
* `separatesPoints_paradigms`: the paradigms separate the four cases.

## Implementation notes

Ralli's table gives the accusative singular of the first declension as *anθropo(n)*, with an
optional *-n*, and the genitive singular of the fourth as *polis* beside the literary *poleos*;
the endings are Ackerman and Malouf's *-on* and *-s*.

## References

* [ackerman-malouf-2013]
* [ralli-2000]
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

/-- The endings of the eight declensions, rows 1–8 of Table 1 of [ackerman-malouf-2013], *-∅* the
zero ending. -/
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

/-! ### The cases the paradigms distinguish -/

theorem injective_iff {d : Fin 8} {r : Row} :
    Function.Injective (Function.curry (nominal d) r) ↔ d = 0 ∧ r = .sg := by
  revert d r
  decide

theorem nominal_vocPl (d : Fin 8) : nominal d vocPl = nominal d nomPl := by
  revert d
  decide

theorem injOn_pl : Set.InjOn (Function.curry (nominal 0) .pl) {.voc}ᶜ :=
  Set.injOn_iff_injective.2 (by decide)

/-- The paradigms separate the four cases. -/
theorem separatesPoints_paradigms :
    {p | ∃ d r, p = Function.curry (nominal d) r}.SeparatesPoints := fun _ _ h ↦
  ⟨_, ⟨0, .sg, rfl⟩, (injective_iff.2 ⟨rfl, rfl⟩).ne h⟩

end Greek.StandardModern.Declension
