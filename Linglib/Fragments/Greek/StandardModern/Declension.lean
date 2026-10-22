module

public import Linglib.Fragments.Greek.StandardModern.Case
public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets

/-!
# Modern Greek nominal declensions

The eight nominal inflection classes of Modern Greek by their case–number endings, after
Ralli's description as Ackerman and Malouf simplify it (stem alternations and stress set aside),
as a paradigm system whose classes are the paper's rows 1–8 and whose cells pair the four cases
with the two numbers.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Greek.StandardModern.Declension

open Morphology

/-- The nominal endings. -/
inductive Ending
  | os
  | u
  | on
  | e
  | i
  | us
  | s
  | zero
  | es
  | is
  | o
  | a
  deriving DecidableEq, Repr

/-- Modern Greek distinguishes the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- A cell pairs a case with a number. -/
abbrev Cell : Type := Case × numberSystem.values

/-- The nominative singular. -/
abbrev nomSg : Cell := (.nom, numberSystem.value .singular)
/-- The genitive singular. -/
abbrev genSg : Cell := (.gen, numberSystem.value .singular)
/-- The accusative singular. -/
abbrev accSg : Cell := (.acc, numberSystem.value .singular)
/-- The vocative singular. -/
abbrev vocSg : Cell := (.voc, numberSystem.value .singular)
/-- The nominative plural. -/
abbrev nomPl : Cell := (.nom, numberSystem.value .plural)
/-- The genitive plural. -/
abbrev genPl : Cell := (.gen, numberSystem.value .plural)
/-- The accusative plural. -/
abbrev accPl : Cell := (.acc, numberSystem.value .plural)
/-- The vocative plural. -/
abbrev vocPl : Cell := (.voc, numberSystem.value .plural)

/-- `row nom gen acc voc` gives each case its ending, in the column order of the paper's
Table 1. -/
def row (nom gen acc voc : Ending) : Case → Ending
  | .nom => nom
  | .gen => gen
  | .acc => acc
  | .voc => voc

/-- The singular and plural endings of the eight declensions, rows 1–8 of the paper's Table 1. -/
def endings : Fin 8 → (Case → Ending) × (Case → Ending) :=
  ![(row .os .u .on .e, row .i .on .us .i),
    (row .s .zero .zero .zero, row .es .on .es .es),
    (row .zero .s .zero .zero, row .es .on .es .es),
    (row .zero .s .zero .zero, row .is .on .is .is),
    (row .o .u .o .o, row .a .on .a .a),
    (row .zero .u .zero .zero, row .a .on .a .a),
    (row .os .us .os .os, row .i .on .i .i),
    (row .zero .os .zero .zero, row .a .on .a .a)]

/-- The eight declensions as a paradigm system over the case–number cells. -/
def nominal : ParadigmSystem (Fin 8) Cell Ending := fun d σ ↦
  (numberSystem.elim (endings d).1 (endings d).2) σ.2 σ.1

end Greek.StandardModern.Declension
