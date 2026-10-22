module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets

/-!
# Burmeso object agreement

The two classes of Burmeso object agreement prefixes over six noun classes in two numbers,
after Donohue's description as Ackerman and Malouf tabulate it, as a paradigm system whose cells
pair a noun class with a number.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Burmeso.ObjectAgreement

open Morphology

/-- The agreement prefixes. -/
inductive AgreementPrefix
  | j
  | s
  | g
  | b
  | t
  | n
  deriving DecidableEq, Repr

/-- The six noun classes, I to VI. -/
inductive Gender where
  | gI
  | gII
  | gIII
  | gIV
  | gV
  | gVI
  deriving DecidableEq, Repr, Fintype

/-- Burmeso distinguishes the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- A cell pairs a noun class with a number. -/
abbrev Cell : Type := Gender × numberSystem.values

/-- `byGender gI gII gIII gIV gV gVI` gives each noun class its singular and plural prefixes, in
the column order of the paper's Table A3. -/
def byGender (gI gII gIII gIV gV gVI : AgreementPrefix × AgreementPrefix) :
    Gender → AgreementPrefix × AgreementPrefix
  | .gI => gI
  | .gII => gII
  | .gIII => gIII
  | .gIV => gIV
  | .gV => gV
  | .gVI => gVI

/-- The singular and plural prefixes of the two classes, rows A and B of Table A3. -/
def prefixes : Fin 2 → Gender → AgreementPrefix × AgreementPrefix :=
  ![byGender (.j, .s) (.g, .s) (.g, .j) (.j, .j) (.j, .g) (.g, .g),
    byGender (.b, .t) (.n, .t) (.n, .b) (.b, .b) (.b, .n) (.n, .n)]

/-- The two classes as a paradigm system over the noun class–number cells. -/
def objectAgreement : ParadigmSystem (Fin 2) Cell AgreementPrefix := fun d σ ↦
  (numberSystem.elim (prefixes d σ.1).1 (prefixes d σ.1).2) σ.2

end Burmeso.ObjectAgreement
