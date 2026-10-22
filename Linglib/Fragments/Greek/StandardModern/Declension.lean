module

public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Modern Greek nominal declensions

The eight nominal inflection classes of Modern Greek by their case–number endings, after
Ralli's description as simplified in [ackerman-malouf-2013] (stem alternations and stress set
aside), as a paradigm system whose classes are the paper's rows 1–8.

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

/-- The cells are nominative, genitive, accusative, and vocative, singular then plural. -/
abbrev nomSg : Fin 8 := 0
abbrev genSg : Fin 8 := 1
abbrev accSg : Fin 8 := 2
abbrev vocSg : Fin 8 := 3
abbrev nomPl : Fin 8 := 4
abbrev genPl : Fin 8 := 5
abbrev accPl : Fin 8 := 6
abbrev vocPl : Fin 8 := 7

/-- The eight declensions, rows 1–8 of the paper's Table 1. -/
def nominal : ParadigmSystem (Fin 8) (Fin 8) Ending :=
  ![![.os, .u, .on, .e, .i, .on, .us, .i],
    ![.s, .zero, .zero, .zero, .es, .on, .es, .es],
    ![.zero, .s, .zero, .zero, .es, .on, .es, .es],
    ![.zero, .s, .zero, .zero, .is, .on, .is, .is],
    ![.o, .u, .o, .o, .a, .on, .a, .a],
    ![.zero, .u, .zero, .zero, .a, .on, .a, .a],
    ![.os, .us, .os, .os, .i, .on, .i, .i],
    ![.zero, .os, .zero, .zero, .a, .on, .a, .a]]

end Greek.StandardModern.Declension
