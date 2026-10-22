module

public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Chiquihuitlán Mazatec verb inflection

Two of the three cross-cutting inflection-class systems of Chiquihuitlán Mazatec verbs over the
cells 1sg, 2sg, 3, 1incl, 1pl, 2pl, after Jamieson's description as tabulated in
[ackerman-malouf-2013]: the ten final-vowel classes and the six neutral-aspect tone patterns.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Mazatec.Verbs

open Morphology

/-- The cells. -/
abbrev firstSg : Fin 6 := 0
abbrev secondSg : Fin 6 := 1
abbrev third : Fin 6 := 2
abbrev firstIncl : Fin 6 := 3
abbrev firstPl : Fin 6 := 4
abbrev secondPl : Fin 6 := 5

/-- Final vowels, nasal ones suffixed `N`. -/
inductive Vowel
  | ae
  | i
  | e
  | u
  | o
  | a
  | eN
  | iN
  | uN
  | oN
  | aN
  deriving DecidableEq, Repr

/-- The ten final-vowel classes. -/
def finalVowels : ParadigmSystem (Fin 10) (Fin 6) Vowel :=
  ![![.ae, .i, .i, .eN, .iN, .uN],
    ![.ae, .e, .e, .eN, .iN, .uN],
    ![.ae, .e, .ae, .eN, .iN, .uN],
    ![.u, .i, .u, .uN, .iN, .uN],
    ![.o, .e, .o, .oN, .iN, .uN],
    ![.a, .e, .a, .aN, .iN, .uN],
    ![.eN, .iN, .iN, .eN, .iN, .uN],
    ![.eN, .iN, .eN, .eN, .iN, .uN],
    ![.uN, .iN, .uN, .uN, .iN, .uN],
    ![.aN, .iN, .eN, .aN, .iN, .uN]]

/-- Tone patterns, named by their tone numbers. -/
inductive Tone
  | t3_1
  | t3_31
  | t3_14
  | t1_1
  | t2_2
  | t2_24
  | t3_2
  | t1_43
  | t3_24
  | t14_42
  | t14_34
  | t14_3
  deriving DecidableEq, Repr

/-- The six neutral-aspect tone patterns. -/
def tones : ParadigmSystem (Fin 6) (Fin 6) Tone :=
  ![![.t3_1, .t3_1, .t3_1, .t3_31, .t3_14, .t3_1],
    ![.t1_1, .t2_2, .t2_2, .t2_2, .t2_24, .t2_2],
    ![.t3_1, .t2_2, .t3_2, .t2_2, .t2_24, .t2_2],
    ![.t1_43, .t1_43, .t3_24, .t14_42, .t14_34, .t14_3],
    ![.t1_1, .t3_2, .t3_2, .t3_2, .t3_24, .t3_2],
    ![.t3_1, .t3_2, .t3_2, .t3_2, .t3_24, .t3_2]]

end Mazatec.Verbs
