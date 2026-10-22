module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets

/-!
# Chiquihuitlán Mazatec verb inflection

Two of the three cross-cutting inflection-class systems of Chiquihuitlán Mazatec verbs over the
cells 1sg, 2sg, 3, 1incl, 1pl, 2pl, after Jamieson's description as Ackerman and Malouf tabulate
it: the ten final-vowel classes and the six neutral-aspect tone patterns. A cell is a person with
a number where the paper's label gives one.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Mazatec.Verbs

open Morphology

/-- The cells 1sg, 2sg, 3, 1incl, 1pl and 2pl as person and number, the number given where the
paper's label gives one. The first plural is exclusive, the inclusive being a cell of its own. -/
def cells : Finset (Person × Option Number) :=
  {(.first, some .singular), (.second, some .singular), (.third, none), (.firstInclusive, none),
    (.firstExclusive, some .plural), (.second, some .plural)}

/-- A cell is one of the six. -/
abbrev Cell : Type := cells

/-- The first person singular. -/
abbrev firstSg : Cell := ⟨(.first, some .singular), by decide⟩
/-- The second person singular. -/
abbrev secondSg : Cell := ⟨(.second, some .singular), by decide⟩
/-- The third person. -/
abbrev third : Cell := ⟨(.third, none), by decide⟩
/-- The first person inclusive. -/
abbrev firstIncl : Cell := ⟨(.firstInclusive, none), by decide⟩
/-- The first person plural, exclusive. -/
abbrev firstPl : Cell := ⟨(.firstExclusive, some .plural), by decide⟩
/-- The second person plural. -/
abbrev secondPl : Cell := ⟨(.second, some .plural), by decide⟩

/-- `row sg1 sg2 third incl pl1 pl2` gives each cell its value, in the column order of the
paper's Tables 6 and 7. -/
def row {α : Type*} (sg1 sg2 third incl pl1 pl2 : α) (σ : Cell) : α :=
  match σ.1 with
  | (.first, some .singular) => sg1
  | (.second, some .singular) => sg2
  | (.third, none) => third
  | (.firstInclusive, none) => incl
  | (.firstExclusive, some .plural) => pl1
  | _ => pl2

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
def finalVowels : ParadigmSystem (Fin 10) Cell Vowel :=
  ![row .ae .i .i .eN .iN .uN,
    row .ae .e .e .eN .iN .uN,
    row .ae .e .ae .eN .iN .uN,
    row .u .i .u .uN .iN .uN,
    row .o .e .o .oN .iN .uN,
    row .a .e .a .aN .iN .uN,
    row .eN .iN .iN .eN .iN .uN,
    row .eN .iN .eN .eN .iN .uN,
    row .uN .iN .uN .uN .iN .uN,
    row .aN .iN .eN .aN .iN .uN]

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
def tones : ParadigmSystem (Fin 6) Cell Tone :=
  ![row .t3_1 .t3_1 .t3_1 .t3_31 .t3_14 .t3_1,
    row .t1_1 .t2_2 .t2_2 .t2_2 .t2_24 .t2_2,
    row .t3_1 .t2_2 .t3_2 .t2_2 .t2_24 .t2_2,
    row .t1_43 .t1_43 .t3_24 .t14_42 .t14_34 .t14_3,
    row .t1_1 .t3_2 .t3_2 .t3_2 .t3_24 .t3_2,
    row .t3_1 .t3_2 .t3_2 .t3_2 .t3_24 .t3_2]

end Mazatec.Verbs
