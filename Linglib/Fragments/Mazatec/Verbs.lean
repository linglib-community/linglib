module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Chiquihuitlán Mazatec verb inflection

Two of the three cross-cutting inflection-class systems of Chiquihuitlán Mazatec verbs over the
cells 1sg, 2sg, 3, 1incl, 1pl, 2pl, after Jamieson's description as Ackerman and Malouf tabulate
it: the ten final-vowel classes and the six neutral-aspect tone patterns.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Mazatec.Verbs

open Morphology

/-- The cells of the paper's Tables 6 and 7: 1sg, 2sg, 3, 1incl, 1pl and 2pl. -/
inductive Row where
  | sg1 | sg2 | third | incl | pl1 | pl2
  deriving DecidableEq, Fintype, Repr

/-- The person of a row. The first plural is exclusive, the inclusive being a row of its own. -/
def Row.person : Row → Person
  | .sg1 => .first
  | .sg2 | .pl2 => .second
  | .third => .third
  | .incl => .firstInclusive
  | .pl1 => .firstExclusive

/-- The number of a row, none where the paper's label gives none. -/
def Row.number : Row → Option Number
  | .sg1 | .sg2 => some .singular
  | .pl1 | .pl2 => some .plural
  | .third | .incl => none

/-- The ten final-vowel classes, the paper's Table 6. -/
def finalVowels : ParadigmSystem (Fin 10) Row String := ![
  fun | .sg1 => "-æ" | .sg2 | .third => "-i" | .incl => "-ẽ" | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 => "-æ" | .sg2 | .third => "-e" | .incl => "-ẽ" | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .third => "-æ" | .sg2 => "-e" | .incl => "-ẽ" | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .third => "-u" | .sg2 => "-i" | .incl | .pl2 => "-ũ" | .pl1 => "-ĩ",
  fun | .sg1 | .third => "-o" | .sg2 => "-e" | .incl => "-õ" | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .third => "-a" | .sg2 => "-e" | .incl => "-ã" | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .incl => "-ẽ" | .sg2 | .third | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .third | .incl => "-ẽ" | .sg2 | .pl1 => "-ĩ" | .pl2 => "-ũ",
  fun | .sg1 | .third | .incl | .pl2 => "-ũ" | .sg2 | .pl1 => "-ĩ",
  fun | .sg1 | .incl => "-ã" | .sg2 | .pl1 => "-ĩ" | .third => "-ẽ" | .pl2 => "-ũ"]

/-- The six neutral-aspect tone patterns, the paper's Table 7. -/
def tones : ParadigmSystem (Fin 6) Row String := ![
  fun | .sg1 | .sg2 | .third | .pl2 => "3-1" | .incl => "3-31" | .pl1 => "3-14",
  fun | .sg1 => "1-1" | .sg2 | .third | .incl | .pl2 => "2-2" | .pl1 => "2-24",
  fun | .sg1 => "3-1" | .sg2 | .incl | .pl2 => "2-2" | .third => "3-2" | .pl1 => "2-24",
  fun | .sg1 | .sg2 => "1-43" | .third => "3-24" | .incl => "14-42" | .pl1 => "14-34"
      | .pl2 => "14-3",
  fun | .sg1 => "1-1" | .sg2 | .third | .incl | .pl2 => "3-2" | .pl1 => "3-24",
  fun | .sg1 => "3-1" | .sg2 | .third | .incl | .pl2 => "3-2" | .pl1 => "3-24"]

end Mazatec.Verbs
