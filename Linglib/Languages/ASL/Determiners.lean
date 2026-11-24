module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# ASL quantifier signs

This file records the quantificational signs of American Sign Language attested with locus and
height modification in [davidson-gagne-2022], under their ASL Signbank ID glosses, as the
carrier `Sign`. A sign projects to a `QuantificationalDeterminer` record and denotes the
readings the literature makes available for its gloss: `FS(ALL)` is the fingerspelled universal, `ALL-b` its
two-handed form, `NONEsym` the symmetrical negative quantifier, and the numerals `ONE` and `TWO`
carry both the at-least and the exactly reading. Which signs carry a height-marked locus
themselves and which take a following `IX-arc` is a matter of their phonological form and is
classified in the study, not here.

## References

* [K. Davidson and D. Gagne, *"More is up" for domain restriction in ASL*
  (2022)][davidson-gagne-2022]
-/

@[expose] public section

namespace ASL.Determiners

/-- The quantifier signs attested in the paper. -/
inductive Sign where
  | fsAll | allB | noneSym | someone | something | one | two | many | few | each | most
  deriving DecidableEq, Repr, Fintype

namespace Sign

/-- The ASL Signbank ID gloss. -/
def form : Sign → String
  | .fsAll => "FS(ALL)"
  | .allB => "ALL-b"
  | .noneSym => "NONEsym"
  | .someone => "SOMEONE"
  | .something => "SOMETHING"
  | .one => "ONE"
  | .two => "TWO"
  | .many => "MANY"
  | .few => "FEW"
  | .each => "EACH"
  | .most => "MOST"

/-- The grammatical number a sign selects. -/
def numberRestriction : Sign → Option Number
  | .fsAll | .allB | .two | .many | .few | .most => some .plural
  | .someone | .something | .one | .each => some .singular
  | .noneSym => none

/-- The sign as a determiner record. -/
def toQuantifier (s : Sign) : QuantificationalDeterminer :=
  { form := s.form, numberRestriction := s.numberRestriction }

/-- All the signs. -/
def toList : List Sign :=
  [.fsAll, .allB, .noneSym, .someone, .something, .one, .two, .many, .few, .each, .most]

universe u

/-- The readings available for a sign, those of its gloss: the universals and `EACH` read as
`every`, `NONEsym` as `no`, the existentials as `Quantifier.Det.some`, `MOST` as `most`, and the
numerals as `atLeast` or `exactly`; `MANY` and `FEW` have no reading, their standards being
contextual. -/
noncomputable instance : Denotes Sign (Set Quantifier.Det.Family.{u}) where
  denote
    | .fsAll | .allB | .each => {Quantifier.Det.Family.every}
    | .noneSym => {Quantifier.Det.Family.no}
    | .someone | .something => {Quantifier.Det.Family.some}
    | .one => {Quantifier.Det.Family.atLeast 1, Quantifier.Det.Family.exactly 1}
    | .two => {Quantifier.Det.Family.atLeast 2, Quantifier.Det.Family.exactly 2}
    | .most => {Quantifier.Det.Family.most}
    | .many | .few => ∅

end Sign

end ASL.Determiners
