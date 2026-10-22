module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Burmeso object agreement

The two classes of Burmeso object agreement prefixes over six noun classes in two numbers,
after Donohue's description as Ackerman and Malouf tabulate it, as a paradigm system whose cells
are the paper's noun class and number columns.

## References

* [ackerman-malouf-2013]
-/

@[expose] public section

namespace Burmeso.ObjectAgreement

open Morphology

/-- The six noun classes, I to VI. -/
inductive Gender where
  | gI
  | gII
  | gIII
  | gIV
  | gV
  | gVI
  deriving DecidableEq, Fintype, Repr

/-- The cells of the paper's Table A3: a noun class and a number each. -/
inductive Row where
  | sgI | plI | sgII | plII | sgIII | plIII | sgIV | plIV | sgV | plV | sgVI | plVI
  deriving DecidableEq, Fintype, Repr

/-- The noun class of a row. -/
def Row.gender : Row → Gender
  | .sgI | .plI => .gI
  | .sgII | .plII => .gII
  | .sgIII | .plIII => .gIII
  | .sgIV | .plIV => .gIV
  | .sgV | .plV => .gV
  | .sgVI | .plVI => .gVI

/-- The number of a row. -/
def Row.number : Row → Number
  | .sgI | .sgII | .sgIII | .sgIV | .sgV | .sgVI => .singular
  | .plI | .plII | .plIII | .plIV | .plV | .plVI => .plural

/-- The prefixes of the two classes, rows A and B of the paper's Table A3. -/
def objectAgreement : ParadigmSystem (Fin 2) Row String := ![
  fun | .sgI | .plIII | .sgIV | .plIV | .sgV => "j-" | .plI | .plII => "s-"
      | .sgII | .sgIII | .plV | .sgVI | .plVI => "g-",
  fun | .sgI | .plIII | .sgIV | .plIV | .sgV => "b-" | .plI | .plII => "t-"
      | .sgII | .sgIII | .plV | .sgVI | .plVI => "n-"]

end Burmeso.ObjectAgreement
