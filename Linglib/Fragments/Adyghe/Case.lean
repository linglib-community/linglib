module

public import Linglib.Syntax.Case.Basic
public import Linglib.Morphology.Morph

/-!
# Adyghe case

This file defines the cases of Adyghe. Caponigro and Polinsky distinguish three, the absolutive
in *-r* and the ergative and the oblique, which share the suffix *-m*. A noun without a case suffix
is read as non-specific. The oblique marks every indirect argument, each licensed by an
applicative head on the verb. Caponigro and Polinsky note an analysis with two cases, absolutive
and oblique, built on the identity of the ergative and oblique exponents.

## Main definitions

* `Adyghe.Case`, `Adyghe.Case.label`: the three cases, and the comparative value each is named
  for.
* `Adyghe.Case.exponents`: the case suffixes of a noun.

## References

* [caponigro-polinsky-2011]
-/

@[expose] public section

namespace Adyghe

open Morphology (Morph)

/-- The three cases. -/
inductive Case where
  /-- The absolutive. -/
  | abs
  /-- The ergative. -/
  | erg
  /-- The oblique, of the indirect arguments. -/
  | obl
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | abs => .abs
  | erg => .erg
  | obl => .obl

/-- The case suffixes of a noun, the ergative and the oblique syncretic in *-m*. -/
def exponents : Case → List Morph
  | abs => [.suff "r"]
  | erg | obl => [.suff "m"]

end Case

end Adyghe
