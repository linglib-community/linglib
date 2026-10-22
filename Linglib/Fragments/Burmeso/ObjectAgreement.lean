module

public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Burmeso object agreement

The two classes of Burmeso object agreement prefixes over six noun classes in two numbers,
after Donohue's description as tabulated in [ackerman-malouf-2013].

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

/-- The two classes over the cells I.sg, I.pl, …, VI.sg, VI.pl. -/
def objectAgreement : ParadigmSystem (Fin 2) (Fin 12) AgreementPrefix :=
  ![![.j, .s, .g, .s, .g, .j, .j, .j, .j, .g, .g, .g],
    ![.b, .t, .n, .t, .n, .b, .b, .b, .b, .n, .n, .n]]

end Burmeso.ObjectAgreement
