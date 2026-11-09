module

public import Mathlib.Data.Fintype.Basic
public import Linglib.Syntax.Number.Basic

/-!
# Inverse number

Kiowa-Tanoan verbal agreement distinguishes singular, dual, plural and *inverse*, a marker so
called "because it appears to change the basic number meaning of the stem to which it is
attached" ([corbett-2000] §5.5, p. 159). Inverse is not a number value alongside the others:
inverse systems "are a matter of morphological arrangement and not of semantic values"
(p. 161), so `Category` lists agreement categories rather than values of `Number`. What the
inverse marks is a question for the analyses: Harbour's, in which a D head's number features
receive conflicting values from the noun's class and its natural number, is in
`Studies/Middleton2026.lean`.

## References

* [corbett-2000]
* [harbour-2011]
-/

@[expose] public section

namespace Number.Inverse

/-- The four categories of Kiowa-Tanoan verbal agreement. -/
inductive Category where
  | singular
  | dual
  | plural
  | inverse
  deriving DecidableEq, Repr, Fintype

end Number.Inverse
