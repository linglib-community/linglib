module

public import Mathlib.Tactic.DeriveFintype

/-!
# Bantu noun classes

This file defines the types shared by the Bantu noun-class fragments: the noun classes in the
comparative numbering, the semantic cores a gender may bear, [human], [animal] and [inanimate],
or the [non-human] of a two-way system, and the status of a gender as interpretable, bearing a
core, or uninterpretable, purely formal ([carstens-2026]). Each language's fragment says which
classes it has and what marks them, and pairs its singular and plural classes into genders
([carstens-1991]).

## References

* [carstens-1991]
* [carstens-2026]
-/

@[expose] public section

namespace Bantu

/-- A noun class, one of classes 1 to 18 of the comparative Bantu numbering. -/
inductive NounClass where
  | cl1 | cl2 | cl3 | cl4 | cl5 | cl6 | cl7 | cl8 | cl9 | cl10 | cl11 | cl12 | cl13 | cl14
  | cl15 | cl16 | cl17 | cl18
  deriving DecidableEq, Repr, Fintype

/-- The class a numeral names. -/
def NounClass.ofNumeral? (s : String) : Option NounClass :=
  [("1", cl1), ("2", cl2), ("3", cl3), ("4", cl4), ("5", cl5), ("6", cl6), ("7", cl7), ("8", cl8),
    ("9", cl9), ("10", cl10), ("11", cl11), ("12", cl12), ("13", cl13), ("14", cl14),
    ("15", cl15), ("16", cl16), ("17", cl17), ("18", cl18)].lookup s

/-- A semantic core is the salient class of entities a gender is associated with. Xhosa has
[human], [animal] and [inanimate], Shona [human] and [non-human]. -/
inductive SemanticCore where
  | human
  | animal
  | inanimate
  | nonhuman
  deriving DecidableEq, Repr

/-- A gender is interpretable, bearing a semantic core, or uninterpretable, with no association
to a class of entities. -/
inductive GenderStatus where
  | interpretable : SemanticCore → GenderStatus
  | uninterpretable : GenderStatus
  deriving DecidableEq, Repr

end Bantu
