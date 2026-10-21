module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Logophoric pronouns

A logophoric pronoun is a personal pronoun reserved for the one whose speech, thoughts or feelings
a report conveys, a form distinct from the ordinary third person: Ewe *yè*, Wan *mɔ̄*. Which
reports license one varies by language and is not recorded on the entry. A long-distance reflexive
is sensitive to the same factors, but it is a reflexive and a `ReflexivePronoun`.

## Main definitions

* `LogophoricPronoun`: a personal pronoun of the logophoric kind.

## References

* [sells-1987]
-/

@[expose] public section

/-- A logophoric pronoun is a `PersonalPronoun` of the logophoric kind. -/
@[ext]
structure LogophoricPronoun extends PersonalPronoun

instance : DecidableEq LogophoricPronoun :=
  fun _ _ ↦ decidable_of_iff _ LogophoricPronoun.ext_iff.symm
