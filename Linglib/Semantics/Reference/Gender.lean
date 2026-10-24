module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.Features

/-!
# Referent gender

The gender a word restricts its referents to, which a language's semantic rules of gender
assignment read: for people the gender they are taken to have, for the animals a language
differentiates their sex. A noun or name restricts it where the language has a form for each, as
*mother* and *father* or *lioness* and *lion*. The two values are the restrictions words impose,
not a classification of referents: *teacher* imposes none, and a pronoun's presupposition lets a
referent be neither masculine nor feminine. A word token realizes a referent gender as a
Universal Dependencies gender tag (`ReferentGender.toUD`).

## References

* [corbett-1991] — the semantic rules over sex-differentiable nouns, §3.1.1, p. 34
* [konnelly-cowper-2020] — the gender nouns and names bear lexically
* [corbett-fedden-2016]
-/

@[expose] public section

/-- The gender a word restricts its referents to. -/
inductive ReferentGender where
  | male
  | female
  deriving DecidableEq, Repr, Fintype

/-- A referent gender realizes as the masculine or the feminine tag. -/
def ReferentGender.toUD : ReferentGender → UD.Gender
  | .male => .Masc
  | .female => .Fem
