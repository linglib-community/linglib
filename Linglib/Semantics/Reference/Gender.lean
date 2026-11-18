module

public import Mathlib.Data.Set.Disjoint
public import Mathlib.Logic.Pairwise
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.UD.Features

/-!
# Referent gender

The gender a word restricts its referents to, which a language's semantic rules of gender
assignment read: for people the gender they are taken to have, for the animals a language
differentiates their sex. A noun or name restricts it where the language has a form for each, as
*mother* and *father* or *lioness* and *lion*; *teacher* imposes no restriction. A word token
realizes a referent gender as a Universal Dependencies gender tag.

What the restriction requires of a referent is a fact about the entity domain: a gendered domain
supplies the referents gendered masculine and those gendered feminine, and a referent gender
denotes [one of the two sets](##ReferentGender.referents). The sets are
[disjoint](##ReferentGender.pairwise_disjoint_referents) and need not cover the domain, so the two
values are the restrictions words impose rather than a classification of referents: a referent
may be gendered neither way.

## References

* [corbett-1991] — the semantic rules over sex-differentiable nouns
* [konnelly-cowper-2020] — the gender nouns and names bear lexically
* [corbett-fedden-2016]
-/

@[expose] public section

/-- The gender a word restricts its referents to. -/
inductive ReferentGender where
  | male
  | female
  deriving DecidableEq, Repr, Fintype

/-- A gendered entity domain has disjoint sets of referents gendered masculine and gendered
feminine, as socially constituted. Grammatical gender presupposes it, and a referent may be
gendered neither way. -/
class Gendered (E : Type*) where
  /-- The referents gendered masculine. -/
  masculine : Set E
  /-- The referents gendered feminine. -/
  feminine : Set E
  /-- No referent is gendered both ways. -/
  disjoint : Disjoint masculine feminine

namespace ReferentGender

/-- A referent gender realizes as the masculine or the feminine tag. -/
def toUD : ReferentGender → UD.Gender
  | .male => .Masc
  | .female => .Fem

variable {E : Type*} [Gendered E]

/-- The referents a word of a referent gender is restricted to, those the entity domain genders
that way. -/
def referents : ReferentGender → Set E
  | .male => Gendered.masculine
  | .female => Gendered.feminine

@[simp] theorem referents_male : referents (E := E) .male = Gendered.masculine := rfl

@[simp] theorem referents_female : referents (E := E) .female = Gendered.feminine := rfl

open scoped Function in
/-- No referent satisfies the restrictions of two referent genders. -/
theorem pairwise_disjoint_referents : Pairwise (Disjoint on referents (E := E))
  | .male, .female, _ => Gendered.disjoint
  | .female, .male, _ => Gendered.disjoint.symm
  | .male, .male, h | .female, .female, h => absurd rfl h

end ReferentGender
