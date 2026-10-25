module

public import Linglib.Syntax.Minimalist.Category.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses

/-!
# The functional sequence

This file defines the height of a category in the functional sequence and the families of
extended projections. Grimshaw takes a clause or a noun phrase to be one extended projection, a
lexical head together with the functional heads above it, all of one category family and with a
functional level, the F-value, that does not decrease going up. The F-value of each category is
a natural number, with the lexical heads at `0`, and the four families, verbal, nominal,
adjectival and adpositional, carry Chomsky's `[±V, ±N]` features, so that two categories share
those features exactly when they are of one family. A category extends to another when the two
are of one family and the second is at least as high; the extended projections are the chains
of this relation.

## Main definitions

* `Minimalist.Cat.fValue`: the functional level of a category.
* `Minimalist.CatFamily`, `Minimalist.Cat.family`: the four families of extended projections.
* `Minimalist.CatFeatures`, `Minimalist.Cat.features`: Chomsky's `[±V, ±N]` features, read off
  the family.
* `Minimalist.Cat.ExtendsTo`: the step relation of an extended projection, a preorder.

## Main results

* `Minimalist.Cat.features_eq_iff`: two categories share their features iff they share their
  family.

## Implementation notes

The F-values place the families on one scale, `n` with `v`, `Q` with `T`, `Num` with `Fin` and
`D` with `Foc`. Rizzi's order Fin < Foc < Top < Force fixes the verbal left periphery, Borer's
individuation before counting puts `Q` below `Num`, the Say layer of embedded speech reports
sits between Foc and C as in Egressy, and Speas and Tenny's speech-act head closes the verbal
sequence. Tense, negation, modality, polarity, aspect and evidentiality share the inflectional
level; `Cartography.Head` orders the clausal heads that level collapses, some aspect heads among
them below Voice. Prepositions form their own family, with den Dikken's Place and Path above them,
following Chomsky's `[−V, −N]`, whereas Grimshaw places P in the nominal extended projection.

## References

* [grimshaw-2005]
* [chomsky-1970]
* [rizzi-1997]
* [cinque-1999]
* [borer-2005]
* [speas-tenny-2003]
* [egressy-2026]
* [dendikken-2010]
-/

@[expose] public section

namespace Minimalist

/-- The four families of extended projections, each anchored by a lexical category. -/
inductive CatFamily
  | verbal
  | nominal
  | adjectival
  | adpositional
  deriving DecidableEq, Repr

/-- The family of a category, the extended projection it belongs to. -/
def Cat.family : Cat → CatFamily
  | .V | .v | .Voice | .Appl | .T | .Foc | .Top | .Fin | .C | .SA | .Say
  | .Force | .Neg | .Mod | .Rel | .Pol | .Asp | .Evid | .Nmlz => .verbal
  | .N | .n | .Num | .Dem | .Q | .D | .K => .nominal
  | .A | .a => .adjectival
  | .P | .Place | .Path => .adpositional

/-- Chomsky's categorial features `[±V, ±N]`, which cross-classify the four lexical categories:
V is `[+V, −N]`, N is `[−V, +N]`, A is `[+V, +N]` and P is `[−V, −N]`. -/
structure CatFeatures where
  plusV : Bool
  plusN : Bool
  deriving DecidableEq, Repr

/-- The features of a family are those of its lexical anchor. -/
def CatFamily.features : CatFamily → CatFeatures
  | .verbal => ⟨true, false⟩
  | .nominal => ⟨false, true⟩
  | .adjectival => ⟨true, true⟩
  | .adpositional => ⟨false, false⟩

theorem CatFamily.features_injective : Function.Injective CatFamily.features := by
  intro a b h
  cases a <;> cases b <;> simp_all [CatFamily.features]

/-- The features of a category are those of its family, so that every functional head inherits
the features of its lexical anchor. -/
def Cat.features (c : Cat) : CatFeatures := c.family.features

theorem Cat.features_eq_iff {c d : Cat} : c.features = d.features ↔ c.family = d.family :=
  CatFamily.features_injective.eq_iff

/-- The F-value of a category is its level in the functional sequence: lexical heads are at `0`,
categorizers at `1`, the inflectional domain at `2` and the left periphery from `3` up, with the
nominal and adpositional levels aligned to the verbal ones.

| level | verbal                     | nominal | adjectival | adpositional |
|-------|----------------------------|---------|------------|--------------|
| 0     | V                          | N       | A          | P            |
| 1     | v, Voice, Appl             | n       | a          | Place        |
| 2     | T, Neg, Mod, Pol, Asp, Evid | Q       |            | Path         |
| 3     | Fin, Nmlz                  | Num     |            |              |
| 4     | Foc                        | D, Dem  |            |              |
| 5     | Top, Rel, Say              | K       |            |              |
| 6     | C, Force                   |         |            |              |
| 7     | SA                         |         |            |              | -/
def Cat.fValue : Cat → ℕ
  | .V | .N | .A | .P => 0
  | .v | .n | .a | .Voice | .Appl | .Place => 1
  | .T | .Q | .Neg | .Mod | .Pol | .Asp | .Evid | .Path => 2
  | .Fin | .Num | .Nmlz => 3
  | .Foc | .D | .Dem => 4
  | .Top | .Rel | .K | .Say => 5
  | .C | .Force => 6
  | .SA => 7

/-- `c.ExtendsTo d` holds when `d` extends the projection of `c`, the two categories being of one
family and `d` at least as high, so that the extended projections are the chains of this
relation. -/
def Cat.ExtendsTo (c d : Cat) : Prop := c.family = d.family ∧ c.fValue ≤ d.fValue

instance : DecidableRel Cat.ExtendsTo := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : IsPreorder Cat Cat.ExtendsTo where
  refl _ := ⟨rfl, le_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end Minimalist
