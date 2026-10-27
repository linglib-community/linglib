module

public import Linglib.Syntax.Minimalist.Category.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.RelClasses

/-!
# Extended projections

Grimshaw takes a clause or a noun phrase to be one extended projection: a lexical head together
with the functional heads above it, all sharing the categorial features of the lexical head, at
functional levels, the F-values, that do not decrease going up. Each category here belongs to one
of four families, verbal, nominal, adjectival and adpositional, each with its lexical head, and has
an F-value, a natural number that is `0` exactly at the lexical head of its family. The families
carry the categorial features `[±V, ±N]`, and the two binary features have four combinations, one
for each family, so two categories share their features exactly when they share their family. A
category extends to another when the two are of one family and the second is at least as high.
Every category extends the lexical head of its family and any two categories of one family are
comparable, so an extended projection is a chain rising from its lexical head.

## Main definitions

* `Minimalist.CatFamily`, `Minimalist.Cat.family`: the four families of extended projections.
* `Minimalist.CatFamily.lexical`: the lexical head of a family.
* `Minimalist.CatFeatures`, `Minimalist.Cat.features`: the features `[±V, ±N]`, read off the
  family.
* `Minimalist.Cat.fValue`: the functional level of a category.
* `Minimalist.Cat.ExtendsTo`: the step relation of an extended projection, a preorder.

## Main results

* `Minimalist.CatFamily.features_bijective`: the features cross-classify the families.
* `Minimalist.Cat.fValue_eq_zero_iff`: the categories at level `0` are the lexical heads.
* `Minimalist.Cat.lexical_extendsTo`: every category extends the lexical head of its family.
* `Minimalist.Cat.extendsTo_total`: the categories of one family form a chain.

## Implementation notes

An F-value ranks the heads of one family, as Grimshaw's F-values order the heads that share
categorial features [panagiotidis-2015]; heads of different families are never compared, and each
family counts up from its lexical head at `0`. In the verbal family the left periphery is Rizzi's
Fin < Foc < Top < Force, with one topic position, the one above the focus, of the two in which
his topics recur. The Say layer of embedded speech reports sits between Foc and C as in Egressy,
and Speas and Tenny's speech-act head closes the sequence. Tense, negation, mood, modality,
polarity, outer aspect and evidentiality share the inflectional level, inner aspect shares the
level of v, and `Cartography.Head` orders the clausal heads these levels collapse. In the nominal
family Borer's dividing head `Q` lies below the counting head `Num`. Prepositions form their own
family, with den Dikken's Place and Path above them, whereas Grimshaw places P in the nominal
extended projection.

Chomsky's features first classified the noun, the verb and the adjective; the fourth combination,
`[−V, −N]`, was given to the adposition afterwards [baker-2003].

## References

* [grimshaw-2005]
* [chomsky-1970]
* [baker-2003]
* [panagiotidis-2015]
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

/-- The lexical head of a family, at the foot of its extended projections. -/
def CatFamily.lexical : CatFamily → Cat
  | .verbal => .V
  | .nominal => .N
  | .adjectival => .A
  | .adpositional => .P

/-- The family of a category, the extended projection it belongs to. -/
def Cat.family : Cat → CatFamily
  | .V | .v | .Voice | .Appl | .T | .Foc | .Top | .Fin | .C | .SA | .Say
  | .Force | .Neg | .Mod | .Mood | .Pol | .Asp | .InnerAsp | .Evid | .Nmlz => .verbal
  | .N | .n | .Num | .Dem | .Q | .D | .K => .nominal
  | .A | .a => .adjectival
  | .P | .Place | .Path => .adpositional

@[simp] theorem CatFamily.family_lexical (f : CatFamily) : f.lexical.family = f := by
  cases f <;> rfl

/-- The categorial features `[±V, ±N]`, which cross-classify the four lexical categories: V is
`[+V, −N]`, N is `[−V, +N]`, A is `[+V, +N]` and P is `[−V, −N]`. -/
structure CatFeatures where
  plusV : Bool
  plusN : Bool
  deriving DecidableEq, Repr

/-- The features of a family are those of its lexical head. -/
def CatFamily.features : CatFamily → CatFeatures
  | .verbal => ⟨true, false⟩
  | .nominal => ⟨false, true⟩
  | .adjectival => ⟨true, true⟩
  | .adpositional => ⟨false, false⟩

/-- Each of the four combinations of the two features is the features of exactly one family. -/
theorem CatFamily.features_bijective : Function.Bijective CatFamily.features :=
  ⟨fun a b h ↦ by cases a <;> cases b <;> simp_all [features], fun
    | ⟨true, false⟩ => ⟨.verbal, rfl⟩
    | ⟨false, true⟩ => ⟨.nominal, rfl⟩
    | ⟨true, true⟩ => ⟨.adjectival, rfl⟩
    | ⟨false, false⟩ => ⟨.adpositional, rfl⟩⟩

/-- The features of a category are those of its family, so that every functional head inherits
the features of its lexical head. -/
def Cat.features (c : Cat) : CatFeatures := c.family.features

theorem Cat.features_eq_iff {c d : Cat} : c.features = d.features ↔ c.family = d.family :=
  CatFamily.features_bijective.injective.eq_iff

/-- The F-value of a category is its level in its extended projection: lexical heads are at `0`,
categorizers at `1`, the inflectional domain at `2` and the left periphery from `3` up.

| level | verbal                            | nominal | adjectival | adpositional |
|-------|-----------------------------------|---------|------------|--------------|
| 0     | V                                 | N       | A          | P            |
| 1     | v, Voice, Appl, InnerAsp          | n       | a          | Place        |
| 2     | T, Neg, Mod, Mood, Pol, Asp, Evid | Q       |            | Path         |
| 3     | Fin, Nmlz                         | Num     |            |              |
| 4     | Foc                               | D, Dem  |            |              |
| 5     | Top, Say                          | K       |            |              |
| 6     | C, Force                          |         |            |              |
| 7     | SA                                |         |            |              | -/
def Cat.fValue : Cat → ℕ
  | .V | .N | .A | .P => 0
  | .v | .n | .a | .Voice | .Appl | .InnerAsp | .Place => 1
  | .T | .Q | .Neg | .Mod | .Mood | .Pol | .Asp | .Evid | .Path => 2
  | .Fin | .Num | .Nmlz => 3
  | .Foc | .D | .Dem => 4
  | .Top | .K | .Say => 5
  | .C | .Force => 6
  | .SA => 7

@[simp] theorem CatFamily.fValue_lexical (f : CatFamily) : f.lexical.fValue = 0 := by
  cases f <;> rfl

/-- The categories at level `0` are exactly the lexical heads. -/
theorem Cat.fValue_eq_zero_iff {c : Cat} : c.fValue = 0 ↔ c = c.family.lexical := by
  cases c <;> decide

/-- `c.ExtendsTo d` holds when `d` extends the projection of `c`, the two categories being of one
family and `d` at least as high, so that the extended projections are the chains of this
relation. -/
def Cat.ExtendsTo (c d : Cat) : Prop := c.family = d.family ∧ c.fValue ≤ d.fValue

instance : DecidableRel Cat.ExtendsTo := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : IsPreorder Cat Cat.ExtendsTo where
  refl _ := ⟨rfl, le_rfl⟩
  trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Every category extends the lexical head of its family. -/
theorem Cat.lexical_extendsTo (c : Cat) : c.family.lexical.ExtendsTo c :=
  ⟨CatFamily.family_lexical _, by simp⟩

/-- Any two categories of one family are comparable. -/
theorem Cat.extendsTo_total {c d : Cat} (h : c.family = d.family) :
    c.ExtendsTo d ∨ d.ExtendsTo c :=
  (le_total c.fValue d.fValue).imp (⟨h, ·⟩) (⟨h.symm, ·⟩)

end Minimalist
