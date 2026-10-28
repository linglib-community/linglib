module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.PartialUnify
public import Linglib.Morphology.Word.Features

/-!
# Feature bundles

This file defines the dimensions in which agreement targets covary and the analytical
feature bundle over them, a value or nothing in each dimension.

An agreement bundle gives each dimension a slot of the flat order of `Core/Order/Flat.lean`, so
its partial order, its bottom, the wholly unspecified bundle, and its unification are the
pointwise ones. Each dimension is a token feature with that feature's values, and a token's
bundle is its features read along that inclusion, `Agreement.Bundle.ofFeatures`.

## Main definitions

* `Agreement.Dimension` — the five dimensions a target's form may covary in
* `Agreement.Dimension.toFeature`, `Agreement.Dimension.Value` — the token feature a dimension
  is, and its values
* `Agreement.Bundle` — a value or `⊥` in each dimension
* `Agreement.Bundle.set`, `Agreement.Bundle.personNumber` — a bundle with one dimension set,
  and the bundle valued in person and number alone
* `Agreement.Bundle.ofFeatures` — the restriction of a token's features
* `Agreement.Bundle.person`, `Agreement.Bundle.IsSAP`, `Agreement.Bundle.IsPlural` — the person a
  bundle bears, and the speech-act participant and plural bundles
* `Agreement.Bundle.personNumberCells` — the six bundles of three persons and two numbers

## References

* [corbett-1998] — the three indisputable agreement features and the two contested ones
* [norris-2019] — the dimensions of the concord survey
-/

@[expose] public section

namespace Agreement

/-- A dimension is a feature in which a target's form may covary with another element, one of the
three indisputable agreement features or the two contested ones ([corbett-1998]). -/
inductive Dimension where
  | person | number | gender | case | definiteness
  deriving DecidableEq, Repr, Fintype

/-- The token feature a dimension is. It is reducible, so that the values of a dimension reduce
to those of its feature when coercions are sought. -/
abbrev Dimension.toFeature : Dimension → Morphology.Feature
  | .person => .person
  | .number => .number
  | .gender => .gender
  | .case => .case
  | .definiteness => .definiteness

/-- The values of a dimension are those of the token feature it is. -/
abbrev Dimension.Value (d : Dimension) : Type := d.toFeature.Value

instance (d : Dimension) : DecidableEq d.Value := by cases d <;> exact inferInstance

/-- A feature bundle assigns each dimension a value or `⊥`. -/
abbrev Bundle := (d : Dimension) → Flat d.Value

namespace Bundle

/-- The bundle with the dimension `d` set to the value `v`. -/
def set (d : Dimension) (v : d.Value) (b : Bundle) : Bundle := Function.update b d (some v)

/-- The bundle valued in person and number alone. -/
def personNumber (p : Person) (n : Number) : Bundle :=
  set .number n (set .person p ⊥)

@[simp] theorem personNumber_person (p : Person) (n : Number) : personNumber p n .person = p :=
  rfl

@[simp] theorem personNumber_number (p : Person) (n : Number) : personNumber p n .number = n :=
  rfl

@[simp] theorem personNumber_gender (p : Person) (n : Number) : personNumber p n .gender = ⊥ :=
  rfl

@[simp] theorem personNumber_case (p : Person) (n : Number) : personNumber p n .case = ⊥ := rfl

@[simp] theorem personNumber_definiteness (p : Person) (n : Number) :
    personNumber p n .definiteness = ⊥ :=
  rfl

/-- The restriction of a token's features to the agreement dimensions reads them along
`Dimension.toFeature`. -/
def ofFeatures (f : Morphology.Features) : Bundle := fun d ↦ f d.toFeature

@[simp] theorem ofFeatures_apply (f : Morphology.Features) (d : Dimension) :
    ofFeatures f d = f d.toFeature :=
  rfl

instance : DecidableLE Bundle := fun x y ↦ inferInstanceAs (Decidable (∀ d, x d ≤ y d))

instance : DecidableLT Bundle := decidableLTOfDecidableLE

/-- A bundle extends the person–number bundle exactly when it has that person and number. -/
theorem personNumber_le_iff {p : Person} {n : Number} {x : Bundle} :
    personNumber p n ≤ x ↔ x .person = p ∧ x .number = n := by
  refine ⟨fun h ↦ ⟨Flat.coe_le_iff.1 (h .person), Flat.coe_le_iff.1 (h .number)⟩, ?_⟩
  rintro ⟨hp, hn⟩ d
  cases d <;> simp [hp, hn]

/-- The person a bundle bears, third where it bears none. -/
def person (b : Bundle) : Person := (b .person).unbotD .third

@[simp] theorem person_personNumber (p : Person) (n : Number) : (personNumber p n).person = p :=
  rfl

/-- A bundle is a speech-act participant's when the person it bears is. -/
def IsSAP (b : Bundle) : Prop := b.person.IsSAP

instance (b : Bundle) : Decidable b.IsSAP := inferInstanceAs (Decidable b.person.IsSAP)

/-- A bundle is plural when its number is. -/
def IsPlural (b : Bundle) : Prop := b .number = ↑Number.plural

instance (b : Bundle) : Decidable b.IsPlural := inferInstanceAs (Decidable (_ = _))

/-- The six bundles of the first, second and third persons in the singular and the plural, the
cells of a paradigm without clusivity or a dual. -/
def personNumberCells : List Bundle :=
  [Number.singular, .plural].flatMap fun n ↦ [Person.first, .second, .third].map (personNumber · n)

end Bundle

instance : Repr Bundle where
  reprPrec b _ := repr (b .person, b .number, b .gender, b .case, b .definiteness)

end Agreement
