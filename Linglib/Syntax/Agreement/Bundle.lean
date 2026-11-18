module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.PartialUnify
public import Linglib.Morphology.Word.Features
public import Linglib.Syntax.Person.Specification

/-!
# Feature bundles

This file defines the dimensions in which agreement targets covary and the analytical
feature bundle over them, a value or nothing in each dimension.

An agreement bundle gives each dimension a slot: a person specification
(`Syntax/Person/Specification.lean`) in the person dimension, so that a form with no clusivity
is less specific than an inclusive or an exclusive one, and a slot of the flat order of
`Core/Order/Flat.lean` in the others. Its partial order, its bottom, the wholly unspecified
bundle, and its unification are the pointwise ones. Each dimension is a token feature with that
feature's values, and a token's bundle is its features read along that inclusion,
`Agreement.Bundle.ofFeatures`.

## Main definitions

* `Agreement.Dimension` — the five dimensions a target's form may covary in
* `Agreement.Dimension.toFeature`, `Agreement.Dimension.Value` — the token feature a dimension
  is, and its values
* `Agreement.Dimension.Slot`, `Agreement.Dimension.Slot.ofFlat` — the slot of a dimension, and
  a value or `⊥` as a slot
* `Agreement.Bundle` — a slot in each dimension
* `Agreement.Bundle.set`, `Agreement.Bundle.personNumber` — a bundle with one dimension set,
  and the bundle valued in person and number alone
* `Agreement.Bundle.ofFeatures` — the restriction of a token's features
* `Agreement.Bundle.IsSAP`, `Agreement.Bundle.IsPlural` — the speech-act participant and plural
  bundles
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

/-- The slot of a dimension: a person specification for person, and a value or `⊥` for the
others. -/
abbrev Dimension.Slot : Dimension → Type
  | .person => Person.Specification
  | .number => Flat Number
  | .gender => Flat UD.Gender
  | .case => Flat Case
  | .definiteness => Flat UD.Definite

instance (d : Dimension) : DecidableEq d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : PartialOrder d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : OrderBot d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : DecidableLE d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : PartialUnify d.Slot := by cases d <;> exact inferInstance

/-- A value of a dimension or `⊥` as a slot, a person value as the specification of what it
covers. -/
def Dimension.Slot.ofFlat : (d : Dimension) → Flat d.Value → d.Slot
  | .person, x => x.recBotCoe ⊥ Person.Specification.ofPerson
  | .number, x => x
  | .gender, x => x
  | .case, x => x
  | .definiteness, x => x

@[simp] theorem Dimension.Slot.ofFlat_bot (d : Dimension) : Dimension.Slot.ofFlat d ⊥ = ⊥ := by
  cases d <;> rfl

@[simp] theorem Dimension.Slot.ofFlat_person_bot :
    Dimension.Slot.ofFlat .person (⊥ : Flat Person) = ⊥ :=
  rfl

@[simp] theorem Dimension.Slot.ofFlat_person (p : Person) :
    Dimension.Slot.ofFlat .person (p : Flat Person) = Person.Specification.ofPerson p :=
  rfl

/-- A feature bundle assigns each dimension a slot. -/
abbrev Bundle := (d : Dimension) → d.Slot

namespace Bundle

/-- The bundle with the dimension `d` set to the value `v`. -/
def set (d : Dimension) (v : d.Value) (b : Bundle) : Bundle :=
  Function.update b d (Dimension.Slot.ofFlat d (v : Flat d.Value))

/-- The bundle valued in person and number alone. -/
def personNumber (p : Person) (n : Number) : Bundle :=
  set .number n (set .person p ⊥)

@[simp] theorem personNumber_person (p : Person) (n : Number) :
    personNumber p n .person = Person.Specification.ofPerson p :=
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
def ofFeatures (f : Morphology.Features) : Bundle := fun d ↦ Dimension.Slot.ofFlat d (f d.toFeature)

@[simp] theorem ofFeatures_apply (f : Morphology.Features) (d : Dimension) :
    ofFeatures f d = Dimension.Slot.ofFlat d (f d.toFeature) :=
  rfl

instance : DecidableLE Bundle := fun x y ↦ inferInstanceAs (Decidable (∀ d, x d ≤ y d))

instance : DecidableLT Bundle := decidableLTOfDecidableLE

/-- A bundle extends the person–number bundle exactly when its person is covered by that person
and it has that number. -/
theorem personNumber_le_iff {p : Person} {n : Number} {x : Bundle} :
    personNumber p n ≤ x ↔ Person.Specification.ofPerson p ≤ x .person ∧ x .number = n := by
  refine ⟨fun h ↦ ⟨h .person, Flat.coe_le_iff.1 (h .number)⟩, ?_⟩
  rintro ⟨hp, hn⟩ d
  cases d
  · exact hp
  · exact Flat.coe_le_iff.2 hn
  all_goals exact bot_le

/-- A bundle is a speech-act participant's when its person specification is. -/
def IsSAP (b : Bundle) : Prop := (b .person).IsSAP

instance (b : Bundle) : Decidable b.IsSAP := inferInstanceAs (Decidable (b .person).IsSAP)

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
