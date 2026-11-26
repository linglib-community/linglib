/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.BoundedComplete
public import Linglib.Morphology.Word.Features

/-!
# Feature bundles

A feature bundle gives a slot to each of the five dimensions in which the form of one element
may covary with another: person, number, gender, case and definiteness, the first three the
φ-features (`Agreement.Dimension.phi`). The index of a bundle and its concord
(`Agreement.Bundle.index`, `Agreement.Bundle.concord`) are its projections onto the φ-features
and onto case, number and gender, and two elements agree in one of them when the projections of
their bundles are compatible. Bundles are compatible exactly when they unify
(`Agreement.Bundle.coe_sup_coe_eq_top_iff`). A slot is a value or nothing, in the flat order of
`Core/Order/Flat.lean`, and the person slot is a pair of them, a person and a clusivity, so that
a first person form with no clusivity is less specific than an inclusive or an exclusive one.
The partial order of bundles, their bottom, the wholly unspecified bundle, and their unification
are the pointwise ones. Each dimension is a token feature with that feature's values, and
[a token's bundle](##Agreement.Bundle.ofFeatures) is its features read along that inclusion, the
person slot from the token's person and clusivity together.

## Implementation notes

The slots hold labels and nothing about what a label refers to. The person slot pairs any
person with any clusivity, the second person with the exclusive among them: which pairs some
referent satisfies is a fact about participant sets, stated where a person and a clusivity are
read as the participant sets they cover (`Syntax/Feature/Person/Specification.lean`), and no
rule of agreement consults it.

Clusivity is a part of the person slot and not a sixth dimension, as the inclusive and the
exclusive are values of person in the classification the dimensions follow, and a language
distinguishes values in each dimension with no clusivity among them.

Bundles are borne by pronouns and nominals as well as by agreement targets, and are spelled out
by morphology, so the file stands with the feature inventories below `Syntax/Agreement` and
`Morphology`. Its declarations keep the namespace `Agreement`.

The slots hold the cross-linguistic values of the token features, so that bundles of different
languages compare. A language-particular system, such as a set of noun classes, is not a
bundle; `Syntax/Feature/Gender/AgreementClasses.lean` treats those over an arbitrary feature type.

## References

* [corbett-1998]
* [corbett-2006]
* [norris-2019]
* [wechsler-zlatic-2000]
-/

@[expose] public section

namespace Agreement

/-- A dimension is a feature in which a target's form may covary with another element, one of the
three indisputable agreement features or the two contested ones ([corbett-1998]). -/
inductive Dimension where
  | person | number | gender | case | definiteness
  deriving DecidableEq, Repr, Fintype

/-- The φ-features are the three indisputable agreement features, person, number and gender
([corbett-2006]). -/
def Dimension.phi : Finset Dimension := {.person, .number, .gender}

/-- The concord features are case, number and gender, those in which the elements of a noun
phrase covary ([wechsler-zlatic-2000]). -/
def Dimension.concord : Finset Dimension := {.case, .number, .gender}

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

/-- The slot of a dimension: a person and a clusivity, each a value or `⊥`, for person, and a
value or `⊥` for the others. -/
abbrev Dimension.Slot : Dimension → Type
  | .person => Flat Person × Flat Clusivity
  | .number => Flat Number
  | .gender => Flat UD.Gender
  | .case => Flat Case
  | .definiteness => Flat UD.Definite

instance (d : Dimension) : DecidableEq d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : PartialOrder d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : OrderBot d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) : DecidableLE d.Slot := by cases d <;> exact inferInstance

instance (d : Dimension) (x y : d.Slot) : Decidable (Compat x y) := by
  cases d <;> exact inferInstance

/-- A value of a dimension or `⊥` as a slot, a person with no clusivity. -/
def Dimension.Slot.ofFlat : (d : Dimension) → Flat d.Value → d.Slot
  | .person, x => (x, ⊥)
  | .number, x => x
  | .gender, x => x
  | .case, x => x
  | .definiteness, x => x

@[simp] theorem Dimension.Slot.ofFlat_bot (d : Dimension) : Dimension.Slot.ofFlat d ⊥ = ⊥ := by
  cases d <;> rfl

@[simp] theorem Dimension.Slot.ofFlat_person_bot :
    Dimension.Slot.ofFlat .person (⊥ : Flat Person) = ⊥ :=
  rfl

theorem Dimension.Slot.ofFlat_person (x : Flat Person) :
    Dimension.Slot.ofFlat .person x = (x, ⊥) :=
  rfl

/-- Unification of two slots, `⊤` when they are incompatible: two values unify when they are
equal, and two person slots when their persons and their clusivities do. -/
def Dimension.Slot.unify : (d : Dimension) → d.Slot → d.Slot → WithTop d.Slot
  | .person => WithTop.prodUnify Flat.unify Flat.unify
  | .number => Flat.unify
  | .gender => Flat.unify
  | .case => Flat.unify
  | .definiteness => Flat.unify

theorem Dimension.Slot.isLUB_unify (d : Dimension) (a b : d.Slot) :
    IsLUB ({↑a, ↑b} : Set (WithTop d.Slot)) (Dimension.Slot.unify d a b) := by
  cases d
  · exact WithTop.isLUB_prodUnify Flat.isLUB_unify Flat.isLUB_unify a b
  all_goals exact Flat.isLUB_unify a b

/-- A feature bundle assigns each dimension a slot. -/
abbrev Bundle := (d : Dimension) → d.Slot

/-- With the failure of unification adjoined as `⊤`, bundles form a join-semilattice whose join
unifies dimension by dimension. -/
instance : SemilatticeSup (WithTop Bundle) :=
  WithTop.semilatticeSupOfIsLUB (WithTop.piUnify Dimension.Slot.unify)
    (WithTop.isLUB_piUnify Dimension.Slot.isLUB_unify)

/-- Unifying with a bundle that bears one slot unifies at that dimension. -/
theorem Bundle.coe_sup_coe_update_bot (b : Bundle) (d : Dimension) (x : d.Slot) :
    (b : WithTop Bundle) ⊔ ↑(Function.update (⊥ : Bundle) d x) =
      (Dimension.Slot.unify d (b d) x).map (Function.update b d) :=
  WithTop.piUnify_update_bot Dimension.Slot.isLUB_unify b d x

/-- Two bundles fail to unify exactly when they are incompatible. -/
theorem Bundle.coe_sup_coe_eq_top_iff {x y : Bundle} :
    (x : WithTop Bundle) ⊔ y = ⊤ ↔ ¬ Compat x y :=
  WithTop.eq_top_iff_of_isLUB (WithTop.isLUB_piUnify Dimension.Slot.isLUB_unify x y)

namespace Bundle

/-- The index of a bundle, its φ-features: the projection onto person, number and gender. -/
def index (x : Bundle) : (d : Dimension.phi) → Dimension.Slot d := Dimension.phi.restrict x

/-- The concord of a bundle: the projection onto case, number and gender. -/
def concord (x : Bundle) : (d : Dimension.concord) → Dimension.Slot d :=
  Dimension.concord.restrict x

@[simp] theorem index_apply (x : Bundle) (d : Dimension.phi) : x.index d = x d := rfl

@[simp] theorem concord_apply (x : Bundle) (d : Dimension.concord) : x.concord d = x d := rfl

/-- The person of a bundle, a value or `⊥`. -/
def person (x : Bundle) : Flat Person := (x .person).1

/-- The clusivity of a bundle, a value or `⊥`. -/
def clusivity (x : Bundle) : Flat Clusivity := (x .person).2

/-- The bundle with the dimension `d` set to the value `v`, a person with no clusivity. -/
def set (d : Dimension) (v : d.Value) (b : Bundle) : Bundle :=
  Function.update b d (Dimension.Slot.ofFlat d (v : Flat d.Value))

/-- The bundle with its clusivity set to `c` and its person kept. -/
def setClusivity (c : Clusivity) (b : Bundle) : Bundle :=
  Function.update b .person (b.person, ↑c)

@[simp] theorem person_setClusivity (c : Clusivity) (b : Bundle) :
    (b.setClusivity c).person = b.person :=
  rfl

@[simp] theorem clusivity_setClusivity (c : Clusivity) (b : Bundle) :
    (b.setClusivity c).clusivity = c :=
  rfl

/-- The bundle valued in person and number alone. -/
def personNumber (p : Person) (n : Number) : Bundle := set .person p (set .number n ⊥)

@[simp] theorem personNumber_person (p : Person) (n : Number) :
    personNumber p n .person = (↑p, ⊥) :=
  rfl

@[simp] theorem person_personNumber (p : Person) (n : Number) : (personNumber p n).person = p :=
  rfl

@[simp] theorem clusivity_personNumber (p : Person) (n : Number) :
    (personNumber p n).clusivity = ⊥ :=
  rfl

@[simp] theorem personNumber_number (p : Person) (n : Number) : personNumber p n .number = n :=
  rfl

@[simp] theorem personNumber_gender (p : Person) (n : Number) : personNumber p n .gender = ⊥ :=
  rfl

@[simp] theorem personNumber_case (p : Person) (n : Number) : personNumber p n .case = ⊥ :=
  rfl

@[simp] theorem personNumber_definiteness (p : Person) (n : Number) :
    personNumber p n .definiteness = ⊥ :=
  rfl

/-- The restriction of a token's features to the agreement dimensions reads them along
`Dimension.toFeature`. -/
def ofFeatures (f : Morphology.Features) : Bundle
  | .person => (f .person, f .clusivity)
  | .number => f .number
  | .gender => f .gender
  | .case => f .case
  | .definiteness => f .definiteness

@[simp] theorem ofFeatures_person (f : Morphology.Features) :
    ofFeatures f .person = (f .person, f .clusivity) :=
  rfl

@[simp] theorem ofFeatures_number (f : Morphology.Features) : ofFeatures f .number = f .number :=
  rfl

@[simp] theorem ofFeatures_gender (f : Morphology.Features) : ofFeatures f .gender = f .gender :=
  rfl

@[simp] theorem ofFeatures_case (f : Morphology.Features) : ofFeatures f .case = f .case := rfl

@[simp] theorem ofFeatures_definiteness (f : Morphology.Features) :
    ofFeatures f .definiteness = f .definiteness :=
  rfl

/-- More specific features give a more specific bundle. -/
theorem ofFeatures_mono : Monotone ofFeatures := fun _ _ h d ↦ by
  cases d
  · exact ⟨h .person, h .clusivity⟩
  all_goals exact h _

/-- `ofFeatures` as an order homomorphism. -/
@[simps]
def ofFeaturesHom : Morphology.Features →o Bundle := ⟨ofFeatures, ofFeatures_mono⟩

instance : DecidableLE Bundle := fun x y ↦ inferInstanceAs (Decidable (∀ d, x d ≤ y d))

instance : DecidableLT Bundle := decidableLTOfDecidableLE

/-- A bundle extends the person–number bundle exactly when it has that person and that
number. -/
theorem personNumber_le_iff {p : Person} {n : Number} {x : Bundle} :
    personNumber p n ≤ x ↔ x.person = p ∧ x .number = n := by
  refine ⟨fun h ↦ ⟨Flat.coe_le_iff.1 (h .person).1, Flat.coe_le_iff.1 (h .number)⟩, ?_⟩
  rintro ⟨hp, hn⟩ d
  cases d
  · exact ⟨Flat.coe_le_iff.2 hp, bot_le⟩
  · exact Flat.coe_le_iff.2 hn
  all_goals exact bot_le

/-- A bundle is plural when its number is. -/
def IsPlural (b : Bundle) : Prop := b .number = ↑Number.plural

instance (b : Bundle) : Decidable b.IsPlural := inferInstanceAs (Decidable (_ = _))

/-- The six bundles of the first, second and third persons in the singular and the plural, the
cells of a paradigm without clusivity or a dual. -/
def personNumberCells : List Bundle :=
  [Number.singular, .plural].flatMap fun n ↦
    [Person.first, .second, .third].map (personNumber · n)

end Bundle

instance : Repr Bundle where
  reprPrec b _ := repr (b.person, b.clusivity, b .number, b .gender, b .case, b .definiteness)

end Agreement
