module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.BoundedComplete
public import Linglib.Morphology.Word.Features
public import Linglib.Syntax.Feature.Person.Specification

/-!
# Feature bundles

A feature bundle gives a slot to each of the five dimensions in which the form of one element
may covary with another: person, number, gender, case and definiteness, the first three the
φ-features (`Agreement.Dimension.phi`). The index of a bundle and its concord
(`Agreement.Bundle.index`, `Agreement.Bundle.concord`) are its projections onto the φ-features
and onto case, number and gender, and two elements agree in one of them when the projections of
their bundles are compatible. Bundles are compatible exactly when they unify
(`Agreement.Bundle.coe_sup_coe_eq_top_iff`). The person slot is a person specification
(`Syntax/Feature/Person/Specification.lean`), so that a form with no clusivity is less specific
than an inclusive or an exclusive one, and the others are slots of the flat order
of `Core/Order/Flat.lean`, a value or nothing. The partial order of bundles, their bottom, the
wholly unspecified bundle, and their unification are the pointwise ones. Each dimension is a
token feature with that feature's values, and [a token's bundle](##Agreement.Bundle.ofFeatures)
is its features read along that inclusion, the person slot from the token's person and
clusivity together.

## Implementation notes

A person and a clusivity that no participant set satisfies, as the second person and the
exclusive, have no specification, and no monotone map could give them one: its value would
extend both the second person and the exclusive, which are incompatible. The person slot of such
a token is `⊥`, so `Agreement.Bundle.ofFeatures` is monotone on the coherent tokens
(`Agreement.Bundle.monotoneOn_ofFeatures`) and not outright.

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

instance (d : Dimension) (x y : d.Slot) : Decidable (Compat x y) := by
  cases d <;> exact inferInstance

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

/-- Unification of two slots, `⊤` when they are incompatible: person specifications unify to what
both cover, and two values unify when they are equal. -/
def Dimension.Slot.unify : (d : Dimension) → d.Slot → d.Slot → WithTop d.Slot
  | .person => Finset.unify
  | .number => Flat.unify
  | .gender => Flat.unify
  | .case => Flat.unify
  | .definiteness => Flat.unify

theorem Dimension.Slot.isLUB_unify (d : Dimension) (a b : d.Slot) :
    IsLUB ({↑a, ↑b} : Set (WithTop d.Slot)) (Dimension.Slot.unify d a b) := by
  cases d
  · exact Finset.isLUB_unify a b
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

/-- The bundle with the dimension `d` set to the value `v`. -/
def set (d : Dimension) (v : d.Value) (b : Bundle) : Bundle :=
  Function.update b d (Dimension.Slot.ofFlat d (v : Flat d.Value))

/-- The bundle valued in person and number alone, the person a specification, as which a person
value is read. -/
def personNumber (x : Person.Specification) (n : Number) : Bundle :=
  Function.update (set .number n ⊥) .person x

@[simp] theorem personNumber_person (x : Person.Specification) (n : Number) :
    personNumber x n .person = x :=
  rfl

@[simp] theorem personNumber_number (x : Person.Specification) (n : Number) :
    personNumber x n .number = n :=
  rfl

@[simp] theorem personNumber_gender (x : Person.Specification) (n : Number) :
    personNumber x n .gender = ⊥ :=
  rfl

@[simp] theorem personNumber_case (x : Person.Specification) (n : Number) :
    personNumber x n .case = ⊥ :=
  rfl

@[simp] theorem personNumber_definiteness (x : Person.Specification) (n : Number) :
    personNumber x n .definiteness = ⊥ :=
  rfl

/-- The restriction of a token's features to the agreement dimensions reads them along
`Dimension.toFeature`. -/
def ofFeatures (f : Morphology.Features) : Bundle
  | .person => .ofPersonClusivity (f .person) (f .clusivity)
  | .number => f .number
  | .gender => f .gender
  | .case => f .case
  | .definiteness => f .definiteness

@[simp] theorem ofFeatures_person (f : Morphology.Features) :
    ofFeatures f .person = .ofPersonClusivity (f .person) (f .clusivity) :=
  rfl

@[simp] theorem ofFeatures_number (f : Morphology.Features) : ofFeatures f .number = f .number :=
  rfl

@[simp] theorem ofFeatures_gender (f : Morphology.Features) : ofFeatures f .gender = f .gender :=
  rfl

@[simp] theorem ofFeatures_case (f : Morphology.Features) : ofFeatures f .case = f .case := rfl

@[simp] theorem ofFeatures_definiteness (f : Morphology.Features) :
    ofFeatures f .definiteness = f .definiteness :=
  rfl

/-- More specific features give a more specific bundle, where the more specific person and
clusivity are coherent. -/
theorem ofFeatures_le_ofFeatures {f g : Morphology.Features} (h : f ≤ g)
    (hg : Person.Specification.Coherent (g .person) (g .clusivity)) :
    ofFeatures f ≤ ofFeatures g := by
  intro d
  cases d
  · exact Person.Specification.ofPersonClusivity_le_ofPersonClusivity (h .person) (h .clusivity) hg
  all_goals exact h _

theorem monotoneOn_ofFeatures :
    MonotoneOn ofFeatures {f | Person.Specification.Coherent (f .person) (f .clusivity)} :=
  fun _ _ _ hg h ↦ ofFeatures_le_ofFeatures h hg

/-- The bundle of features is not monotone outright: the second person with the exclusive is
unspecified for person. -/
theorem not_monotone_ofFeatures : ¬ Monotone ofFeatures := fun h ↦
  absurd (h (a := .of (person := some .second))
    (b := .of (person := some .second) (clusivity := some .exclusive)) (by decide)) (by decide)

instance : DecidableLE Bundle := fun x y ↦ inferInstanceAs (Decidable (∀ d, x d ≤ y d))

instance : DecidableLT Bundle := decidableLTOfDecidableLE

/-- A bundle extends the person–number bundle exactly when its person is covered by that person
and it has that number. -/
theorem personNumber_le_iff {p : Person.Specification} {n : Number} {x : Bundle} :
    personNumber p n ≤ x ↔ p ≤ x .person ∧ x .number = n := by
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
  [Number.singular, .plural].flatMap fun n ↦
    [Person.Specification.first, .second, .third].map (personNumber · n)

end Bundle

instance : Repr Bundle where
  reprPrec b _ := repr (b .person, b .number, b .gender, b .case, b .definiteness)

end Agreement
