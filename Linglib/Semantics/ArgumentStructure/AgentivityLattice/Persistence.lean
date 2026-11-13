module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Persistence levels

Grimm replaces Dowty's five Proto-Patient entailments by four persistence features, existential
and qualitative persistence at the beginning and at the end of the event. Their logical
dependencies, that an entity that exists does so with its qualities and that nonexistence at a
boundary erases them, leave five valid combinations, ordered by inclusion: a lattice with a
creation branch (`existentialEnd`) and an affectedness branch
(`existentialBeginning ≤ qualitativeBeginning`)
rejoining at `total`.

## Implementation notes

A level is `SetLike` over its features, so its order is inclusion. Grimm's first principle, that
some qualitative persistence accompanies existential persistence, is read as qualitative
persistence at the beginning with existence there and some qualitative persistence with existence
at the end; this is the reading under which exactly five combinations remain, as the paper says.
The third principle is a disjunction, so the levels are closed under union but not under
intersection, and the lattice is lifted along
[the adjunction](##ArgumentStructure.Persistence.gc_features_interior) between a level's
features and the largest level inside a set of features.
`AgentivityLattice/OfLifespan.lean` assigns a participant its level from its life span and an
event's run time.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure

/-- The five valid persistence levels ([grimm-2011] pp.524–525, Fig. 2). -/
inductive Persistence where
  /-- No entailed existence, as for the arguments of *seek*, *want* and negated copulas. -/
  | nonPersistence
  /-- The entity comes into existence, as the objects of *build*, *invent* and the subject of
  *appear* do. -/
  | existentialEnd
  /-- The entity exists before the event and ceases to, as the subjects of *die*, *evaporate*
  and the objects of *destroy*, *ruin* do. -/
  | existentialBeginning
  /-- The entity persists but is qualitatively changed, as the objects of transitive *move*,
  *dim*, *frighten* and the intransitive subject of *fall* are. -/
  | qualitativeBeginning
  /-- The entity persists unchanged throughout, as prototypical transitive subjects and the
  unaffected objects of *see* and *cut at* do. -/
  | total
  deriving DecidableEq, Repr, Fintype

namespace Persistence

/-- The four persistence features ([grimm-2011] Table 2). -/
inductive Feature where
  /-- Existential persistence at the beginning of the event, the paper's ExPB. -/
  | existsAtBeginning
  /-- Existential persistence at the end of the event, ExPE. -/
  | existsAtEnd
  /-- Qualitative persistence at the beginning of the event, QuPB. -/
  | qualitiesAtBeginning
  /-- Qualitative persistence at the end of the event, QuPE. -/
  | qualitiesAtEnd
  deriving DecidableEq, Repr, Fintype

/-- The features of a level. -/
def features : Persistence → Finset Feature
  | .nonPersistence => ∅
  | .existentialEnd => {.existsAtEnd, .qualitiesAtEnd}
  | .existentialBeginning => {.existsAtBeginning, .qualitiesAtBeginning}
  | .qualitativeBeginning => {.existsAtBeginning, .existsAtEnd, .qualitiesAtBeginning}
  | .total => {.existsAtBeginning, .existsAtEnd, .qualitiesAtBeginning, .qualitiesAtEnd}

theorem features_injective : Function.Injective features := by decide

/-- Grimm's exclusion principles on persistence features: qualities persist at a boundary only
where the entity exists there, existence at the beginning brings qualitative persistence at the
beginning, and existence at the end brings some qualitative persistence. -/
def Valid (s : Finset Feature) : Prop :=
  (.qualitiesAtBeginning ∈ s ↔ .existsAtBeginning ∈ s) ∧ (.qualitiesAtEnd ∈ s → .existsAtEnd ∈ s) ∧
    (.existsAtEnd ∈ s → .qualitiesAtBeginning ∈ s ∨ .qualitiesAtEnd ∈ s)

instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The five levels are exactly the combinations of features the exclusion principles leave. -/
theorem range_features : Set.range features = {s | Valid s} :=
  Set.ext <| (by decide : ∀ s, (∃ l, features l = s) ↔ Valid s)

instance : SetLike Persistence Feature where
  coe l := l.features
  coe_injective _ _ h := features_injective (Finset.coe_injective h)

instance : PartialOrder Persistence := .ofSetLike Persistence

@[simp] theorem mem_features {l : Persistence} {f : Feature} : f ∈ l.features ↔ f ∈ l :=
  Iff.rfl

instance (l : Persistence) : DecidablePred (· ∈ l) := fun f ↦
  inferInstanceAs (Decidable (f ∈ l.features))

theorem le_iff_features_subset {l m : Persistence} : l ≤ m ↔ l.features ⊆ m.features :=
  IsConcreteLE.le_iff.trans Finset.coe_subset

instance : DecidableRel (α := Persistence) (· ≤ ·) := fun _ _ ↦
  decidable_of_iff _ le_iff_features_subset.symm

instance : DecidableLT Persistence := fun _ _ ↦ decidable_of_iff _ lt_iff_le_not_ge.symm

/-! ### The lattice

The levels are closed under union of features but not under intersection, so the largest level
inside a set of features exists, and it is upper adjoint to the features of a level. The lattice
structure is lifted along the adjunction: the join of two levels has the union of their features,
and their meet is the largest level inside the intersection. -/

/-- The largest level whose features are among `s`. -/
def interior (s : Finset Feature) : Persistence :=
  if .existsAtBeginning ∈ s ∧ .qualitiesAtBeginning ∈ s then
    if .existsAtEnd ∈ s then if .qualitiesAtEnd ∈ s then .total else .qualitativeBeginning
    else .existentialBeginning
  else if .existsAtEnd ∈ s ∧ .qualitiesAtEnd ∈ s then .existentialEnd else .nonPersistence

/-- A level's features are among `s` exactly when the level is below the largest level inside
`s`. -/
theorem gc_features_interior : GaloisConnection features interior := by
  intro l s; revert l s; decide

/-- The levels are a retract of the sets of features. -/
def gciFeaturesInterior : GaloisCoinsertion features interior :=
  gc_features_interior.toGaloisCoinsertion (by decide)

@[simp] theorem interior_features (l : Persistence) : interior l.features = l :=
  gciFeaturesInterior.u_l_eq l

instance : Lattice Persistence := gciFeaturesInterior.liftLattice

theorem features_sup (l m : Persistence) : (l ⊔ m).features = l.features ∪ m.features := by
  revert l m; decide

theorem features_inf_subset (l m : Persistence) :
    (l ⊓ m).features ⊆ l.features ∩ m.features :=
  gc_features_interior.l_u_le _

instance : BoundedOrder Persistence where
  bot := .nonPersistence
  bot_le := by decide
  top := .total
  le_top := by decide

/-! ### Features as intervals

Grimm's three degrees of affectedness, no change, qualitative change and existential change, are
cuts of the lattice: each feature, and existence at both ends, holds on an up-set or fails on a
down-set of levels. -/

variable {l : Persistence}

/-- An entity exists when the event begins at existential persistence (beginning) and above. -/
theorem existsAtBeginning_mem_iff_le : .existsAtBeginning ∈ l ↔ existentialBeginning ≤ l := by
  revert l; decide

/-- An entity exists when the event ends at existential persistence (end) and above. -/
theorem existsAtEnd_mem_iff_le :
    .existsAtEnd ∈ l ↔ existentialEnd ≤ l ∨ qualitativeBeginning ≤ l := by
  revert l; decide

/-- An entity exists at both ends of the event at qualitative persistence (beginning) and above. -/
theorem existsAtBothEnds_iff_le :
    .existsAtBeginning ∈ l ∧ .existsAtEnd ∈ l ↔ qualitativeBeginning ≤ l := by
  revert l; decide

/-- An entity is not entailed to keep its qualities to the end of the event at qualitative
persistence (beginning) and below. -/
theorem qualitiesAtEnd_notMem_iff_le : .qualitiesAtEnd ∉ l ↔ l ≤ qualitativeBeginning := by
  revert l; decide

end Persistence

end ArgumentStructure
