module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.DeriveFintype

/-!
# Persistence levels

Grimm replaces Dowty's five Proto-Patient entailments by four persistence features, existential
and qualitative persistence at the beginning and at the end of the event. Their logical
dependencies, that an entity that exists does so with its qualities and that nonexistence at a
boundary erases them, leave five valid combinations, ordered by inclusion: a lattice with a
creation branch (`exPersEnd`) and an affectedness branch (`exPersBeginning ≤ quPersBeginning`)
rejoining at `totalPersistence`.

## Main definitions

* `PersistenceLevel.Feature`: the four persistence features.
* `PersistenceLevel`: the five valid combinations, each a set of features.
* `PersistenceLevel.Valid`: Grimm's exclusion principles, with `range_features` showing that the
  five levels are exactly the combinations they leave.

## Implementation notes

A level is `SetLike` over its features, so its order is inclusion. Grimm's first principle, that
some qualitative persistence accompanies existential persistence, is read as qualitative
persistence at the beginning with existence there and some qualitative persistence with existence
at the end; this is the reading under which exactly five combinations remain, as the paper says.
The levels are closed under union but not under intersection, so the meet is the largest level
inside the intersection, given by a table.

## References

* [grimm-2011]
-/

@[expose] public section

namespace ArgumentStructure

/-- The five valid persistence levels ([grimm-2011] pp.524–525, Fig. 2). -/
inductive PersistenceLevel where
  /-- No entailed existence, as for the arguments of *seek*, *want* and negated copulas. -/
  | totalNonPersistence
  /-- The entity comes into existence, as the objects of *build*, *invent* and the subject of
  *appear* do. -/
  | exPersEnd
  /-- The entity exists before the event and ceases to, as the subjects of *die*, *evaporate*
  and the objects of *destroy*, *ruin* do. -/
  | exPersBeginning
  /-- The entity persists but is qualitatively changed, as the objects of transitive *move*,
  *dim*, *frighten* and the intransitive subject of *fall* are. -/
  | quPersBeginning
  /-- The entity persists unchanged throughout, as prototypical transitive subjects and the
  unaffected objects of *see* and *cut at* do. -/
  | totalPersistence
  deriving DecidableEq, Repr, Fintype

namespace PersistenceLevel

/-- The four persistence features ([grimm-2011] Table 2). -/
inductive Feature where
  /-- Existential persistence at the beginning of the event. -/
  | exPB
  /-- Existential persistence at the end of the event. -/
  | exPE
  /-- Qualitative persistence at the beginning of the event. -/
  | quPB
  /-- Qualitative persistence at the end of the event. -/
  | quPE
  deriving DecidableEq, Repr, Fintype

/-- The features of a level. -/
def features : PersistenceLevel → Finset Feature
  | .totalNonPersistence => ∅
  | .exPersEnd => {.exPE, .quPE}
  | .exPersBeginning => {.exPB, .quPB}
  | .quPersBeginning => {.exPB, .exPE, .quPB}
  | .totalPersistence => {.exPB, .exPE, .quPB, .quPE}

theorem features_injective : Function.Injective features := by decide

/-- Grimm's exclusion principles on persistence features: qualities persist at a boundary only
where the entity exists there, existence at the beginning brings qualitative persistence at the
beginning, and existence at the end brings some qualitative persistence. -/
def Valid (s : Finset Feature) : Prop :=
  (.quPB ∈ s ↔ .exPB ∈ s) ∧ (.quPE ∈ s → .exPE ∈ s) ∧ (.exPE ∈ s → .quPB ∈ s ∨ .quPE ∈ s)

instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The five levels are exactly the combinations of features the exclusion principles leave. -/
theorem range_features : Set.range features = {s | Valid s} :=
  Set.ext <| (by decide : ∀ s, (∃ l, features l = s) ↔ Valid s)

instance : SetLike PersistenceLevel Feature where
  coe l := l.features
  coe_injective _ _ h := features_injective (Finset.coe_injective h)

instance : PartialOrder PersistenceLevel := .ofSetLike PersistenceLevel

@[simp] theorem mem_features {l : PersistenceLevel} {f : Feature} : f ∈ l.features ↔ f ∈ l :=
  Iff.rfl

instance (l : PersistenceLevel) : DecidablePred (· ∈ l) := fun f ↦
  inferInstanceAs (Decidable (f ∈ l.features))

theorem le_iff_features_subset {l m : PersistenceLevel} : l ≤ m ↔ l.features ⊆ m.features :=
  IsConcreteLE.le_iff.trans Finset.coe_subset

instance : DecidableRel (α := PersistenceLevel) (· ≤ ·) := fun _ _ ↦
  decidable_of_iff _ le_iff_features_subset.symm

/-- The join of two levels, the level whose features are the union of theirs. -/
def sup' : PersistenceLevel → PersistenceLevel → PersistenceLevel
  | .totalNonPersistence, x | x, .totalNonPersistence => x
  | .totalPersistence, _ | _, .totalPersistence => .totalPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning | .quPersBeginning, .exPersBeginning => .quPersBeginning
  | .exPersBeginning, .exPersEnd | .exPersEnd, .exPersBeginning => .totalPersistence
  | .exPersEnd, .quPersBeginning | .quPersBeginning, .exPersEnd => .totalPersistence

/-- The meet of two levels, the largest level inside the intersection of their features. -/
def inf' : PersistenceLevel → PersistenceLevel → PersistenceLevel
  | .totalPersistence, x | x, .totalPersistence => x
  | .totalNonPersistence, _ | _, .totalNonPersistence => .totalNonPersistence
  | .exPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersEnd, .exPersEnd => .exPersEnd
  | .quPersBeginning, .quPersBeginning => .quPersBeginning
  | .exPersBeginning, .quPersBeginning | .quPersBeginning, .exPersBeginning => .exPersBeginning
  | .exPersBeginning, .exPersEnd | .exPersEnd, .exPersBeginning => .totalNonPersistence
  | .exPersEnd, .quPersBeginning | .quPersBeginning, .exPersEnd => .totalNonPersistence

theorem features_sup' (l m : PersistenceLevel) : (sup' l m).features = l.features ∪ m.features := by
  revert l m; decide

instance : Lattice PersistenceLevel where
  __ := (inferInstance : PartialOrder PersistenceLevel)
  sup := sup'
  inf := inf'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder PersistenceLevel where
  bot := .totalNonPersistence
  bot_le := by decide
  top := .totalPersistence
  le_top := by decide

end PersistenceLevel

end ArgumentStructure
