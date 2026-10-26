module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Tense.Allen

/-!
# Clause chaining

A clause chain is a sequence of medial clauses, dependent and morphologically reduced, closed by
one final clause that supplies tense, mood and often agreement for the whole chain; Foley and Van
Valin and Longacre take it as the prototypical cosubordinate combination of clauses, dependent but
not embedded. A language's medial forms are an instance of `MedialForm`, which records for each
form the switch-reference value it marks, the interclausal relations it encodes, whether it
indexes the subject of its clause, and the cell of Allen relations in which it places the time of
its clause relative to the time the clause is evaluated against, as a relative tense does in
Toosarvandani's account of Northern Paiute. A language evaluates each medial clause against the
next clause, as Manambu does, or against the final clause, as Northern Paiute does; in the first
case the time of the first clause of a chain stands to that of the final clause in the composite
of the cells along the chain.

## Main definitions

* `SwitchReference`: same subject or different subject.
* `InterclauseRelation`: the relations a medial form can encode.
* `MedialForm`: the class of a language's medial forms, with `MedialForm.HasSR` and
  `MedialForm.SSUnmarked` for its switch-reference system and `MedialForm.relationsMarked`.
* `MedialForm.chainTiming`: the cell of a chain whose clauses are each evaluated against the next.

## TODO

The Korean, Turkish and Nungon forms record their timing only through the relations `sequential`
and `simultaneous`, which should give way to cells, and the relations should be Dixon's semantic
types of clause linking.

## References

* [sarvasy-aikhenvald-2025]
* [foley-r-d-van-valin-1984]
* [longacre-2007]
* [toosarvandani-2016]
* [dixon-2009]
-/

@[expose] public section

/-- The switch-reference value a medial form marks: the subject of its clause is the same as that
of the reference clause, or different. -/
inductive SwitchReference where
  /-- Same subject. -/
  | ss
  /-- Different subject. -/
  | ds
  deriving DecidableEq, Repr, Fintype

/-- A semantic relation between a medial clause and the next clause that a medial form can
encode. -/
inductive InterclauseRelation where
  /-- The medial event precedes the next event, in iconic order. -/
  | sequential
  /-- The medial event overlaps the next event. -/
  | simultaneous
  /-- The medial event is the reason for the next event. -/
  | causal
  /-- The medial event is a condition on the next event. -/
  | conditional
  /-- The medial event holds despite the next event. -/
  | concessive
  /-- The medial event specifies how the next event occurs. -/
  | manner
  /-- The events contrast. -/
  | contrastive
  /-- The medial event is added without temporal or causal import. -/
  | additive
  /-- The medial event is the purpose of the next event. -/
  | purpose
  deriving DecidableEq, Repr, Fintype

/-- The temporal relations, sequence and simultaneity. -/
def InterclauseRelation.Temporal (r : InterclauseRelation) : Prop :=
  r = .sequential ∨ r = .simultaneous

instance : DecidablePred InterclauseRelation.Temporal :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A language's medial forms: the switch-reference value each marks, the interclausal relations
it encodes, the cell in which it places the time of its clause, and whether it indexes the subject
of its clause. -/
class MedialForm (M : Type*) where
  /-- The switch-reference value a form marks, `none` for a form neutral to it. -/
  sr : M → Option SwitchReference
  /-- The interclausal relations a form encodes. -/
  relations : M → Finset InterclauseRelation
  /-- The cell of Allen relations in which a form places the time of its clause relative to the
  time the clause is evaluated against, every relation for a form that leaves it open. -/
  timing : M → Finset Allen.Relation := fun _ ↦ Allen.atoms
  /-- The form carries subject cross-referencing. -/
  IndexesSubject : M → Prop
  [decidableIndexesSubject : DecidablePred IndexesSubject]

namespace MedialForm

attribute [instance_reducible] decidableIndexesSubject
attribute [instance] decidableIndexesSubject

/-! ### The switch-reference system -/

section

variable (M : Type*) [MedialForm M]

/-- Some medial form marks switch-reference. -/
def HasSR : Prop := ∃ m : M, sr m ≠ none

/-- The same-subject forms leave the subject unindexed and the different-subject forms index it,
the dominant markedness pattern of switch-reference. -/
def SSUnmarked : Prop :=
  (∀ m : M, sr m = some .ss → ¬ IndexesSubject m) ∧ ∀ m : M, sr m = some .ds → IndexesSubject m

variable [Fintype M]

instance : Decidable (HasSR M) := inferInstanceAs (Decidable (∃ m : M, sr m ≠ none))

instance : Decidable (SSUnmarked M) := inferInstanceAs (Decidable (_ ∧ _))

/-- The relations some medial form encodes. -/
def relationsMarked : Finset InterclauseRelation := (Finset.univ : Finset M).biUnion relations

end

@[simp] theorem mem_relationsMarked {M : Type*} [MedialForm M] [Fintype M]
    {r : InterclauseRelation} : r ∈ relationsMarked M ↔ ∃ m : M, r ∈ relations m := by
  simp [relationsMarked]

/-! ### Timing -/

section

variable {M : Type*} [MedialForm M]

/-- The cell in which the time of the first clause of a chain with the forms `ms` stands to the
time of the final clause, when each clause is evaluated against the next. -/
def chainTiming (ms : List M) : Finset Allen.Relation := Allen.compAlong (ms.reverse.map timing)

@[simp] theorem chainTiming_nil : chainTiming ([] : List M) = Allen.eq := rfl

theorem chainTiming_concat (ms : List M) (m : M) :
    chainTiming (ms ++ [m]) = Allen.comp (chainTiming ms) (timing m) := by
  simp [chainTiming, Allen.compAlong]

end

end MedialForm
