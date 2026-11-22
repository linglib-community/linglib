module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Logic.Temporal.IntervalAlgebra

/-!
# Clause chaining

A clause chain is a sequence of medial clauses, dependent and morphologically reduced, closed by
one final clause that supplies tense, mood and often agreement for the whole chain; Foley and Van
Valin and Longacre take it as the prototypical cosubordinate combination of clauses, dependent but
not embedded. A language's medial forms are an instance of `MedialForm`, which records for each
form the switch-reference value it marks, the kinds of clause linking it marks, whether it indexes
the subject of its clause, and the cell of Allen relations in which it places the time of its
clause relative to the time the clause is evaluated against, as a relative tense does in
Toosarvandani's account of Northern Paiute. A language evaluates each medial clause against the
next clause, as Manambu does, or against the final clause, as Northern Paiute does; in the first
case the time of the first clause of a chain stands to that of the final clause in the composite
of the cells along the chain.

The kinds of linking are Dixon's: two linked clauses stand in one of sixteen semantic relations,
the subtypes of six types. Temporal linking is succession ('and then'), relative time ('after',
'before', 'while') or condition; consequence is cause, result or purpose; possible consequence
('lest') stands alone; addition is unordered, of two aspects of one event, elaboration or
contrast; alternatives are disjunction, rejection ('instead of') or suggestion ('rather than');
and manner is real ('like') or hypothetical ('as if').

## Main definitions

* `SwitchReference`: same subject or different subject.
* `Clause.Linking`: the sixteen kinds of clause linking, with `Clause.Linking.type` their six
  types, `Clause.LinkingType`.
* `MedialForm`: the class of a language's medial forms, with `MedialForm.HasSR` and
  `MedialForm.SSUnmarked` for its switch-reference system and `MedialForm.linkingsMarked`.
* `MedialForm.chainTiming`: the cell of a chain whose clauses are each evaluated against the next,
  and `MedialForm.chainTimingHom`, the same as a homomorphism from the chains under concatenation.

## Implementation notes

A form that leaves the kind of linking to the context, as a general medial verb does, marks none.
Whether one clause precedes or overlaps another is not a kind of linking, 'after' and 'while'
both being relative time; it is the `timing` of a form.

## TODO

The Korean and Turkish forms record no timing.

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

namespace Clause

/-- The six semantic types of clause linking. -/
inductive LinkingType where
  | temporal
  | consequence
  | possibleConsequence
  | addition
  | alternatives
  | manner
  deriving DecidableEq, Repr, Fintype

/-- The kinds of clause linking, the semantic relations in which a supporting clause stands to
its focal clause. -/
inductive Linking where
  /-- Temporal succession: one event and then the other. -/
  | succession
  /-- Relative time: the time of one event located by the other, as with 'after', 'before',
  'when', 'since', 'until' and 'while'. -/
  | relativeTime
  /-- The supporting clause is a condition on the focal clause. -/
  | conditional
  /-- The supporting clause gives the reason for the focal clause. -/
  | cause
  /-- The focal clause is a natural consequence of the supporting clause. -/
  | result
  /-- The focal clause is done so that the event of the other will come about. -/
  | purpose
  /-- The supporting clause is a consequence to be guarded against, as with 'lest' and
  'in case'. -/
  | possibleConsequence
  /-- Two pieces of information are added, in no order. -/
  | unorderedAddition
  /-- The clauses describe two aspects of one event. -/
  | sameEventAddition
  /-- The second clause elaborates on the first. -/
  | elaboration
  /-- The focal clause holds against what the supporting clause would lead one to expect, as
  with 'but' and 'although'. -/
  | contrast
  /-- The clauses are alternatives, as with 'or'. -/
  | disjunction
  /-- One alternative is rejected for the other, as with 'instead of'. -/
  | rejection
  /-- One alternative is preferred to the other, as with 'rather than'. -/
  | suggestion
  /-- The supporting clause says how the event of the focal clause is done. -/
  | realManner
  /-- The supporting clause says how the event of the focal clause appears to be done, as with
  'as if'. -/
  | hypotheticalManner
  deriving DecidableEq, Repr, Fintype

/-- The type of a kind of linking. -/
def Linking.type : Linking → LinkingType
  | .succession | .relativeTime | .conditional => .temporal
  | .cause | .result | .purpose => .consequence
  | .possibleConsequence => .possibleConsequence
  | .unorderedAddition | .sameEventAddition | .elaboration | .contrast => .addition
  | .disjunction | .rejection | .suggestion => .alternatives
  | .realManner | .hypotheticalManner => .manner

end Clause

/-- A language's medial forms: the switch-reference value each marks, the kinds of clause linking
it marks, the cell in which it places the time of its clause, and whether it indexes the subject
of its clause. -/
class MedialForm (M : Type*) where
  /-- The switch-reference value a form marks, `none` for a form neutral to it. -/
  sr : M → Option SwitchReference
  /-- The kinds of clause linking a form marks, none for a form that leaves the kind open. -/
  linkings : M → Finset Clause.Linking
  /-- The cell of Allen relations in which a form places the time of its clause relative to the
  time the clause is evaluated against, every relation for a form that leaves it open. -/
  timing : M → IntervalAlgebra := fun _ ↦ ⊤
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

/-- The kinds of clause linking some medial form marks. -/
def linkingsMarked : Finset Clause.Linking := (Finset.univ : Finset M).biUnion linkings

end

@[simp] theorem mem_linkingsMarked {M : Type*} [MedialForm M] [Fintype M]
    {l : Clause.Linking} : l ∈ linkingsMarked M ↔ ∃ m : M, l ∈ linkings m := by
  simp [linkingsMarked]

/-! ### Timing -/

section

variable {M : Type*} [MedialForm M]

/-- The cell in which the time of the first clause of a chain with the forms `ms` stands to the
time of the final clause, when each clause is evaluated against the next. -/
def chainTiming (ms : List M) : IntervalAlgebra := (ms.reverse.map timing).prod

@[simp] theorem chainTiming_nil : chainTiming ([] : List M) = 1 := rfl

@[simp] theorem chainTiming_singleton (m : M) : chainTiming [m] = timing m := by
  simp [chainTiming]

theorem chainTiming_append (ms ns : List M) :
    chainTiming (ms ++ ns) = chainTiming ns * chainTiming ms := by
  simp [chainTiming]

theorem chainTiming_concat (ms : List M) (m : M) :
    chainTiming (ms ++ [m]) = timing m * chainTiming ms := by
  rw [chainTiming_append, chainTiming_singleton]

/-- `chainTiming` as a homomorphism from the chains under concatenation, into the opposite
monoid since a product of cells composes its second factor first. -/
def chainTimingHom : FreeMonoid M →* IntervalAlgebraᵐᵒᵖ where
  toFun ms := .op (chainTiming ms.toList)
  map_one' := rfl
  map_mul' ms ns := by rw [FreeMonoid.toList_mul, chainTiming_append, MulOpposite.op_mul]

@[simp] theorem chainTimingHom_apply (ms : FreeMonoid M) :
    chainTimingHom ms = .op (chainTiming ms.toList) := rfl

end

end MedialForm
