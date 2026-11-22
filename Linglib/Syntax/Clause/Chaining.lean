module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Clause chaining

A clause chain is a sequence of medial clauses, dependent and morphologically reduced, closed by
one final clause that supplies tense, mood and often agreement for the whole chain; Foley and Van
Valin and Longacre take it as the prototypical cosubordinate combination of clauses, dependent but
not embedded. In many chaining languages a medial form marks switch-reference, whether the subject
of its clause is that of the clause it is evaluated against. A language's medial forms are an
instance of `MedialForm`, which records for each form the switch-reference value it marks and
whether it indexes the subject of its clause.

## Main definitions

* `SwitchReference`: same subject or different subject.
* `MedialForm`: the class of a language's medial forms, with
  `MedialForm.MarksSwitchReference` and `MedialForm.IndexesSubjectIffDS` for its switch-reference
  system.

## References

* [sarvasy-aikhenvald-2025]
* [foley-r-d-van-valin-1984]
* [longacre-2007]
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

/-- A language's medial forms: the switch-reference value each marks and whether it indexes the
subject of its clause. -/
class MedialForm (M : Type*) where
  /-- The switch-reference value a form marks, `none` for a form neutral to it. -/
  switchReference : M → Option SwitchReference
  /-- The form carries subject cross-referencing. -/
  IndexesSubject : M → Prop
  [decidableIndexesSubject : DecidablePred IndexesSubject]

namespace MedialForm

attribute [instance_reducible] decidableIndexesSubject
attribute [instance] decidableIndexesSubject

variable (M : Type*) [MedialForm M]

/-- Some medial form marks switch-reference. -/
def MarksSwitchReference : Prop := ∃ m : M, switchReference m ≠ none

/-- A form that marks switch-reference indexes the subject exactly when it marks a different
subject, the dominant pattern of switch-reference marking. -/
def IndexesSubjectIffDS : Prop :=
  ∀ m : M, ∀ s, switchReference m = some s → (IndexesSubject m ↔ s = .ds)

variable [Fintype M]

instance : Decidable (MarksSwitchReference M) :=
  inferInstanceAs (Decidable (∃ m : M, switchReference m ≠ none))

instance : Decidable (IndexesSubjectIffDS M) :=
  inferInstanceAs (Decidable (∀ m : M, ∀ s, switchReference m = some s → _))

end MedialForm
