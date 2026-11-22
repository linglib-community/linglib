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
* `MedialForm`: the class of a language's medial forms, with `MedialForm.HasSR` and
  `MedialForm.SSUnmarked` for its switch-reference system.

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
  sr : M → Option SwitchReference
  /-- The form carries subject cross-referencing. -/
  IndexesSubject : M → Prop
  [decidableIndexesSubject : DecidablePred IndexesSubject]

namespace MedialForm

attribute [instance_reducible] decidableIndexesSubject
attribute [instance] decidableIndexesSubject

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

end MedialForm
