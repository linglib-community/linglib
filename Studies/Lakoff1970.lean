module

public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Data.Examples.Judgment

/-!
# Lakoff (1970): Tense and Its Relation to Participants

This file formalizes the claim of [lakoff-1970] that the choice of a tense answers to the
participants and not only to the times: a past tense may report a present state the speaker no
longer treats as salient, a present tense survives under a past matrix when its content is new
to the hearer, the present perfect asks for a relevance the speaker grants, and a present tense
stands for a future one when the event is scheduled. `Perspective` extends the library's
Reichenbach frame with the two participant dimensions, the salience of the event to the speaker
and the novelty of the content to the hearer, and each of the paper's uses is a condition on
such a frame. A use of a tense is true when the relation of the event to the speech time lies
in the cell of the tense chosen (`IsTrueUse`) and false otherwise; the paper's judgments are
predicted by true use or by a licensed false use in a synthetic form
(`predicted_iff_acceptable`), the periphrastic *used to* being confined to true pasts
(`false_use_synthetic`).

## Implementation notes

The participant dimensions are propositions on the frame, and the frame is Reichenbach's; the
evidential refinement of the frame belongs to the later literature and is not used. The false
future of the paper's (4b) and (10a), a *will* for a present state not yet real to the speaker,
would need a second direction of salience and is not represented, nor is the ban on *used to*
under sequence of tense, (11b).

## References

* [lakoff-1970]
* [reichenbach-1947]
-/

@[expose] public section

namespace Lakoff1970

open Semantics

open Tense

variable {T : Type*}

/-! ### The participant frame -/

/-- Reichenbach's frame with the two participant dimensions: whether the event is salient to
the speaker at speech time, and whether the content is new to the hearer. -/
structure Perspective (T : Type*) extends ReichenbachFrame T where
  /-- The event is psychologically salient to the speaker at speech time. -/
  Salient : Prop
  /-- The content is new to the hearer. -/
  Novel : Prop
  [decSalient : Decidable Salient]
  [decNovel : Decidable Novel]

attribute [instance] Perspective.decSalient Perspective.decNovel

/-- A use of a tense cell is true when the relation of the event to the speech time lies in
the cell: the past, present, future, and nonpast table. -/
def IsTrueUse [LinearOrder T] (cell : Finset Ordering) (f : Perspective T) : Prop :=
  compare f.eventTime f.speechTime ∈ cell

instance [LinearOrder T] (cell : Finset Ordering) (f : Perspective T) :
    Decidable (IsTrueUse cell f) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- False past (§1): a past tense on a present state the speaker no longer finds salient, as
*The animal you saw was a chipmunk* of an animal that still is one. -/
def FalsePast [DecidableEq T] (f : Perspective T) : Prop :=
  f.eventTime = f.speechTime ∧ ¬ f.Salient

instance [DecidableEq T] (f : Perspective T) : Decidable (FalsePast f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Novel present (§2): a present tense under a past matrix, licensed by content new to the
hearer, as *He discovered that the boy has blue eyes*. -/
def NovelPresent (f : Perspective T) : Prop := f.Novel ∧ f.eventTime = f.speechTime

/-- Relevant perfect (§4): the present perfect, a past event at a present reference time,
requires the event to be salient, as *Shakespeare has written thirty-seven plays* against
*Shakespeare has quarreled with Bacon*. -/
def RelevantPerfect [LinearOrder T] (f : Perspective T) : Prop :=
  f.eventPosition = .lt ∧ f.referenceTime = f.speechTime ∧ f.Salient

/-- Will-deletion (§5): a present tense for a future event the speaker treats as scheduled and
salient, as *John dies tomorrow* against *It rains Thursday*. -/
def WillDeletion [LinearOrder T] (f : Perspective T) : Prop :=
  f.speechTime < f.eventTime ∧ f.Salient

instance [LinearOrder T] (f : Perspective T) : Decidable (WillDeletion f) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem falsePast_not_trueUse [LinearOrder T] {f : Perspective T} (h : FalsePast f) :
    ¬ IsTrueUse ⟦past⟧ f := by
  simp only [IsTrueUse, compare_mem_past, h.1, lt_self_iff_false, not_false_eq_true]

theorem willDeletion_not_trueUse [LinearOrder T] {f : Perspective T} (h : WillDeletion f) :
    ¬ IsTrueUse ⟦present⟧ f := by
  simp only [IsTrueUse, compare_mem_present]; exact h.1.ne'

/-! ### Forms and judgments -/

/-- The morphology of a tense form: synthetic, as *walked*, or periphrastic, as *used to
walk*. -/
inductive Form where
  | synthetic
  | periphrastic
  deriving DecidableEq

/-- An English tense form: the cell it realizes and its morphology. -/
structure TenseForm where
  cell : Finset Ordering
  form : Form

/-- The simple past. -/
def simplePast : TenseForm := ⟨⟦past⟧, .synthetic⟩

/-- The simple present. -/
def simplePresent : TenseForm := ⟨⟦present⟧, .synthetic⟩

/-- The future with *will*. -/
def will : TenseForm := ⟨⟦future⟧, .synthetic⟩

/-- The periphrastic past *used to*. -/
def usedTo : TenseForm := ⟨⟦past⟧, .periphrastic⟩

/-- A frame at speech time zero with the event at `e`. -/
def frame (e : ℤ) (Salient : Prop) [Decidable Salient] : Perspective ℤ :=
  { speechTime := 0, perspectiveTime := 0, referenceTime := e, eventTime := e
    Salient, Novel := False }

/-- A judgment of the paper: the form used, the frame of the utterance, and the verdict. -/
structure Judgment where
  form : TenseForm
  frame : Perspective ℤ
  verdict : _root_.Judgment

/-- The paper licenses a form in a frame when its use is true, or when it is a synthetic form
in one of the false uses the paper describes: a false past, or will-deletion. -/
def Judgment.Predicted (j : Judgment) : Prop :=
  IsTrueUse j.form.cell j.frame ∨
    (j.form.form = .synthetic ∧
      ((j.form.cell = ⟦past⟧ ∧ FalsePast j.frame) ∨
        (j.form.cell = ⟦present⟧ ∧ WillDeletion j.frame)))

instance (j : Judgment) : Decidable j.Predicted := by
  unfold Judgment.Predicted; infer_instance

/-- The judgments of the paper's first and fifth sections: (4a) *the animal you saw was a
chipmunk*, of an animal still running up a tree; (6a) *the animal you saw is a chipmunk*; (8a)
*the animal you saw used to be a chipmunk*, of the same animal; (9a) *the animal the sorcerer
got hold of used to be a chipmunk, but now he's a badger*; (27a) *John will die tomorrow*, said by
his doctor; (27b) *John dies tomorrow*, said by his executioner; and (25b) *it rains Thursday,
because the weatherman predicted it*. -/
def rows : List Judgment :=
  [ ⟨simplePast, frame 0 False, .acceptable⟩
  , ⟨simplePresent, frame 0 True, .acceptable⟩
  , ⟨usedTo, frame 0 False, .ungrammatical⟩
  , ⟨usedTo, frame (-1) True, .acceptable⟩
  , ⟨will, frame 1 True, .acceptable⟩
  , ⟨simplePresent, frame 1 True, .acceptable⟩
  , ⟨simplePresent, frame 1 False, .ungrammatical⟩ ]

theorem predicted_iff_acceptable : ∀ j ∈ rows, j.Predicted ↔ j.verdict = .acceptable := by
  decide

/-- §1: an acceptable false use is in a synthetic form; the periphrastic *used to* is confined
to true pasts. -/
theorem false_use_synthetic (j : Judgment) (hj : j ∈ rows) (ha : j.verdict = .acceptable)
    (hf : ¬ IsTrueUse j.form.cell j.frame) : j.form.form = .synthetic :=
  (((predicted_iff_acceptable j hj).mpr ha).resolve_left hf).1

end Lakoff1970
