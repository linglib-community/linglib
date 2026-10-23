module

public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Syntax.Clause.Basic
public import Linglib.Semantics.Modality.Basic
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Data.Examples.Kubota2026

/-!
# Kubota (2026): Outlook Management

This file formalizes Kubota's account of the Japanese *outlook markers*, adverbs and
focus particles such as *dōse* 'anyway', *nanka* 'anything like', *semete* 'at least',
*mushiro* 'rather', and *koso* 'precisely', whose secondary meaning is two-layered: a
presupposition that the prior discourse has made a counterstance salient, and an
expressive-like stance that situates the prejacent relative to that counterstance. `Outlook`
carries the three components, with the stance layer indexed by an outlook in the sense of
Coppock. Its presuppositional and expressive projections are its trivalent and
`TwoDim` images, so that denial reaches the prejacent alone ((40)–(41)), and the shifted
readings under attitude verbs ((42)) are exactly the non-rigidity of the stance layer
(`isRigid_iff`), which a pure expressive in the sense of Potts lacks
(`ofTwoDim_isRigid`).

The chapter's judgment data are the rows of `Data/Examples/Kubota2026.json`, and its
generalizations are stated over them. An outlook-marked utterance is felicitous iff the prior
move raises a counterstance, an evaluative assertion or a polar question about the prejacent's
issue rather than a general wh-question (`counterstance_requirement`, (37)–(39)). The contrary
marker *mushiro* and the confirmatory *yahari* are licensed by opposite expectations and neither
stance can be cancelled (`mushiro_yahari_expectation`, (11)–(12)). *Nanka* combines with every
modal flavor but is pejorative only under priority modality (`nanka_pejorative_iff_priority`,
(45)), while *semete* combines only with priority modals (`semete_selects_priority`, (46)),
priority modality being the deontic and bouletic flavors of Portner.

## Implementation notes

The chapter is descriptive and defers its formal analysis to Kubota and Ido, where both
layers derive from a counterstance-marker discourse function over a Farkas and Bruce
Table; `Outlook` records the chapter-level picture with the two layers as fields. Perspective
shift is modelled as outlook-relativity of the stance layer, following the chapter's remark
that outlook markers fail Potts's independence and nondisplaceability and instead
behave like locally accommodated presuppositions (Heim). Judgments the chapter marks
?? are recorded as `questionable`. The substrate's `circumstantial` flavor stands in for the
chapter's ability modals.

## TODO

* Deriving the two layers from a Table update, as Kubota and Ido do, is not attempted.

## References

* [kubota-2026]
* [kubota-ido-2025]
* [coppock-2018]
* [potts-2007b]
* [heim-1992]
* [portner-2009]
* [farkas-bruce-2010]
-/

@[expose] public section

namespace Kubota2026

open Modality (ModalFlavor)
open ConventionalImplicature (TwoDim)

/-! ### The two-layered meaning (§3) -/

/-- The meaning of an outlook-marked clause, made up of the at-issue prejacent, the presupposed
salient counterstance, and a stance layer evaluated relative to an outlook. -/
structure Outlook (W O : Type*) where
  /-- The at-issue content. -/
  prejacent : W → Prop
  /-- The presupposition that a counterstance is salient ((37)–(39)). -/
  counterstance : W → Prop
  /-- The evaluative stance, relative to an outlook. -/
  evaluation : O → W → Prop

namespace Outlook

variable {W O : Type*}

open Classical in
/-- The presuppositional projection presupposes the counterstance and asserts the prejacent. -/
noncomputable def toTrivalent (m : Outlook W O) : W → SignType :=
  {w | m.counterstance w}.indicator fun w ↦ SignType.ofProp (m.prejacent w)

/-- The expressive projection at an outlook pairs the prejacent with the stance as its
use-conditional dimension. -/
@[simps] def toTwoDim (m : Outlook W O) (o : O) : TwoDim W (W → Prop) :=
  ⟨m.prejacent, m.evaluation o⟩

/-- Negation, and so denial, leaves the counterstance presupposition in place ((40)–(41)). -/
theorem support_neg_toTrivalent (m : Outlook W O) :
    Function.support (-m.toTrivalent) = {w | m.counterstance w} := by
  ext w
  simp [toTrivalent]

/-- Negation leaves the stance layer in place at every outlook ((40)–(41)). -/
theorem toTwoDim_neg_notAtIssue (m : Outlook W O) (o : O) :
    (m.toTwoDim o).neg.notAtIssue = m.evaluation o := rfl

/-- A meaning is rigid when its stance layer does not depend on the outlook. -/
def IsRigid (m : Outlook W O) : Prop := _root_.IsRigid m.evaluation

/-- The expressive projection varies with the outlook iff the stance layer does, so perspective
shift is non-rigidity ((42)). -/
theorem isRigid_iff (m : Outlook W O) :
    m.IsRigid ↔ ∀ o o', m.toTwoDim o = m.toTwoDim o' := by
  simp only [IsRigid, _root_.IsRigid, toTwoDim, TwoDim.mk.injEq, true_and]

/-- The outlook-marked meaning of a pure expressive, whose conventional implicature is the same
at every outlook and which presupposes nothing. -/
def ofTwoDim (t : TwoDim W (W → Prop)) : Outlook W O :=
  ⟨t.atIssue, fun _ ↦ True, fun _ ↦ t.notAtIssue⟩

theorem ofTwoDim_isRigid (t : TwoDim W (W → Prop)) : (ofTwoDim (O := O) t).IsRigid :=
  isRigid_const t.notAtIssue

end Outlook

/-! ### The counterstance requirement ((37)–(39)) -/

/-- A prior move raises a counterstance when it puts the prejacent's issue at issue, as an
evaluative assertion about its topic, (37), or a polar question about it, (39) Q1, does and a
general wh-question that leaves the issue unraised, (38) and (39) Q2, does not. -/
def RaisesCounterstance (t : Clause.SentenceType) : Prop := t = .declarative ∨ t = .polar

instance : DecidablePred RaisesCounterstance := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The sentence type of the row's prior move. -/
def priorMove? (row : Datum) : Option Clause.SentenceType :=
  match row.feature? "priorMove" with
  | some "evaluativeAssertion" => some .declarative
  | some "polarQuestion" => some .polar
  | some "whQuestion" => some .constituent
  | _ => none

/-- A row is predicted felicitous iff its prior move raises a counterstance. -/
def PredictsFelicitous (row : Datum) : Prop :=
  match priorMove? row with
  | some t => RaisesCounterstance t
  | none => False

instance (row : Datum) : Decidable (PredictsFelicitous row) := by
  unfold PredictsFelicitous
  split <;> infer_instance

theorem counterstance_requirement :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "counterstance" →
      (row.judgment = .acceptable ↔ PredictsFelicitous row) := by
  decide

/-! ### Non-cancelability ((10)–(12)) -/

theorem mushiro_yahari_expectation :
    ∀ row ∈ Examples.all, row.feature? "phenomenon" = some "noncancelability" →
      row.feature? "contextExpectation" ≠ none →
      (row.feature? "marker" = some "mushiro" ↔
        row.feature? "contextExpectation" = some "unexpected") := by
  decide

/-! ### Modal interactions ((45)–(46)) -/

/-- Priority modality after [portner-2009] comprises the deontic and bouletic flavors, as against
epistemic and ability modality. -/
def IsPriority : ModalFlavor → Prop
  | .deontic | .bouletic => True
  | .epistemic | .circumstantial => False

instance : DecidablePred IsPriority := fun f ↦ by
  cases f <;> unfold IsPriority <;> infer_instance

/-- The row's modal flavor. -/
def flavor? (row : Datum) : Option ModalFlavor :=
  match row.feature? "modalFlavor" with
  | some "epistemic" => some .epistemic
  | some "deontic" => some .deontic
  | some "bouletic" => some .bouletic
  | some "circumstantial" => some .circumstantial
  | _ => none

/-- The row's modal is a priority modal. -/
def PriorityRow (row : Datum) : Prop :=
  match flavor? row with
  | some f => IsPriority f
  | none => False

instance (row : Datum) : Decidable (PriorityRow row) := by
  unfold PriorityRow
  split <;> infer_instance

/-- *Nanka* combines with modals of every flavor ((45)). -/
theorem nanka_unrestricted :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "nanka" →
      row.feature? "phenomenon" = some "modalInteraction" → row.judgment = .acceptable := by
  decide

/-- The negative implication of *nanka* is pejorative under priority modals and comparatively
neutral under epistemic and ability modals ((45)). -/
theorem nanka_pejorative_iff_priority :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "nanka" →
      row.feature? "phenomenon" = some "modalInteraction" →
      (row.feature? "evaluation" = some "pejorative" ↔ PriorityRow row) := by
  decide

/-- *Semete* combines with priority modals and not with epistemic or ability modals ((46)). -/
theorem semete_selects_priority :
    ∀ row ∈ Examples.all, row.feature? "marker" = some "semete" →
      row.feature? "phenomenon" = some "modalInteraction" →
      (row.judgment = .acceptable ↔ PriorityRow row) := by
  decide

end Kubota2026
