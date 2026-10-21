module

public import Linglib.Semantics.Evidential.Defs
public import Linglib.Semantics.Tense.Defs

/-!
# Tense and evidence

An evidential frame locates an assertion by three times: the time of speech, the time of the
event, and the time at which the speaker acquires the evidence for the assertion, the learning
time of Koev's account of the Bulgarian evidential and the acquisition time of Cumming's account
of tense-evidential paradigms. Evidence is downstream of the event when the event precedes or
coincides with its acquisition, so that on linear time the event stands to the acquisition in a
nonfuture position.

A constraint on a frame restricts each of its three relations to a cell of the tense partition:
the event to the acquisition, which Cumming calls the evidential perspective, the acquisition
to speech, and the event to speech, his utterance perspective. On linear time the first two
compose to a cell containing the third (`EvidentialFrame.Constraint.compare_mem_derived`).
Downstream evidence is the constraint whose first cell is the nonfuture. An evidential that
fixes when its evidence was acquired, as Korean *-te* fixes it before speech and *-ney* at
speech, carries the cell of its acquisition relative to speech (`Evidential.Timed`).

## Main definitions

* `Tense.EvidentialFrame`: the speech time, the event time and the acquisition time of an
  assertion.
* `Tense.EvidentialFrame.Downstream`: the event is no later than the acquisition of the
  evidence.
* `Tense.EvidentialFrame.Constraint`: a cell for each of the frame's three relations, with
  `Constraint.Holds` its satisfaction and `Constraint.derived` the composition of the first two.
* `Evidential.Timed`: an evidential together with the cell of its acquisition relative to
  speech.

## Implementation notes

* Downstream evidence is read temporally, the event no later than the acquisition, as in
  Koev's and Lee's accounts and Cumming's tables; Cumming's own constraint is causal.
* Every evidence-based assertion has its evidence in hand by the time of speech, so the
  nonfuture cell of acquisition relative to speech is not lexical content; only an evidential
  that fixes a finer cell is timed.

## TODO

A constraint is a qualitative constraint network in the point algebra on three named times,
and `Constraint.derived` its one path-consistency step. Networks on any number of times, with
their closure, await a consumer.

## References

* [cumming-2026]
* [koev-2017]
* [lee-2013]
* [huijsmans-2025]
-/

@[expose] public section

namespace Tense

open Semantics

/-- An evidential frame consists of the time of speech, the time of the event, and the time at
which the speaker acquires the evidence for the assertion. -/
structure EvidentialFrame (T : Type*) where
  /-- The time at which the utterance occurs. -/
  speechTime : T
  /-- The time at which the event occurs. -/
  eventTime : T
  /-- The time at which the speaker acquires the evidence for the assertion. -/
  acquisitionTime : T

namespace EvidentialFrame

variable {T : Type*}

/-- The evidence is downstream of the event when the event precedes or coincides with its
acquisition. -/
def Downstream [LE T] (f : EvidentialFrame T) : Prop := f.eventTime ≤ f.acquisitionTime

instance [LE T] [DecidableLE T] (f : EvidentialFrame T) : Decidable f.Downstream :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.acquisitionTime))

theorem downstream_iff [LinearOrder T] (f : EvidentialFrame T) :
    f.Downstream ↔ compare f.eventTime f.acquisitionTime ∈ ⟦future⟧ᶜ :=
  (compare_mem_compl_future _ _).symm

/-- A constraint on an evidential frame restricts each of its three relations to a cell of the
tense partition, `⊤` where it leaves the relation open. -/
structure Constraint where
  /-- The cell of the event relative to the acquisition of the evidence, Cumming's evidential
  perspective. -/
  eventToAcquisition : Finset Ordering := ⊤
  /-- The cell of the acquisition of the evidence relative to speech. -/
  acquisitionToSpeech : Finset Ordering := ⊤
  /-- The cell of the event relative to speech, Cumming's utterance perspective. -/
  eventToSpeech : Finset Ordering := ⊤
  deriving DecidableEq

namespace Constraint

variable [LinearOrder T] {c : Constraint} {f : EvidentialFrame T}

/-- A frame satisfies a constraint when each of its three relations lies in the constraint's
cell. -/
def Holds (c : Constraint) (f : EvidentialFrame T) : Prop :=
  compare f.eventTime f.acquisitionTime ∈ c.eventToAcquisition ∧
    compare f.acquisitionTime f.speechTime ∈ c.acquisitionToSpeech ∧
    compare f.eventTime f.speechTime ∈ c.eventToSpeech

instance (c : Constraint) (f : EvidentialFrame T) : Decidable (c.Holds f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The cell of the event relative to speech that the relations of the event to the
acquisition and of the acquisition to speech compose to. -/
def derived (c : Constraint) : Finset Ordering := comp c.eventToAcquisition c.acquisitionToSpeech

/-- At a frame where a constraint holds, the event stands to speech in the composition of the
other two cells. -/
theorem compare_mem_derived (h : c.Holds f) : compare f.eventTime f.speechTime ∈ c.derived :=
  compare_mem_comp h.1 h.2.1

/-- A constraint whose cell of the event relative to the acquisition lies within the nonfuture
requires downstream evidence. -/
theorem downstream_of_holds (hc : c.eventToAcquisition ≤ ⟦future⟧ᶜ) (h : c.Holds f) :
    f.Downstream :=
  f.downstream_iff.2 (hc h.1)

/-- A constraint whose cell of the event relative to the acquisition is a join holds exactly
when it holds with one of the two cells. -/
theorem holds_eventToAcquisition_sup {C D : Finset Ordering} :
    ({ c with eventToAcquisition := C ⊔ D } : Constraint).Holds f ↔
      ({ c with eventToAcquisition := C } : Constraint).Holds f ∨
        ({ c with eventToAcquisition := D } : Constraint).Holds f := by
  simp only [Holds, Finset.sup_eq_union, Finset.mem_union, or_and_right]

end Constraint

end EvidentialFrame

end Tense

/-- A timed evidential is an evidential that fixes when its evidence was acquired, by the cell
of the acquisition relative to speech. -/
structure Evidential.Timed extends Evidential where
  /-- The cell of the acquisition of the evidence relative to speech. -/
  acquisitionToSpeech : Finset Ordering
