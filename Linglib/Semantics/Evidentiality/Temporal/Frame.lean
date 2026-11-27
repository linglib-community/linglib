module

public import Linglib.Semantics.Evidentiality.Evidence
public import Linglib.Semantics.Tense.Defs

/-!
# Evidential frames

An evidential frame locates an assertion by three times: the time of speech, the time of the
event, and the time at which the speaker acquires the evidence for the assertion, the learning
time of Koev's account of the Bulgarian evidential and the acquisition time of Cumming's account
of tense-evidential paradigms. Evidence is downstream of the event when the event precedes or
coincides with its acquisition, so that on linear time the event stands to the acquisition in a
nonfuture position.

A constraint on a frame restricts each of its three relations to a cell of the tense partition:
the event to the acquisition, which Cumming calls the evidential perspective, the acquisition
to speech, and the event to speech, his utterance perspective. On linear time the first two
compose to a cell containing the third (`Evidential.Frame.Constraint.compare_mem_derived`).
Downstream evidence is the constraint whose first cell is the nonfuture. An evidential that
fixes when its evidence was acquired, as Korean *-te* fixes it before speech and *-ney* at
speech, carries the cell of its acquisition relative to speech (`Evidential.Timed`).

A dated evidence relation `ev : Parameter → Set W → T → Set W` gives the worlds `ev π p t` in
which the speaker acquires evidence from `π` for `p` at the time `t`; forgetting the time gives
the evidence relation `Evidential.undated ev`. The evidential proposition of a timed evidential
uttered at `s` requires evidence from a source it covers acquired at a time in its cell relative
to `s` (`Evidential.Timed.evidence`). It entails the evidential proposition of the underlying
evidential (`Evidential.Timed.evidence_subset`) and equals it when the cell is `⊤`.

## Main definitions

* `Evidential.Frame`: the speech time, the event time and the acquisition time of an
  assertion.
* `Evidential.Frame.Downstream`: the event is no later than the acquisition of the
  evidence.
* `Evidential.Frame.Constraint`: a cell for each of the frame's three relations, with
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

namespace Evidential

open Tense

open scoped Denotes

/-- An evidential frame consists of the time of speech, the time of the event, and the time at
which the speaker acquires the evidence for the assertion. -/
structure Frame (T : Type*) where
  /-- The time at which the utterance occurs. -/
  speechTime : T
  /-- The time at which the event occurs. -/
  eventTime : T
  /-- The time at which the speaker acquires the evidence for the assertion. -/
  acquisitionTime : T

namespace Frame

variable {T : Type*}

/-- The evidence is downstream of the event when the event precedes or coincides with its
acquisition. -/
def Downstream [LE T] (f : Frame T) : Prop := f.eventTime ≤ f.acquisitionTime

instance [LE T] [DecidableLE T] (f : Frame T) : Decidable f.Downstream :=
  inferInstanceAs (Decidable (f.eventTime ≤ f.acquisitionTime))

theorem downstream_iff [LinearOrder T] (f : Frame T) :
    f.Downstream ↔ compare f.eventTime f.acquisitionTime ∈ nonfuture :=
  (compare_mem_nonfuture _ _).symm

/-- A constraint on an evidential frame restricts each of its three relations to a cell of the
tense partition, `⊤` where it leaves the relation open. -/
structure Constraint where
  /-- The cell of the event relative to the acquisition of the evidence, Cumming's evidential
  perspective. -/
  eventToAcquisition : PointAlgebra := ⊤
  /-- The cell of the acquisition of the evidence relative to speech. -/
  acquisitionToSpeech : PointAlgebra := ⊤
  /-- The cell of the event relative to speech, Cumming's utterance perspective. -/
  eventToSpeech : PointAlgebra := ⊤
  deriving DecidableEq

namespace Constraint

variable [LinearOrder T] {c : Constraint} {f : Frame T}

/-- A frame satisfies a constraint when each of its three relations lies in the constraint's
cell. -/
def Holds (c : Constraint) (f : Frame T) : Prop :=
  compare f.eventTime f.acquisitionTime ∈ c.eventToAcquisition ∧
    compare f.acquisitionTime f.speechTime ∈ c.acquisitionToSpeech ∧
    compare f.eventTime f.speechTime ∈ c.eventToSpeech

instance (c : Constraint) (f : Frame T) : Decidable (c.Holds f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The cell of the event relative to speech that the relations of the event to the
acquisition and of the acquisition to speech compose to. -/
def derived (c : Constraint) : PointAlgebra := c.acquisitionToSpeech * c.eventToAcquisition

theorem compare_mem_derived (h : c.Holds f) : compare f.eventTime f.speechTime ∈ c.derived :=
  PointAlgebra.compare_mem_mul h.1 h.2.1

theorem downstream_of_holds (hc : c.eventToAcquisition ≤ nonfuture) (h : c.Holds f) :
    f.Downstream :=
  f.downstream_iff.2 (hc h.1)

theorem holds_eventToAcquisition_sup {C D : PointAlgebra} :
    ({ c with eventToAcquisition := C ⊔ D } : Constraint).Holds f ↔
      ({ c with eventToAcquisition := C } : Constraint).Holds f ∨
        ({ c with eventToAcquisition := D } : Constraint).Holds f := by
  simp only [Holds, PointAlgebra.mem_sup, or_and_right]

end Constraint

end Frame

end Evidential

/-- A timed evidential is an evidential that fixes when its evidence was acquired, by the cell
of the acquisition relative to speech. -/
structure Evidential.Timed extends Evidential where
  /-- The cell of the acquisition of the evidence relative to speech. -/
  acquisitionToSpeech : PointAlgebra

namespace Evidential

variable {W T : Type*} {ev : Parameter → Set W → T → Set W} {p : Set W} {w : W}

/-! ### Dated evidence -/

/-- The evidence relation of a dated one, forgetting when the evidence is acquired. -/
def undated (ev : Parameter → Set W → T → Set W) : Parameter → Set W → Set W :=
  fun π p ↦ ⋃ t, ev π p t

@[simp] theorem mem_undated {π : Parameter} : w ∈ undated ev π p ↔ ∃ t, w ∈ ev π p t :=
  Set.mem_iUnion

variable [LinearOrder T] {e : Timed} {s : T}

/-- The evidential proposition of a timed evidential uttered at `s`: the speaker has evidence
for `p` from a source it covers, acquired at a time in its cell relative to `s`. -/
def Timed.evidence (e : Timed) (ev : Parameter → Set W → T → Set W) (s : T) (p : Set W) :
    Set W :=
  {w | ∃ π ∈ e.covers, ∃ t, w ∈ ev π p t ∧ compare t s ∈ e.acquisitionToSpeech}

@[simp] theorem Timed.mem_evidence :
    w ∈ e.evidence ev s p ↔
      ∃ π ∈ e.covers, ∃ t, w ∈ ev π p t ∧ compare t s ∈ e.acquisitionToSpeech := Iff.rfl

/-- A timed evidential requires at least the evidence its sources require. -/
theorem Timed.evidence_subset : e.evidence ev s p ⊆ e.toEvidential.evidence (undated ev) p :=
  fun _ ⟨π, hπ, t, ht, _⟩ ↦ ⟨π, hπ, mem_undated.2 ⟨t, ht⟩⟩

/-- An evidential that leaves the time of acquisition open requires only the evidence its
sources require. -/
theorem Timed.evidence_eq_of_eq_top (h : e.acquisitionToSpeech = ⊤) :
    e.evidence ev s p = e.toEvidential.evidence (undated ev) p := by
  ext w
  simp [h]

/-- The evidential proposition of a timed evidential holds where the frame of some acquisition
of evidence from a source it covers satisfies the constraint of its cell. -/
theorem Timed.mem_evidence_iff_holds (x : T) :
    w ∈ e.evidence ev s p ↔ ∃ π ∈ e.covers, ∃ t, w ∈ ev π p t ∧
      ({ acquisitionToSpeech := e.acquisitionToSpeech } : Frame.Constraint).Holds
        { speechTime := s, eventTime := x, acquisitionTime := t } := by
  simp [Frame.Constraint.Holds]

end Evidential
