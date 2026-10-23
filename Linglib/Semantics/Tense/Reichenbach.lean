module

public import Linglib.Semantics.Tense.Defs

/-!
# Reichenbach's temporal frame

A Reichenbach frame locates a clause by four times. Reichenbach's three are points: the point of
speech S, the point of reference R and the point of the event E. Kiparsky adds the perspective
time P, the origin of temporal deixis, which includes S in the simple case and departs from it in
flashbacks and historical presents. A frame has two positions, of R relative to P and of E
relative to R (`ReichenbachFrame.referencePosition`, `ReichenbachFrame.eventPosition`).
Reichenbach names the first past, present or future and the second anterior, simple or posterior;
Kiparsky calls the first tense and the second aspect, the perfect placing E before R and the
prospective after it. A tense cell of `Semantics/Tense/Defs.lean` constrains the first position,
as in `f.referencePosition ∈ ⟦past⟧`. Kiparsky links E to P only through R, so their comparison
is one that the composition of the two positions allows. Reichenbach's own frames are those whose
perspective is the point of speech (`ReichenbachFrame.root`).

## Main definitions

* `Tense.ReichenbachFrame`: the four times of a clause.
* `Tense.ReichenbachFrame.root`: Reichenbach's frame, the perspective at the point of speech.
* `Tense.ReichenbachFrame.referencePosition`, `Tense.ReichenbachFrame.eventPosition`: R relative
  to P and E relative to R.

## Main results

* `Tense.ReichenbachFrame.compare_eventTime_perspectiveTime_mem`: E stands to P as the
  composition of the event position with the reference position allows.

## Implementation notes

The times are points of a linear order, as Reichenbach's are. Kiparsky takes them to be intervals
with points as the degenerate case, so his default inclusions of P and E in R become equalities
here, and the duration of an event that reaches up to the point of speech is not represented;
his interval account of the perfect is `Studies/Kiparsky2002.lean`, and interval aspect is
`Semantics/Aspect/Viewpoint.lean`. A frame records times, not morphology: that a sentence's tense
form yields a frame with a given position is a study's claim.

## References

* [reichenbach-1947]
* [kiparsky-2002]
-/

@[expose] public section

namespace Tense

/-- A Reichenbach frame consists of the point of speech, the perspective time, the point of
reference and the point of the event of a clause. -/
structure ReichenbachFrame (T : Type*) where
  /-- The point of speech S is when the utterance occurs. -/
  speechTime : T
  /-- The perspective time P is the origin of temporal deixis. -/
  perspectiveTime : T
  /-- The point of reference R is the time to which adverbs refer. -/
  referenceTime : T
  /-- The point of the event E is when the event occurs. -/
  eventTime : T

namespace ReichenbachFrame

variable {T : Type*}

/-- Reichenbach's frame of the points `s`, `r` and `e` takes the point of speech as the
perspective. -/
@[simps] def root (s r e : T) : ReichenbachFrame T := ⟨s, s, r, e⟩

variable [LinearOrder T] (f : ReichenbachFrame T)

/-- The reference position of a frame is how its point of reference stands to its perspective
time, which the words past, present and future indicate. -/
def referencePosition : Ordering := compare f.referenceTime f.perspectiveTime

/-- The event position of a frame is how its point of the event stands to its point of reference,
which the words anterior, simple and posterior indicate. -/
def eventPosition : Ordering := compare f.eventTime f.referenceTime

@[simp] theorem referencePosition_eq_lt :
    f.referencePosition = .lt ↔ f.referenceTime < f.perspectiveTime :=
  compare_lt_iff_lt

@[simp] theorem referencePosition_eq_eq :
    f.referencePosition = .eq ↔ f.referenceTime = f.perspectiveTime :=
  compare_eq_iff_eq

@[simp] theorem referencePosition_eq_gt :
    f.referencePosition = .gt ↔ f.perspectiveTime < f.referenceTime :=
  compare_gt_iff_gt

@[simp] theorem eventPosition_eq_lt : f.eventPosition = .lt ↔ f.eventTime < f.referenceTime :=
  compare_lt_iff_lt

@[simp] theorem eventPosition_eq_eq : f.eventPosition = .eq ↔ f.eventTime = f.referenceTime :=
  compare_eq_iff_eq

@[simp] theorem eventPosition_eq_gt : f.eventPosition = .gt ↔ f.referenceTime < f.eventTime :=
  compare_gt_iff_gt

/-- The point of the event stands to the perspective time as the composition of the event
position with the reference position allows. -/
theorem compare_eventTime_perspectiveTime_mem :
    compare f.eventTime f.perspectiveTime ∈ f.eventPosition.comp f.referencePosition :=
  Ordering.compare_mem_comp _ _ _

end ReichenbachFrame

end Tense
