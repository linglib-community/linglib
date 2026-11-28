module

public import Linglib.Core.Order.IntervalOrder

/-!
# Events

Neo-Davidsonian event semantics, after Davidson and Parsons, quantifies over events as individuals
of their own sort: an event domain is a type `E`, verbs denote predicates on it, and thematic
roles relate its events to their participants. The temporal trace of an event domain is a map
`τ : E → NonemptyInterval T` that sends each event to its run time, as in Krifka and Champollion.
It need not be injective, since two distinct events can go on at the same time.

The trace is an argument of the operators that read run times, as a thematic role and a measure
are arguments of the notions stated along them, and its laws are hypotheses on it. The run time of
a part of an event is within the run time of the event, so the trace is monotone, and where
events have sums the trace preserves them. An event precedes another when its run time does, which
makes precedence of events an interval order.

## Main definitions

* `Event.Precedes`: precedence of events by their run times.

## Implementation notes

* Parthood is an order on the event domain from `Semantics/Mereology/Basic.lean`, and theories that
  never read a run time take no trace.
* Run times are `NonemptyInterval T`, and the sum of two intervals is their convex hull, so the
  sum of two events runs from the start of the earlier to the end of the later, where Krifka's
  and Champollion's sums of times keep the gap between them.
* τ is total, where Champollion lets trace functions be partial. Krifka's richness, that every
  time is the run time of some event, is the hypothesis `Function.Surjective τ`.
* Bach divides eventualities into states and non-states; here the division is a property of
  predicates (`Aspect.Dynamicity`), not a field of events.
* The intervals are an event domain under the identity trace, in which the studies build their
  satisfiability witnesses. A trace that depends on the world is the trace at each world.

## References

* [davidson-1967]
* [parsons-1990]
* [bach-1986]
* [krifka-1998]
* [champollion-2017]
* [fishburn-1970]
-/

@[expose] public section

namespace Event

variable {E T : Type*}

section Preorder

variable [Preorder T] (τ : E → NonemptyInterval T)

/-- An event precedes another along a trace when its run time does ([krifka-1998] (29)). -/
def Precedes : E → E → Prop := InvImage NonemptyInterval.Precedes τ

theorem precedes_iff {e e' : E} : Precedes τ e e' ↔ (τ e).snd < (τ e').fst := Iff.rfl

instance [DecidableLT T] : DecidableRel (Precedes τ) := fun e e' ↦
  inferInstanceAs (Decidable ((τ e).snd < (τ e').fst))

end Preorder

/-- Precedence of events in a line of time is an interval order. -/
instance [LinearOrder T] (τ : E → NonemptyInterval T) : IsIntervalOrder E (Precedes τ) :=
  NonemptyInterval.isIntervalOrder_precedes.invImage τ

end Event
