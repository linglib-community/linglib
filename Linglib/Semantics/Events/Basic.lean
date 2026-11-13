module

public import Linglib.Core.Order.IntervalOrder
public import Mathlib.Order.Hom.Lattice

/-!
# Events

This file defines the temporal trace of an event domain. Neo-Davidsonian event semantics, after
Davidson and Parsons, quantifies over events as individuals of their own sort: an event domain is
a type `E`, verbs denote predicates on it, and thematic roles relate its events to their
participants. The temporal trace `τ` sends each event to its run time, as in Krifka and
Champollion, and need not be injective, since two distinct events can go on at the same time.
Where events have sums the trace preserves them, and where run times are intervals of a line an
event precedes another when its run time does, which makes precedence of events an interval
order.

## Main definitions

* `TemporalTrace`: the temporal trace of an event domain.
* `TemporalTrace.IsSupHom`: the trace preserves sums.
* `Event.τSupHom`: the trace as a homomorphism of part structures.
* `Event.Precedes`: precedence of events by their run times.

## Implementation notes

* Parthood is an order on the event domain from `Semantics/Mereology.lean`, and theories that
  never read a run time take no trace.
* Run times are `NonemptyInterval T`, and the sum of two intervals is their convex hull, so the
  sum of two events runs from the start of the earlier to the end of the later, where Krifka's
  and Champollion's sums of times keep the gap between them.
* τ is total, where Champollion lets trace functions be partial. Krifka's richness, that every
  time is the run time of some event, is the hypothesis `Function.Surjective τ`.
* Bach divides eventualities into states and non-states; here the division is a property of
  predicates (`Aspect.Dynamicity`, `Aspect.SortedProperty`), not a field of events.
* Intervals form an event domain with the identity trace, in which the studies build their
  satisfiability witnesses.

## References

* [davidson-1967]
* [parsons-1990]
* [bach-1986]
* [krifka-1998]
* [champollion-2017]
* [fishburn-1970]
-/

@[expose] public section

/-- The temporal trace of an event domain `E`, which sends each event to its run time. -/
class TemporalTrace (E : Type*) (T : outParam Type*) [LE T] where
  /-- The run time of an event. -/
  τ : E → NonemptyInterval T

/-- The run time of a sum of events is the sum of their run times ([krifka-1998] (27),
[champollion-2017] (36)). -/
class TemporalTrace.IsSupHom (E T : Type*) [SemilatticeSup E] [Lattice T] [TemporalTrace E T] :
    Prop where
  /-- The run time of a sum is the sum of the run times. -/
  τ_sup (e e' : E) : TemporalTrace.τ (e ⊔ e') = TemporalTrace.τ e ⊔ TemporalTrace.τ e'

namespace Event

export TemporalTrace (τ)
export TemporalTrace.IsSupHom (τ_sup)

/-- Each interval is an event whose run time is itself. -/
instance {T : Type*} [LE T] : TemporalTrace (NonemptyInterval T) T := ⟨id⟩

@[simp] theorem τ_nonemptyInterval {T : Type*} [LE T] (i : NonemptyInterval T) : τ i = i := rfl

instance {T : Type*} [Lattice T] : TemporalTrace.IsSupHom (NonemptyInterval T) T :=
  ⟨fun _ _ ↦ rfl⟩

/-! ### Sums -/

section SupHom

variable {E T : Type*} [SemilatticeSup E] [Lattice T] [TemporalTrace E T]
  [TemporalTrace.IsSupHom E T]

/-- The temporal trace as a homomorphism of part structures. -/
def τSupHom : SupHom E (NonemptyInterval T) := ⟨τ, τ_sup⟩

@[simp] theorem coe_τSupHom : ⇑(τSupHom : SupHom E (NonemptyInterval T)) = τ := rfl

/-- The run time of a part of an event is part of the event's run time ([krifka-1998] (33)). -/
theorem τ_mono : Monotone (τ : E → NonemptyInterval T) := OrderHomClass.mono τSupHom

end SupHom

/-! ### Precedence -/

section Precedes

variable {E T : Type*}

section Preorder

variable [Preorder T] [TemporalTrace E T]

/-- An event precedes another when its run time does ([krifka-1998] (29)). -/
def Precedes : E → E → Prop := InvImage NonemptyInterval.Precedes τ

theorem precedes_iff {e e' : E} : Precedes e e' ↔ (τ e).snd < (τ e').fst := Iff.rfl

instance [DecidableLT T] : DecidableRel (Precedes : E → E → Prop) := fun e e' ↦
  inferInstanceAs (Decidable ((τ e).snd < (τ e').fst))

end Preorder

/-- Precedence of events in a line of time is an interval order. -/
instance [LinearOrder T] [TemporalTrace E T] : IsIntervalOrder E Precedes :=
  NonemptyInterval.isIntervalOrder_precedes.invImage τ

end Precedes

end Event
