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

* `Event.TemporalTrace`: the temporal trace of an event domain.
* `Event.TemporalTrace.IsSupHom`: the trace preserves sums.
* `Event.τSupHom`: the trace as a homomorphism of part structures.
* `Event.Precedes`: precedence of events by their run times.

## Implementation notes

* The type of run times is a parameter: intervals of a linear order for the aspectual operators,
  and any part structure of times for mereological results. An event domain has one trace, so
  the type of its run times is an `outParam`.
* The sum of two intervals is their convex hull, so under an interval-valued trace the sum of two
  events runs from the start of the earlier to the end of the later, where Krifka's and
  Champollion's sums of times keep the gap between them.
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

namespace Event

/-- The temporal trace of an event domain `E`, which sends each event to its run time, of
type `I`. -/
class TemporalTrace (E : Type*) (I : outParam Type*) where
  /-- The run time of an event. -/
  τ : E → I

export TemporalTrace (τ)

/-- Each interval is an event whose run time is itself. -/
instance {T : Type*} [LE T] : TemporalTrace (NonemptyInterval T) (NonemptyInterval T) := ⟨id⟩

@[simp] theorem τ_nonemptyInterval {T : Type*} [LE T] (i : NonemptyInterval T) : τ i = i := rfl

/-! ### Sums -/

/-- The run time of a sum of events is the sum of their run times ([krifka-1998] (27),
[champollion-2017] (36)). -/
class TemporalTrace.IsSupHom (E I : Type*) [SemilatticeSup E] [SemilatticeSup I]
    [TemporalTrace E I] : Prop where
  /-- The run time of a sum is the sum of the run times. -/
  τ_sup (e e' : E) : τ (e ⊔ e') = τ e ⊔ τ e'

export TemporalTrace.IsSupHom (τ_sup)

instance {T : Type*} [Lattice T] :
    TemporalTrace.IsSupHom (NonemptyInterval T) (NonemptyInterval T) := ⟨fun _ _ ↦ rfl⟩

section SupHom

variable {E I : Type*} [SemilatticeSup E] [SemilatticeSup I] [TemporalTrace E I]
  [TemporalTrace.IsSupHom E I]

/-- The temporal trace as a homomorphism of part structures. -/
def τSupHom : SupHom E I := ⟨τ, τ_sup⟩

@[simp] theorem coe_τSupHom : ⇑(τSupHom : SupHom E I) = τ := rfl

/-- The run time of a part of an event is part of the event's run time ([krifka-1998] (33)). -/
theorem τ_mono : Monotone (τ : E → I) := OrderHomClass.mono τSupHom

end SupHom

/-! ### Precedence -/

section Precedes

variable {E T : Type*}

section Preorder

variable [Preorder T] [TemporalTrace E (NonemptyInterval T)]

/-- An event precedes another when its run time does ([krifka-1998] (29)). -/
def Precedes : E → E → Prop := InvImage NonemptyInterval.Precedes τ

theorem precedes_iff {e e' : E} : Precedes e e' ↔ (τ e).snd < (τ e').fst := Iff.rfl

instance [DecidableLT T] : DecidableRel (Precedes : E → E → Prop) := fun e e' ↦
  inferInstanceAs (Decidable ((τ e).snd < (τ e').fst))

end Preorder

/-- Precedence of events in a line of time is an interval order. -/
instance [LinearOrder T] [TemporalTrace E (NonemptyInterval T)] : IsIntervalOrder E Precedes :=
  NonemptyInterval.isIntervalOrder_precedes.invImage τ

end Precedes

end Event
