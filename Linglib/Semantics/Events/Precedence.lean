module

public import Linglib.Core.Order.AntiAdditive
public import Linglib.Semantics.Events.Basic
public import Linglib.Semantics.Mereology

/-!
# Temporal precedence on a part structure of events

This file defines temporal precedence on a part structure of events as an interval order in
which a sum of events precedes an event exactly when both summands do, and follows one exactly
when both do. Parts of an event that precedes another then precede it too, so no event precedes
one it overlaps. Krifka derives these facts from the temporal trace of an event structure, and
precedence by the run times of a trace that preserves sums is such a relation.

## Main definitions

* `IsTemporalPrecedence`: an interval order on events that is anti-additive in each argument.

## Main statements

* `IsTemporalPrecedence.not_of_overlap`: overlapping events do not precede each other.
* `Event.isTemporalPrecedence_precedes`: precedence by the run times of a sum-preserving trace
  is a temporal precedence.

## Implementation notes

The relation is stated without run times, so it applies to event structures given by their
precedence alone, as in the reconstructions of times from events.

## TODO

* An interval order is precedence of run times in some line of time, and a precedence on a part
  structure is so under a trace that preserves sums: the converse of
  `Event.isTemporalPrecedence_precedes`.

## References

* [krifka-1998]
* [fishburn-1970]
-/

@[expose] public section

open Mereology

/-- A temporal precedence on a part structure of events: an interval order in which a sum
precedes an event exactly when its summands do, and follows one exactly when its summands do. -/
class IsTemporalPrecedence (E : Type*) [SemilatticeSup E] (r : E → E → Prop) : Prop
    extends IsIntervalOrder E r where
  /-- A sum precedes an event exactly when its summands do. -/
  left (c : E) : IsAntiAdditive (r · c)
  /-- A sum follows an event exactly when its summands do. -/
  right (c : E) : IsAntiAdditive (r c ·)

namespace IsTemporalPrecedence

variable {E : Type*} [SemilatticeSup E] {r : E → E → Prop} [IsTemporalPrecedence E r] {a b c : E}

theorem sup_left_iff : r (a ⊔ b) c ↔ r a c ∧ r b c := (left (r := r) c a b).to_iff

theorem sup_right_iff : r c (a ⊔ b) ↔ r c a ∧ r c b := (right (r := r) c a b).to_iff

/-- A part of an event that precedes `c` precedes `c`. -/
theorem mono_left (hab : a ≤ b) (hb : r b c) : r a c := by
  rw [← sup_eq_right.2 hab] at hb
  exact (sup_left_iff.1 hb).1

/-- An event that precedes `b` precedes each part of `b`. -/
theorem mono_right (hab : a ≤ b) (hb : r c b) : r c a := by
  rw [← sup_eq_right.2 hab] at hb
  exact (sup_right_iff.1 hb).1

/-- Overlapping events do not precede each other ([krifka-1998] (35)). -/
theorem not_of_overlap (hab : Overlap a b) : ¬ r a b := fun hr ↦
  let ⟨z, _, hza, hzb⟩ := hab
  irrefl_of r z (mono_right hzb (mono_left hza hr))

end IsTemporalPrecedence

/-- Under a trace that preserves sums, precedence by run times is a temporal precedence on the
part structure of events. -/
instance Event.isTemporalPrecedence_precedes {E T : Type*} [LinearOrder T] [SemilatticeSup E]
    [Event.TemporalTrace E (NonemptyInterval T)]
    [Event.TemporalTrace.IsSupHom E (NonemptyInterval T)] :
    IsTemporalPrecedence E (Event.Precedes : E → E → Prop) where
  left c a b := propext <| by
    simp only [Event.precedes_iff, Event.τ_sup]
    exact max_lt_iff
  right c a b := propext <| by
    simp only [Event.precedes_iff, Event.τ_sup]
    exact lt_min_iff
