/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Aspect.Viewpoint.Basic
public import Linglib.Semantics.Situation.Exemplification

/-!
# Events in a situation semantics

An event of a kind is a situation that exemplifies a proposition: a swim by Ewan is a situation
that exemplifies the proposition that Ewan swims, and not any situation in which Ewan swims. A
sentence about an event of the kind is true in the situations that such an event is part of.

Where parthood is well-founded, a persistent proposition is true in a situation exactly when a
situation that exemplifies it is part of the situation, so existential quantification over the
events of a kind returns the proposition. A condition on the event, such as its duration, is a
condition on the exemplifying situation and not on the situation in which the sentence is true.

Where situations have run times and the run time of a part of a situation is within that of the
situation, an event that is part of a situation runs within the time of the situation: the
perfective of the event predicate holds at the time of the situation.

## Main results

* `Situation.mem_iff_exists_exemplifies_le`: a persistent proposition is true in the situations
  that a situation exemplifying it is part of.
* `Situation.perfective_of_exists_le`: an event that is part of a situation runs within the time
  of the situation.

## Implementation notes

The events of a kind are the predicate `Exemplifies p`, and no type of events is set apart from
the situations. An account on which events and situations are of different sorts relates them by a
map, as the temporal trace relates an event to its run time.

## References

* [kratzer-2023]
* [davidson-1967]
-/

@[expose] public section

namespace Situation

open Set Topology Aspect Event

variable {S : Type*} [TopologicalSpace S] [PartialOrder S] [Topology.IsLowerSet S]
  {p : Set S} {s : S}

/-- Where parthood is well-founded, a persistent proposition is true in a situation exactly when
a situation that exemplifies it is part of the situation. -/
theorem mem_iff_exists_exemplifies_le [WellFoundedLT S] (hp : IsUpperSet p) :
    s ∈ p ↔ ∃ e, Exemplifies p e ∧ e ≤ s := by
  have h := closure_setOf_exemplifies (IsLowerSet.isClosed_iff_isUpper.2 hp)
  rw [IsLowerSet.closure_eq_upperClosure] at h
  exact (Set.ext_iff.1 h s).symm.trans mem_upperClosure

/-- An event that is part of a situation runs within the time of the situation. -/
theorem perfective_of_exists_le {S T : Type*} [PartialOrder S] [LinearOrder T]
    {τ : S → NonemptyInterval T} (hτ : Monotone τ) {P : S → Prop} {s : S}
    (h : ∃ e, P e ∧ e ≤ s) : perfective τ P (τ s) :=
  let ⟨e, hP, he⟩ := h
  perfective_iff.2 ⟨e, hτ he, hP⟩

/-- Where a persistent proposition is true in a situation, the perfective of its events holds at
the time of the situation. -/
theorem perfective_exemplifies_of_mem {T : Type*} [LinearOrder T] [WellFoundedLT S]
    {τ : S → NonemptyInterval T} (hτ : Monotone τ) (hp : IsUpperSet p) (hs : s ∈ p) :
    perfective τ (Exemplifies p) (τ s) :=
  perfective_of_exists_le hτ ((mem_iff_exists_exemplifies_le hp).1 hs)

end Situation
