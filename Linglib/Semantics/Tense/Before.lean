/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.AntiAdditive
public import Linglib.Core.Order.StrictBounds
public import Linglib.Logic.Temporal.IntervalProperty

/-!
# Before ever

A clause holds at some intervals of time, an interval property (`Logic/Temporal/IntervalProperty`):
a stative clause holding throughout `i` has the property `(· ≤ i)`, an accomplishment over `i`
the property `(· = i)`, and an event predicate the run times of its events ([krifka-1989]). One
clause is before ever another, `Tense.beforeEver`, when a time of the first precedes every time
of the second, the universal rendering of *before* in [anscombe-1964]. The times before every
time of a clause are the strict lower bounds of its time trace, so *before* is *not yet*, and
they form a lower set, so *before ever* is anti-additive in its temporal clause.

## Main definitions

* `Tense.beforeEver`: a time of the first clause precedes every time of the second.

## Main results

* `Tense.beforeEver_iff_not_subset_upperClosure`: *before* is *not yet*.
* `Tense.isAntiAdditive_beforeEver`: *before ever* is anti-additive in its temporal clause.

## References

* [krifka-1989]
* [anscombe-1964]
-/

@[expose] public section

namespace Tense

open Temporal

section Preorder

variable {T : Type*} [Preorder T] {A B : NonemptyInterval T → Prop}

/-- *p before ever q* holds when a time of `p` precedes every time of `q`, Anscombe's universal
rendering of *before* ([anscombe-1964] §IV–V). -/
def beforeEver (A B : NonemptyInterval T → Prop) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

theorem beforeEver_iff :
    beforeEver A B ↔ (timeTrace A ∩ strictLowerBounds (timeTrace B)).Nonempty :=
  .rfl

theorem beforeEver.exists_notMem (h : beforeEver A B) : ∃ t ∈ timeTrace A, t ∉ timeTrace B :=
  let ⟨t, hA, ht⟩ := h
  ⟨t, hA, fun hB ↦ lt_irrefl t (ht t hB)⟩

theorem beforeEver.anti_right {B' : NonemptyInterval T → Prop} (h : beforeEver A B)
    (hB : timeTrace B' ⊆ timeTrace B) : beforeEver A B' :=
  let ⟨t, ht, hall⟩ := h
  ⟨t, ht, fun t' ht' ↦ hall t' (hB ht')⟩

theorem not_beforeEver_top : ¬ beforeEver A ⊤ := fun h ↦
  let ⟨_, _, ht⟩ := h.exists_notMem
  ht (timeTrace_top (T := T) ▸ trivial)

theorem beforeEver_iff_of_isLeast {m : T} (h : IsLeast (timeTrace B) m) :
    beforeEver A B ↔ ∃ t ∈ timeTrace A, t < m := by
  rw [beforeEver_iff, h.strictLowerBounds_eq]
  rfl

theorem beforeEver_eq_right {i : NonemptyInterval T} :
    beforeEver A (· = i) ↔ ∃ j, A j ∧ j.fst < i.fst := by
  rw [beforeEver_iff_of_isLeast (isLeast_timeTrace_eq i)]
  exact ⟨fun ⟨_, ⟨j, hj, ht⟩, hlt⟩ ↦ ⟨j, hj, ht.1.trans_lt hlt⟩,
    fun ⟨j, hj, hlt⟩ ↦ ⟨j.fst, ⟨j, hj, le_rfl, j.fst_le_snd⟩, hlt⟩⟩

end Preorder

variable {T : Type*} [LinearOrder T] {A B C : NonemptyInterval T → Prop}

/-- *Before* is *not yet*. `A` is before ever `B` exactly when some time of `A` lies outside the
upward closure of `B`'s times, the times at which `B` holds or has held. -/
theorem beforeEver_iff_not_subset_upperClosure :
    beforeEver A B ↔ ¬ timeTrace A ⊆ upperClosure (timeTrace B) := by
  rw [beforeEver_iff, strictLowerBounds_eq_compl_upperClosure, Set.inter_compl_nonempty_iff]

theorem beforeEver_sup_right : beforeEver A (B ⊔ C) ↔ beforeEver A B ∧ beforeEver A C := by
  simp only [beforeEver_iff, timeTrace_sup, strictLowerBounds_union]
  refine ⟨fun h ↦ ⟨h.mono (Set.inter_subset_inter_right _ Set.inter_subset_left),
    h.mono (Set.inter_subset_inter_right _ Set.inter_subset_right)⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rcases (isLowerSet_strictLowerBounds (timeTrace B)).total
    (isLowerSet_strictLowerBounds (timeTrace C)) with h | h
  · rwa [Set.inter_eq_left.2 h]
  · rwa [Set.inter_eq_right.2 h]

/-- *Before ever* is anti-additive in its temporal clause, since the times before every time of a
clause form a lower set and the lower sets of a linear order are nested. -/
theorem isAntiAdditive_beforeEver (A : NonemptyInterval T → Prop) :
    IsAntiAdditive (beforeEver A) :=
  fun _ _ ↦ propext beforeEver_sup_right

end Tense
