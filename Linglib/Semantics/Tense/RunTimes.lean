/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Core.Order.StrictBounds

/-!
# Run times

After Krifka, a clause denotes its run times, the set of intervals at which it holds. A stative
clause holding throughout `i` denotes `i` with all its subintervals, the principal lower set
`Set.Iic i`, an accomplishment over `i` the singleton `{i}`, and an event predicate the image of
its events under the temporal trace (`Event.TemporalTrace`). This file defines the time trace of
a set of intervals, the time points it covers, and Anscombe's universal *before*, a time of one
clause before every time of the other, the reading Anscombe gives *before ever*. The times before
every time of a clause are its strict lower bounds, the complement of its upward closure: *before*
is *not yet*, the negation of *when* or *after*. They form a lower set, so *before ever* is
anti-additive in its temporal clause. The other analyses of temporal connectives built on run
times live in their studies.

## Main definitions

* `Tense.timeTrace`: the time points that a set of intervals covers.
* `Tense.beforeEver`: Anscombe's universal *before*.

## Main statements

* `Tense.beforeEver_iff_not_subset_upperClosure`: *before* is *not yet*.
* `Tense.beforeEver_union_right`: *before ever* is anti-additive in its temporal clause.

## References

* [krifka-1989]
* [anscombe-1964]
-/

@[expose] public section

namespace Tense

section Preorder

variable {T : Type*} [Preorder T]

/-- The time trace of a set of intervals is the set of time points they contain. -/
def timeTrace (p : Set (NonemptyInterval T)) : Set T :=
  { t | ∃ i ∈ p, t ∈ i }

@[simp] theorem mem_timeTrace {p : Set (NonemptyInterval T)} {t : T} :
    t ∈ timeTrace p ↔ ∃ i ∈ p, t ∈ i := Iff.rfl

theorem timeTrace_image {α : Type*} (f : α → NonemptyInterval T) (s : Set α) :
    timeTrace (f '' s) = { t | ∃ a ∈ s, t ∈ f a } := by
  ext t; simp

@[simp] theorem timeTrace_empty : timeTrace (∅ : Set (NonemptyInterval T)) = ∅ := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_union (p q : Set (NonemptyInterval T)) :
    timeTrace (p ∪ q) = timeTrace p ∪ timeTrace q := by
  ext; simp [or_and_right, exists_or]

theorem isLeast_timeTrace_singleton (i : NonemptyInterval T) : IsLeast (timeTrace {i}) i.fst :=
  ⟨⟨i, rfl, le_rfl, i.fst_le_snd⟩, fun _ ⟨_, hj, ht⟩ ↦ (Set.mem_singleton_iff.1 hj ▸ ht).1⟩

theorem isGreatest_timeTrace_singleton (i : NonemptyInterval T) :
    IsGreatest (timeTrace {i}) i.snd :=
  ⟨⟨i, rfl, i.fst_le_snd, le_rfl⟩, fun _ ⟨_, hj, ht⟩ ↦ (Set.mem_singleton_iff.1 hj ▸ ht).2⟩

/-! ### Before ever -/

variable {A B : Set (NonemptyInterval T)}

/-- *p before ever q* holds when a time of `p` precedes every time of `q`, Anscombe's universal
rendering of *before* ([anscombe-1964] §IV–V). -/
def beforeEver (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

theorem beforeEver_iff :
    beforeEver A B ↔ (timeTrace A ∩ strictLowerBounds (timeTrace B)).Nonempty :=
  .rfl

theorem beforeEver_iff_of_isLeast {m : T} (h : IsLeast (timeTrace B) m) :
    beforeEver A B ↔ ∃ t ∈ timeTrace A, t < m :=
  ⟨fun ⟨t, ht, h'⟩ ↦ ⟨t, ht, h' m h.1⟩,
    fun ⟨t, ht, htm⟩ ↦ ⟨t, ht, fun _ h' ↦ htm.trans_le (h.2 h')⟩⟩

theorem beforeEver_singleton_right {i : NonemptyInterval T} :
    beforeEver A {i} ↔ ∃ j ∈ A, j.fst < i.fst := by
  rw [beforeEver_iff_of_isLeast (isLeast_timeTrace_singleton i)]
  exact ⟨fun ⟨_, ⟨j, hj, ht⟩, hlt⟩ ↦ ⟨j, hj, ht.1.trans_lt hlt⟩,
    fun ⟨j, hj, hlt⟩ ↦ ⟨j.fst, ⟨j, hj, le_rfl, j.fst_le_snd⟩, hlt⟩⟩

end Preorder

section PartialOrder

variable {T : Type*} [PartialOrder T]

@[simp] theorem timeTrace_singleton (i : NonemptyInterval T) :
    timeTrace {i} = (i : Set T) := by
  ext; simp [timeTrace]

@[simp] theorem timeTrace_insert (i : NonemptyInterval T) (p : Set (NonemptyInterval T)) :
    timeTrace (insert i p) = (i : Set T) ∪ timeTrace p := by
  ext; simp [timeTrace]

theorem mem_timeTrace_pure {a t : T} :
    t ∈ timeTrace {NonemptyInterval.pure a} ↔ t = a := by
  simp

@[simp] theorem timeTrace_Iic (i : NonemptyInterval T) : timeTrace (Set.Iic i) = (i : Set T) :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hj, ht⟩ ↦ NonemptyInterval.coe_subset_coe.2 hj ht,
    fun ht ↦ ⟨i, Set.mem_Iic.2 le_rfl, ht⟩⟩

theorem mem_timeTrace_Iic {i : NonemptyInterval T} {t : T} :
    t ∈ timeTrace (Set.Iic i) ↔ t ∈ i := by
  rw [timeTrace_Iic]; rfl

theorem isLeast_timeTrace_Iic (i : NonemptyInterval T) : IsLeast (timeTrace (Set.Iic i)) i.fst := by
  rw [timeTrace_Iic, ← timeTrace_singleton]
  exact isLeast_timeTrace_singleton i

theorem isGreatest_timeTrace_Iic (i : NonemptyInterval T) :
    IsGreatest (timeTrace (Set.Iic i)) i.snd := by
  rw [timeTrace_Iic, ← timeTrace_singleton]
  exact isGreatest_timeTrace_singleton i

end PartialOrder

section LinearOrder

variable {T : Type*} [LinearOrder T] {A B C : Set (NonemptyInterval T)}

/-- *Before* is *not yet*. `A` is before ever `B` exactly when some time of `A` lies outside the
upward closure of `B`'s times, the times at which `B` holds or has held. -/
theorem beforeEver_iff_not_subset_upperClosure :
    beforeEver A B ↔ ¬ timeTrace A ⊆ upperClosure (timeTrace B) := by
  rw [beforeEver_iff, strictLowerBounds_eq_compl_upperClosure, Set.inter_compl_nonempty_iff]

/-- *Before ever* is anti-additive in its temporal clause, since the times before every time of a
clause form a lower set and the lower sets of a linear order are nested. -/
theorem beforeEver_union_right : beforeEver A (B ∪ C) ↔ beforeEver A B ∧ beforeEver A C := by
  simp only [beforeEver_iff, timeTrace_union, strictLowerBounds_union]
  refine ⟨fun h ↦ ⟨h.mono (Set.inter_subset_inter_right _ Set.inter_subset_left),
    h.mono (Set.inter_subset_inter_right _ Set.inter_subset_right)⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rcases (isLowerSet_strictLowerBounds (timeTrace B)).total
    (isLowerSet_strictLowerBounds (timeTrace C)) with h | h
  · rwa [Set.inter_eq_left.2 h]
  · rwa [Set.inter_eq_right.2 h]

end LinearOrder

end Tense
