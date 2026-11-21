module

public import Linglib.Semantics.Aspect.Viewpoint

/-!
# Instantiation of sorted properties

A sorted property is a property of events, of states, or of times. This file defines the relation
`At t w Q`, which says that the sorted property `Q` is instantiated in the world `w` at the
interval `t`: for a property `P` of events, some event `e` with `P w e` has its run time within
`t`; for a property of states, some state `e` with `P w e` has a run time overlapping `t`; and a
property of times is instantiated at `t` when it holds of `t`. The choice of inclusion for events
and overlap for states is that of the discourse representation analyses of Kamp and Rohrer, of
Partee, and of Kamp and Reyle.

Instantiation of a property of events or states is monotone in the interval, `At.mono`, and
fails at the null interval. At the ray from `t` it says that an event starts no earlier than `t`
or that a state lasts until `t`, and at the point `t` that an event occurs exactly at `t` or that
a state holds at `t`. On a bounded interval `i`, a property of events is instantiated when `i`
belongs to the perfective `Aspect.perfective`, and a property of states when a state's run time
overlaps `i`.

## Implementation notes

* Reference intervals are `Interval (WithTop T)`, so that an interval may run to the end of time,
  as `Interval.Ici ↑t` does, and the intersection of two intervals may be the null interval `⊥`.
* The run time of an eventuality is `Event.τ e`, the same in every world; the source's temporal
  trace takes the world as a second argument.

## References

* [C. Condoravdi, *Temporal Interpretation of Modals* (2002)][condoravdi-2002]
* [H. Kamp and C. Rohrer, *Tense in Texts* (1983)][kamp-rohrer-1983]
* [B. Partee, *Nominal and Temporal Anaphora* (1984)][partee-1984]
* [H. Kamp and U. Reyle, *From Discourse to Logic* (1993)][kamp-reyle-1993]
-/

@[expose] public section

namespace Aspect

open Event (τ)

variable {W E T : Type*} [LinearOrder T]

/-- A sorted property is a property of events, of states, or of times. -/
inductive SortedProperty (W E T : Type*) [LinearOrder T]
  | eventive (P : W → E → Prop)
  | stative (P : W → E → Prop)
  | temporal (P : W → Interval (WithTop T) → Prop)

/-- A sorted property is a property of eventualities when it is not a property of times. -/
def SortedProperty.IsEventuality : SortedProperty W E T → Prop
  | .temporal _ => False
  | _ => True

variable [TemporalTrace E T]

/-- `At t w Q` says that the property `Q` is instantiated in `w` at the interval `t`, by inclusion
of the runtime for events, overlap for states, and application for properties of times. -/
def At (t : Interval (WithTop T)) (w : W) : SortedProperty W E T → Prop
  | .eventive P => ∃ e, P w e ∧ ↑(τ e).withTop ≤ t
  | .stative P => ∃ e, P w e ∧ ¬ Disjoint (↑(τ e).withTop) t
  | .temporal P => P w t

variable {P : W → E → Prop} {Q : SortedProperty W E T} {r r' : Interval (WithTop T)} {w : W}

theorem exists_mem_of_at (hQ : Q.IsEventuality) (h : At r w Q) : ∃ x, x ∈ r := by
  cases Q with
  | eventive R => obtain ⟨e, -, hle⟩ := h; exact ⟨_, (Interval.coe_le_iff.1 hle).1⟩
  | stative R =>
    obtain ⟨e, -, hd⟩ := h
    obtain ⟨x, -, hx⟩ := Interval.not_disjoint_iff.1 hd
    exact ⟨x, hx⟩
  | temporal R => exact hQ.elim

theorem not_at_bot (hQ : Q.IsEventuality) : ¬ At ⊥ w Q :=
  fun h ↦ let ⟨_, hx⟩ := exists_mem_of_at hQ h; Interval.notMem_bot hx

/-- Instantiation of an eventuality is monotone in the interval. -/
theorem At.mono (hQ : Q.IsEventuality) (h : r ≤ r') (hr : At r w Q) : At r' w Q := by
  cases Q with
  | eventive R => obtain ⟨e, he, hle⟩ := hr; exact ⟨e, he, le_trans hle h⟩
  | stative R =>
    obtain ⟨e, he, hd⟩ := hr
    exact ⟨e, he, fun hd' ↦ hd (hd'.mono_right h)⟩
  | temporal R => exact hQ.elim

/-- An event is instantiated at the ray from `t` when it starts no earlier than `t`. -/
@[simp] theorem at_Ici_eventive_iff {t : T} :
    At (Interval.Ici ↑t) w (.eventive P) ↔ ∃ e, P w e ∧ t ≤ (τ e).fst := by
  simp [At, Interval.withTop_le_Ici]

/-- A state is instantiated at the ray from `t` when it persists at or past `t`. -/
@[simp] theorem at_Ici_stative_iff {t : T} :
    At (Interval.Ici ↑t) w (.stative P) ↔ ∃ e, P w e ∧ t ≤ (τ e).snd := by
  simp [At, Interval.not_disjoint_withTop_Ici]

/-- On a bounded interval, eventive instantiation is the perfective viewpoint. -/
theorem at_eventive_withTop_iff_perfective {i : NonemptyInterval T} :
    At ↑i.withTop w (.eventive P) ↔ perfective (P w) i := by
  simp [At, perfective_iff, and_comm]

/-- On a bounded interval, a state is instantiated when its run time overlaps the interval. -/
theorem at_stative_withTop_iff {i : NonemptyInterval T} :
    At ↑i.withTop w (.stative P) ↔ ∃ e, P w e ∧ (τ e).Overlaps i := by
  simp [At, Interval.not_disjoint_coe_coe, NonemptyInterval.Overlaps]

theorem at_stative_withTop_of_unbounded {i : NonemptyInterval T} (h : unbounded (P w) i) :
    At ↑i.withTop w (.stative P) :=
  let ⟨e, hle, he⟩ := unbounded_iff.1 h
  at_stative_withTop_iff.2 ⟨e, he, (NonemptyInterval.overlaps_of_le hle).symm⟩

/-- An event is instantiated at the point `t` when its run time is `t`. -/
@[simp] theorem at_pure_eventive_iff {t : T} :
    At (Interval.pure ↑t) w (.eventive P) ↔ ∃ e, P w e ∧ τ e = .pure t :=
  (at_eventive_withTop_iff_perfective (i := .pure t)).trans <|
    perfective_pure_iff.trans <| exists_congr fun _ ↦ and_comm

/-- A state is instantiated at the point `t` when it holds at `t`. -/
@[simp] theorem at_pure_stative_iff {t : T} :
    At (Interval.pure ↑t) w (.stative P) ↔ ∃ e, P w e ∧ t ∈ τ e :=
  (at_stative_withTop_iff (i := .pure t)).trans <| by
    simp [NonemptyInterval.Overlaps, NonemptyInterval.mem_def]

end Aspect
