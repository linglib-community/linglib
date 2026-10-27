module

public import Linglib.Semantics.Aspect.Viewpoint

/-!
# Instantiation of sorted properties

This file defines the instantiation of a sorted property at a reference interval. An event
property is instantiated when the run time of one of its events lies in the interval, a state
property when the run time of one of its states overlaps it, as in the discourse
representation analyses of Kamp and Rohrer, Partee, and Kamp and Reyle, and a property of times
when it holds of the interval. Reference intervals are `Interval (WithTop T)`, so an interval
may run to the end of time and the null interval is `⊥`.

## Main definitions

* `Aspect.SortedProperty`: a property of events, of states, or of times.
* `Aspect.At`: the instantiation relation `AT(t, w, P)`.

## Main results

* `Aspect.At.mono`: instantiation of an eventuality is monotone in the interval.
* `Aspect.at_Ici_eventive_iff`: an event property is instantiated at a ray when an event starts
  no earlier than it.
* `Aspect.at_Ici_stative_iff`: a state property is instantiated at a ray when a state persists
  to it.
* `Aspect.at_eventive_withTop_iff_prfv`: on a bounded interval, eventive instantiation is
  Klein's perfective `PRFV`.

## References

* [H. Kamp and C. Rohrer, *Tense in Texts* (1983)][kamp-rohrer-1983]
* [B. Partee, *Nominal and Temporal Anaphora* (1984)][partee-1984]
* [H. Kamp and U. Reyle, *From Discourse to Logic* (1993)][kamp-reyle-1993]
* [W. Klein, *Time in Language* (1994)][klein-1994]
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

variable [Event.TemporalTrace E T]

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
theorem at_eventive_withTop_iff_prfv {i : NonemptyInterval T} :
    At ↑i.withTop w (.eventive P) ↔ i ∈ PRFV P w := by
  simp [At, mem_prfv, and_comm]

theorem at_stative_withTop_of_unbounded {i : NonemptyInterval T} (h : i ∈ UNBOUNDED P w) :
    At ↑i.withTop w (.stative P) := by
  obtain ⟨e, hle, he⟩ := h
  have hle := NonemptyInterval.le_def.1 hle
  refine ⟨e, he, Interval.not_disjoint_iff.2 ⟨↑i.fst, ?_, ?_⟩⟩
  · exact NonemptyInterval.mem_withTop.2 ⟨WithTop.coe_le_coe.2 hle.1,
      WithTop.coe_le_coe.2 (le_trans i.fst_le_snd hle.2)⟩
  · exact NonemptyInterval.mem_withTop.2 ⟨le_rfl, WithTop.coe_le_coe.2 i.fst_le_snd⟩

end Aspect
