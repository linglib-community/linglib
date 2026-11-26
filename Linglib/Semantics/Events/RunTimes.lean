module

public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Events.Basic

/-!
# Run times of an event predicate

The run times of a predicate `P` of events form the predicate `Event.runTimes P` of intervals,
which holds at `s` when `s` is the run time `τ e` of some event `e` with `P e`. It is possibility
`◇[R] P` along the converse of the graph of the trace, so possibility of a run time along a
relation is possibility of an event along it, `Event.diamond_runTimes_iff`.

## References

* [krifka-1989]
-/

@[expose] public section

namespace Event

open ModalLogic
open scoped SetRel

variable {T : Type*} [LinearOrder T] {E : Type*} [TemporalTrace E T] {P : E → Prop}
  {s : NonemptyInterval T}

/-- The run times of an event predicate: `runTimes P` holds at the run time of each event of
`P`. -/
def runTimes (P : E → Prop) : NonemptyInterval T → Prop := ◇[(Function.graph τ).inv] P

theorem runTimes_iff : runTimes P s ↔ ∃ e, τ e = s ∧ P e := .rfl

theorem runTimes_τ {e : E} (h : P e) : runTimes P (τ e) := ⟨e, rfl, h⟩

/-- Possibility of a run time along a relation is possibility of an event along it. -/
theorem diamond_runTimes_iff {α : Type*} {R : SetRel α (NonemptyInterval T)} {a : α} :
    ◇[R] (runTimes P) a ↔ ∃ e, a ~[R] τ e ∧ P e := by
  constructor
  · rintro ⟨s, h, e, he, hP⟩
    obtain rfl : τ e = s := he
    exact ⟨e, h, hP⟩
  · rintro ⟨e, h, hP⟩
    exact ⟨τ e, h, e, rfl, hP⟩

theorem runTimes_mono : Monotone (runTimes : (E → Prop) → NonemptyInterval T → Prop) :=
  diamond_mono _

end Event
