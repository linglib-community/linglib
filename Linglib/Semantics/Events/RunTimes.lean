module

public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Events.Basic

/-!
# Run times of an event predicate

The run times of a predicate `P` of events form the predicate `Event.runTimes τ P` of intervals,
which holds at `s` when `s` is the run time `τ e` of some event `e` with `P e`. It is possibility
`◇[R] P` along the converse of the graph of the trace, so possibility of a run time along a
relation is possibility of an event along it, `Event.diamond_runTimes_iff`. Taking run times is
left adjoint to pulling an interval property back along the trace, `Event.runTimes_le_iff`, and a
condition on the run time of an event passes through it, `Event.runTimes_inf_comp`.

## References

* [krifka-1989]
-/

@[expose] public section

namespace Event

open ModalLogic
open scoped SetRel

variable {T : Type*} [LinearOrder T] {E : Type*} {τ : E → NonemptyInterval T} {P : E → Prop}
  {s : NonemptyInterval T}

/-- The run times of an event predicate: `runTimes τ P` holds at the run time of each event
of `P`. -/
def runTimes (τ : E → NonemptyInterval T) (P : E → Prop) : NonemptyInterval T → Prop :=
  ◇[(Function.graph τ).inv] P

theorem runTimes_iff : runTimes τ P s ↔ ∃ e, τ e = s ∧ P e := .rfl

theorem runTimes_τ {e : E} (h : P e) : runTimes τ P (τ e) := ⟨e, rfl, h⟩

/-- Possibility of a run time along a relation is possibility of an event along it. -/
theorem diamond_runTimes_iff {α : Type*} {R : SetRel α (NonemptyInterval T)} {a : α} :
    ◇[R] (runTimes τ P) a ↔ ∃ e, a ~[R] τ e ∧ P e := by
  constructor
  · rintro ⟨s, h, e, he, hP⟩
    obtain rfl : τ e = s := he
    exact ⟨e, h, hP⟩
  · rintro ⟨e, h, hP⟩
    exact ⟨τ e, h, e, rfl, hP⟩

theorem runTimes_mono : Monotone (runTimes τ) :=
  diamond_mono _

/-- The run times of a predicate satisfy an interval property exactly when its events run at times
that do: `runTimes` is left adjoint to pullback along the trace. -/
theorem runTimes_le_iff {q : NonemptyInterval T → Prop} : runTimes τ P ≤ q ↔ P ≤ q ∘ τ :=
  ⟨fun h _ he ↦ h _ (runTimes_τ he), fun h _ hs ↦ let ⟨e, he, hP⟩ := runTimes_iff.1 hs; he ▸ h e hP⟩

/-- A condition on the run time of an event is a condition on the run times of the predicate. -/
theorem runTimes_inf_comp (q : NonemptyInterval T → Prop) :
    runTimes τ (P ⊓ q ∘ τ) = runTimes τ P ⊓ q := by
  ext s
  simp only [runTimes_iff, Pi.inf_apply, Function.comp_apply, inf_Prop_eq]
  exact ⟨fun ⟨e, h, hP, hq⟩ ↦ ⟨⟨e, h, hP⟩, h ▸ hq⟩, fun ⟨⟨e, h, hP⟩, hq⟩ ↦ ⟨e, h, hP, h ▸ hq⟩⟩

end Event
