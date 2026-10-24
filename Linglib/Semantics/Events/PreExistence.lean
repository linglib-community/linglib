module

public import Linglib.Semantics.Tense.RunTimes

/-!
# Pre-existence

A description pre-exists an interval when some individual it describes has a time span, the run
time of an event or the life span of an entity, that starts before the interval does: the run
times of the description are *before ever* the interval (`Tense.beforeEver`). Pre-existence has
been proposed as the presupposition of the Buryat attitude verb *hanaxa* 'think' on a nominal
complement and of English *forget* on its complement.

*Before ever* is veridical in its first argument, so pre-existence entails that the description
describes something, and a verb presupposing it gets a factive inference. How much more it says
depends on where a description locates its individuals. One that locates them before the interval
pre-exists it as soon as it describes anything, and one that locates them within the interval
never does.

## Main definitions

* `Event.PreExists τ Q t`: the description `Q` pre-exists the interval `t`.

## Main statements

* `Event.preExists_iff`: some individual of `Q` has a time span starting before `t` does.
* `Event.PreExists.exists`: pre-existence entails existence.
* `Event.preExists_iff_exists_of_precedes`, `Event.not_preExists_of_le`: pre-existence under
  descriptions that locate their individuals before, or within, the interval.

## Implementation notes

The time spans are given by a function `τ` into `NonemptyInterval`, as an event's run time
(`Event.τ`) or an entity's life span, so a description denotes the run times `τ '' {x | Q x}`, as
an event predicate does in `Semantics/Tense/RunTimes.lean`. Pre-existence compares left boundaries
only and leaves the right boundary free, so an individual can outlast the interval it pre-exists.

## References

* [anscombe-1964]
* [bondarenko-2020]
* [williams-2025]
-/

@[expose] public section

namespace Event

variable {X T : Type*} [Preorder T]

/-- The description `Q` pre-exists the interval `t` when the time spans of its individuals are
before ever `t`. -/
def PreExists (τ : X → NonemptyInterval T) (Q : X → Prop) (t : NonemptyInterval T) : Prop :=
  Tense.beforeEver (τ '' {x | Q x}) {t}

variable {τ : X → NonemptyInterval T} {Q Q' : X → Prop} {t t' : NonemptyInterval T}

theorem preExists_iff : PreExists τ Q t ↔ ∃ x, Q x ∧ (τ x).fst < t.fst := by
  simp [PreExists, Tense.beforeEver_singleton_right]

namespace PreExists

theorem «exists» (h : PreExists τ Q t) : ∃ x, Q x :=
  let ⟨x, hx, _⟩ := preExists_iff.1 h
  ⟨x, hx⟩

theorem mono (hQ : ∀ x, Q x → Q' x) (h : PreExists τ Q t) : PreExists τ Q' t :=
  let ⟨x, hx, hlt⟩ := preExists_iff.1 h
  preExists_iff.2 ⟨x, hQ x hx, hlt⟩

theorem mono_right (ht : t.fst ≤ t'.fst) (h : PreExists τ Q t) : PreExists τ Q t' :=
  let ⟨x, hx, hlt⟩ := preExists_iff.1 h
  preExists_iff.2 ⟨x, hx, hlt.trans_le ht⟩

end PreExists

@[simp] theorem preExists_eq_iff {x : X} : PreExists τ (· = x) t ↔ (τ x).fst < t.fst := by
  simp [preExists_iff]

theorem preExists_of_precedes {x : X} (hx : Q x) (h : (τ x).Precedes t) : PreExists τ Q t :=
  preExists_iff.2 ⟨x, hx, (τ x).fst_le_snd.trans_lt h⟩

/-- A description of individuals preceding an interval pre-exists it exactly when it describes
something. -/
theorem preExists_iff_exists_of_precedes (h : ∀ x, Q x → (τ x).Precedes t) :
    PreExists τ Q t ↔ ∃ x, Q x :=
  ⟨PreExists.exists, fun ⟨x, hx⟩ ↦ preExists_of_precedes hx (h x hx)⟩

/-- A description of individuals within an interval never pre-exists it. -/
theorem not_preExists_of_le (h : ∀ x, Q x → τ x ≤ t) : ¬ PreExists τ Q t := fun hp ↦
  let ⟨x, hx, hlt⟩ := preExists_iff.1 hp
  hlt.not_ge (h x hx).1

end Event
