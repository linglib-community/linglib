module

public import Linglib.Core.Order.Interval.Basic

/-!
# Pre-existence

An individual pre-exists a time when its time span, the run time of an event or the life span of
an entity, starts before that time. [bondarenko-2020] derives the factive inference of Buryat
*hanaxa* 'think' with a nominal complement from a presupposition that the complement describes
something that pre-exists the thinking, and [williams-2025] places a covert modal under English
*forget* exactly where the complement would otherwise contradict the same presupposition.

Pre-existence entails existence (`Event.PreExists.exists`), which is how it yields a factive
inference. What it adds depends on where a description locates its individuals: one that
locates them before the time pre-exists it as soon as it describes anything
(`Event.preExists_iff_exists_of_precedes`), and one that locates them within the time never does
(`Event.not_preExists_of_le`).

[bondarenko-2020] takes the presupposition to come from the head that introduces a verb's
internal argument, which also gives verbs of destruction and use theirs (*Sue broke a vase*), so
it is not specific to attitude verbs.

## Main definitions

* `Event.PreExists τ Q a`: some individual of `Q` has a time span starting before `a`.

## Main statements

* `Event.PreExists.exists`: pre-existence entails existence.
* `Event.preExists_iff_exists_of_precedes`, `Event.not_preExists_of_le`: pre-existence under
  descriptions that locate their individuals before, or within, a time.

## Implementation notes

The time spans are given by a function `τ` into `NonemptyInterval`, as an event's run time
(`Event.τ`) or an entity's life span. Pre-existence compares left boundaries only, and leaves the
right boundary free, so an individual can outlast the time it pre-exists ([bondarenko-2020]'s
(10)).

## References

* [bondarenko-2020]
* [williams-2025]
-/

@[expose] public section

namespace Event

variable {X T : Type*} [Preorder T]

/-- Some individual of `Q` pre-exists `a`: its time span starts before `a`. -/
def PreExists (τ : X → NonemptyInterval T) (Q : X → Prop) (a : T) : Prop :=
  ∃ x, Q x ∧ (τ x).fst < a

variable {τ : X → NonemptyInterval T} {Q Q' : X → Prop} {a b : T} {t : NonemptyInterval T}

namespace PreExists

theorem «exists» (h : PreExists τ Q a) : ∃ x, Q x :=
  let ⟨x, hx, _⟩ := h
  ⟨x, hx⟩

theorem mono (hQ : ∀ x, Q x → Q' x) (h : PreExists τ Q a) : PreExists τ Q' a :=
  let ⟨x, hx, hlt⟩ := h
  ⟨x, hQ x hx, hlt⟩

theorem mono_right (hab : a ≤ b) (h : PreExists τ Q a) : PreExists τ Q b :=
  let ⟨x, hx, hlt⟩ := h
  ⟨x, hx, hlt.trans_le hab⟩

end PreExists

@[simp] theorem preExists_eq_iff {x : X} : PreExists τ (· = x) a ↔ (τ x).fst < a :=
  ⟨fun ⟨_, hx, hlt⟩ ↦ hx ▸ hlt, fun h ↦ ⟨x, rfl, h⟩⟩

theorem preExists_of_precedes {x : X} (hx : Q x) (h : (τ x).Precedes t) : PreExists τ Q t.fst :=
  ⟨x, hx, (τ x).fst_le_snd.trans_lt h⟩

theorem preExists_iff_exists_of_precedes (h : ∀ x, Q x → (τ x).Precedes t) :
    PreExists τ Q t.fst ↔ ∃ x, Q x :=
  ⟨PreExists.exists, fun ⟨x, hx⟩ ↦ preExists_of_precedes hx (h x hx)⟩

theorem not_preExists_of_le (h : ∀ x, Q x → τ x ≤ t) : ¬ PreExists τ Q t.fst :=
  fun ⟨x, hx, hlt⟩ ↦ hlt.not_ge (h x hx).1

end Event
