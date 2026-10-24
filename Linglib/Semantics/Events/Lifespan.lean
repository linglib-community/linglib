module

public import Linglib.Semantics.Tense.RunTimes

/-!
# Life spans

The life span of an individual is the interval of times at which it exists: the run time of an
event, or the time from an entity's coming into existence to its going out of it. A description
pre-exists an interval when some individual it describes has a life span starting before the
interval does, that is, when its life spans are *before ever* the interval (`Tense.beforeEver`).
A predicate of individuals at times is permanent when it holds of an individual throughout its
life span if it holds of it at all, as individual-level predicates such as *tall* are taken to be.

## Main definitions

* `Event.PreExists τ Q t`: the description `Q` pre-exists the interval `t`.
* `Event.Permanent span P`: `P` holds of an individual throughout its life span if at all.

## Main statements

* `Event.preExists_iff`: some individual of `Q` has a life span starting before `t` does.
* `Event.PreExists.exists`: pre-existence entails existence, since *before ever* is veridical in
  its first argument.
* `Event.preExists_iff_exists_of_precedes`, `Event.not_preExists_of_le`: pre-existence under
  descriptions that locate their individuals before, or within, the interval.
* `Event.Permanent.forall_not_or_forall_iff_mem`: a permanent predicate that holds only within life
  spans holds of an individual at no time or at exactly the times of its life span.
* `Event.Permanent.precedes_pure`: a permanent predicate that held of an individual before `now` and
  fails at `now` places the individual's life span before `now`.

## Implementation notes

Life spans are given by a function `τ` into `NonemptyInterval`, as an event's run time is
(`Event.τ`), so a description denotes the run times `τ '' {x | Q x}`, as an event predicate does
in `Semantics/Tense/RunTimes.lean`. `Permanent` takes life spans of any type with a membership
relation, such as intervals or sets of times, and `Permanent.precedes_pure` takes them as intervals,
since it needs them convex.

## References

* [anscombe-1964]
* [bondarenko-2020]
* [magri-2009]
* [musan-1995]
* [williams-2025]
-/

@[expose] public section

namespace Event

variable {X T : Type*}

/-! ### Pre-existence -/

section PreExists

variable [Preorder T]

/-- The description `Q` pre-exists the interval `t` when the life spans of its individuals are
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

end PreExists

/-! ### Permanent predicates -/

section Permanent

variable {S : Type*} [Membership T S]

/-- `P` is permanent with respect to the life spans `span` when it holds of an individual
throughout its life span if it holds of it at all. -/
def Permanent (span : X → S) (P : X → T → Prop) : Prop :=
  ∀ x, (∃ t, P x t) → ∀ t ∈ span x, P x t

variable {span : X → S} {P : X → T → Prop} {x : X}

theorem Permanent.forall_or_forall_not (hP : Permanent span P) {A : Set T}
    (hA : ∀ t ∈ A, t ∈ span x) : (∀ t ∈ A, P x t) ∨ ∀ t ∈ A, ¬ P x t := by
  by_cases h : ∃ t, P x t
  · exact .inl fun t ht ↦ hP x h t (hA t ht)
  · exact .inr fun t _ ht ↦ h ⟨t, ht⟩

/-- A permanent predicate that holds only within life spans holds of an individual at no time or
at exactly the times of its life span. -/
theorem Permanent.forall_not_or_forall_iff_mem (hP : Permanent span P)
    (hd : ∀ t, P x t → t ∈ span x) : (∀ t, ¬ P x t) ∨ ∀ t, P x t ↔ t ∈ span x := by
  by_cases h : ∃ t, P x t
  · exact .inr fun t ↦ ⟨hd t, hP x h t⟩
  · exact .inl fun t ht ↦ h ⟨t, ht⟩

/-- A permanent predicate that held of an individual at a time of its life span before `now` and
fails at `now` places the individual's life span before `now`. -/
theorem Permanent.precedes_pure [LinearOrder T] {τ : X → NonemptyInterval T} (hP : Permanent τ P)
    {t now : T} (ht : t ∈ τ x) (hPt : P x t) (hlt : t < now) (hnow : ¬ P x now) :
    (τ x).Precedes (.pure now) :=
  (NonemptyInterval.notMem_iff.1 fun h ↦ hnow (hP x ⟨t, hPt⟩ now h)).resolve_left
    (ht.1.trans_lt hlt).asymm

end Permanent

end Event
