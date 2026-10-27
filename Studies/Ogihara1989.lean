module

public import Linglib.Data.Examples.Ogihara1989
public import Studies.Partee1973

/-!
# Ogihara (1989): Temporal Reference in English and Japanese

The first chapter of the dissertation weighs the quantificational analysis of tense against the
referential analysis of Partee and keeps a part of each: a tense is an existential quantifier
over times, and what depends on context is a restriction of the quantifier to an interval that
the context makes salient. In answer to *Did you see Mary?*, *Yes, I saw her* says that the
speaker saw Mary at some time within the day, which the speaker need not be able to name, so the
tense is not a free variable. *I didn't turn off the stove* says that the salient interval is
past and that the speaker turned off the stove at none of its subintervals. The referential
reading is weaker, since turning off a stove takes less time than the salient interval and so
does not hold at the interval as a whole, and the reading on which the speaker never turned off
the stove is stronger.

## Implementation notes

* A clause holds at an interval when the interval is among its times, and the subinterval
  relation is the order `≤` of `NonemptyInterval`.
* The examples are the rows of `Data.Examples.Ogihara1989`.

## TODO

* The theory of sequence of tense of the second chapter and the fragments of English and
  Japanese of the third are not formalized.

## References

* [ogihara-1989]
* [partee-1973]
* [prior-1967]
-/

@[expose] public section

namespace Ogihara1989

open Montague ModalLogic Tense Partee1973
open scoped Denotes
open scoped SetRel

variable {T : Type*} [LinearOrder T] {P : NonemptyInterval T → Prop} {K σ : NonemptyInterval T}
  {g : Assignment (NonemptyInterval T)} {n : ℕ}

/-- The past restricted to the salient interval `K` holds when the clause held at a past
subinterval of `K`, as *Yes, I saw her* (`Examples.ex_57`) says of the day. It is Partee's past
tense with its index bound by an existential quantifier over the subintervals of `K`. -/
theorem restricted_iff_exists_past :
    ◇[Perspective.toSetRel Allen.precedes] (fun t ↦ t ≤ K ∧ P t) σ ↔
      ∃ t ≤ K, lambdaAbsG n (Past n P σ) g t := by
  simp [Past, Diamond, and_left_comm]

/-! ### The stove

*I didn't turn off the stove* (`Examples.ex_46a`), with `P` the times at which the speaker turns
off the stove and the time of the tense's index the salient interval. The sentence says that this
interval is past and has no subinterval at which the speaker turned off the stove. -/

/-- The stove sentence says that the salient interval is past and denies the past restricted to
it. -/
theorem no_subinterval_iff_not_restricted :
    Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ↔
      Perspective.Presup Allen.precedes σ (g n) ∧
        ¬ ◇[Perspective.toSetRel Allen.precedes] (fun t ↦ t ≤ g n ∧ P t) σ :=
  ⟨fun h ↦ ⟨h.1, fun ⟨t, _, hle, hP⟩ ↦ h.2 ⟨t, hle, hP⟩⟩, fun h ↦ ⟨h.1, fun ⟨t, hle, hP⟩ ↦
    h.2 ⟨t, Perspective.presup_precedes.2 (NonemptyInterval.precedes_of_le_of_precedes hle
      (Perspective.presup_precedes.1 h.1)), hle, hP⟩⟩⟩

/-- A speaker who turned off the stove at no subinterval of the salient interval did not turn it
off at that interval. -/
theorem no_subinterval_entails_deictic (h : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g) :
    Past n (fun t ↦ ¬ P t) σ g :=
  ⟨h.1, fun hP ↦ h.2 ⟨_, le_rfl, hP⟩⟩

/-- Turning off the stove takes a moment, so a speaker who did so within the salient interval
did not do so at that interval, and the referential reading is true where the sentence is
false. -/
theorem deictic_too_weak :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ P t) σ g ∧ ¬ Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  ⟨.pure 10, fun _ ↦ ⟨(0, 5), by decide⟩, (· = .pure 3),
    ⟨Perspective.presup_precedes.2 (by decide), by decide⟩,
    fun h ↦ h.2 ⟨.pure 3, by decide, rfl⟩⟩

/-- A speaker who never turned off the stove turned it off at no subinterval of the salient
interval. -/
theorem never_entails_no_subinterval (hn : Perspective.Presup Allen.precedes σ (g n))
    (h : ¬ ◇[Perspective.toSetRel Allen.precedes] P σ) : Past n (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g :=
  ⟨hn, fun ⟨t, hle, hP⟩ ↦ h ⟨t, Perspective.presup_precedes.2
    (NonemptyInterval.precedes_of_le_of_precedes hle (Perspective.presup_precedes.1 hn)), hP⟩⟩

/-- The sentence is true of a speaker who turned off the stove before the salient interval. -/
theorem never_too_strong :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ ∃ t' ≤ t, P t') σ g ∧ ◇[Perspective.toSetRel Allen.precedes] P σ := by
  refine ⟨.pure 10, fun _ ↦ ⟨(5, 6), by decide⟩, (· = .pure 1),
    ⟨Perspective.presup_precedes.2 (by decide), ?_⟩, .pure 1,
    Perspective.presup_precedes.2 (by decide), rfl⟩
  rintro ⟨t, ht, rfl⟩
  exact absurd (NonemptyInterval.le_def.1 ht).1 (by decide)

end Ogihara1989
