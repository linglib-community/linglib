module

public import Linglib.Semantics.Composition.Assignment
public import Linglib.Semantics.Tense.Quantificational

/-!
# Partee (1973): Some Structural Analogies between Tenses and Pronouns in English

Partee argues that tenses have the uses of pronouns, deictic, anaphoric and bound, and so refer
to times as pronouns refer to individuals, where the tense operators of Prior quantify over
them. Uttered halfway down the turnpike, *I didn't turn off the stove* is about a definite
interval that the context makes salient, and says that the speaker did not turn off the stove
then. An existential past gives the sentence two readings, by the scope of the negation, and it
has neither: that the speaker never turned off the stove is too strong, and that there is a past
time at which the speaker did not is too weak. In *Sheila had a party last Friday and Sam got
drunk* the second tense picks up the time of the first, as an anaphoric pronoun picks up its
antecedent, which two existential pasts do not require.

## Implementation notes

* A time is an interval of a linear order, mathlib's `NonemptyInterval`, and a tense is an index
  of an assignment of times, read as a pronoun, the value of its index.
* A clause in the past tense says that the time of its index precedes the speech time and that
  the clause holds at that time, as a conjunction.

## References

* [partee-1973]
* [prior-1967]
-/

@[expose] public section

namespace Partee1973

open Montague ModalLogic Tense
open scoped Denotes
open scoped SetRel

variable {T : Type*} [LinearOrder T] {P Q : NonemptyInterval T → Prop} {σ : NonemptyInterval T}
  {g : Assignment (NonemptyInterval T)} {n : ℕ}

/-- A clause in the past tense with index `n` says that the time of `n` precedes the speech time
`σ` and that the clause holds at it. -/
def Past (n : ℕ) (P : NonemptyInterval T → Prop) (σ : NonemptyInterval T) :
    Assignment (NonemptyInterval T) → Prop :=
  fun g ↦ Perspective.Presup Allen.precedes σ (g n) ∧ P (g n)

theorem past_iff : Past n P σ g ↔ (g n).Precedes σ ∧ P (g n) := by
  simp [Past]

theorem dependsOn_past : DependsOn (Past n P σ) {n} := fun g g' h ↦ by
  simp only [Past, h n rfl]

theorem Past.sometime (h : Past n P σ g) : ◇[Perspective.toSetRel Allen.precedes] P σ :=
  ⟨_, h.1, h.2⟩

/-- With its index bound by an existential quantifier, the past tense is Prior's past. -/
theorem exists_past_iff_sometime :
    (∃ t, lambdaAbsG n (Past n P σ) g t) ↔ ◇[Perspective.toSetRel Allen.precedes] P σ := by
  simp [Past, Diamond]

/-! ### The stove

*I didn't turn off the stove*, with `P` the times at which the speaker turns off the stove. -/

/-- A speaker who never turned off the stove did not turn it off at the salient time. -/
theorem never_entails_deictic (hn : Perspective.Presup Allen.precedes σ (g n))
    (h : ¬ ◇[Perspective.toSetRel Allen.precedes] P σ) : Past n (fun t ↦ ¬ P t) σ g :=
  ⟨hn, fun hP ↦ h (Past.sometime ⟨hn, hP⟩)⟩

/-- A speaker who did not turn off the stove at the salient time did not turn it off at some
past time. -/
theorem deictic_entails_sometime_not (h : Past n (fun t ↦ ¬ P t) σ g) :
    ◇[Perspective.toSetRel Allen.precedes] (fun t ↦ ¬ P t) σ :=
  h.sometime

/-- The sentence is true of a speaker who turned off the stove on an earlier occasion and not at
the salient time, so the reading on which the speaker never turned it off is too strong. -/
theorem never_too_strong :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      Past 0 (fun t ↦ ¬ P t) σ g ∧ ◇[Perspective.toSetRel Allen.precedes] P σ :=
  ⟨.pure 10, fun _ ↦ .pure 5, (· = .pure 1), ⟨Perspective.presup_precedes.2 (by decide), by decide⟩,
    .pure 1, Perspective.presup_precedes.2 (by decide), rfl⟩

/-- The sentence is false of a speaker who turned off the stove at the salient time, although
there are past times at which the speaker did not, so that reading is too weak. -/
theorem sometime_not_too_weak :
    ∃ (σ : NonemptyInterval ℤ) (g : Assignment (NonemptyInterval ℤ))
      (P : NonemptyInterval ℤ → Prop),
      ◇[Perspective.toSetRel Allen.precedes] (fun t ↦ ¬ P t) σ ∧
        Perspective.Presup Allen.precedes σ (g 0) ∧ ¬ Past 0 (fun t ↦ ¬ P t) σ g :=
  ⟨.pure 10, fun _ ↦ .pure 5, (· = .pure 5),
    ⟨.pure 1, Perspective.presup_precedes.2 (by decide), by decide⟩,
    Perspective.presup_precedes.2 (by decide), fun h ↦ h.2 rfl⟩

/-! ### Anaphora

*Sheila had a party last Friday and Sam got drunk*, with `P` the times of the party and `Q`
those of Sam's getting drunk. -/

/-- Two past tenses with one index locate their clauses at one time, as an anaphoric pronoun and
its antecedent pick out one individual. -/
theorem anaphoric_iff :
    Past n P σ g ∧ Past n Q σ g ↔ Past n (fun t ↦ P t ∧ Q t) σ g :=
  ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩⟩

/-- Two existential pasts may be true of different times and of no common one. -/
theorem existential_pasts_not_anaphoric :
    ∃ (σ : NonemptyInterval ℤ) (P Q : NonemptyInterval ℤ → Prop),
      ◇[Perspective.toSetRel Allen.precedes] P σ ∧ ◇[Perspective.toSetRel Allen.precedes] Q σ ∧
        ∀ t, ¬ (P t ∧ Q t) :=
  ⟨.pure 10, (· = .pure 1), (· = .pure 2), ⟨_, Perspective.presup_precedes.2 (by decide), rfl⟩,
    ⟨_, Perspective.presup_precedes.2 (by decide), rfl⟩,
    fun _ ⟨h₁, h₂⟩ ↦ absurd (h₁.symm.trans h₂) (by decide)⟩

end Partee1973
