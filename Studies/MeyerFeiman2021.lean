module

public import Mathlib.Data.Finset.Insert

/-!
# Meyer and Feiman (2021): Priming Reveals Similarities and Differences Between Implicatures

This file formalizes the implicature spectrum that [meyer-feiman-2021] propose to reconcile
their structural-priming results. The core implicature mechanism has two sub-computations,
generating alternatives and negating them, and each may run online or have its output
stored; alternatives generated online cannot have been pre-negated, so the spectrum has
three points (`Spectrum`, `spectrum_iff`): both steps online, the alternatives stored and
negated online, or the enriched reading stored as a second lexical entry. Two readings
prime each other when they share an online sub-computation that can be primed (`Primes`).
Three experiments find that *some* and number words prime each other while free-choice
disjunction primes neither; the paper places *some* at the fully online point and number
words at the stored-alternatives point, so the shared computation behind the effect is the
negation of alternatives (`negate_primeable`), and the free-choice data then rule out the
recursive-implicature derivation of free choice, which negates alternatives, while
admitting the alternative-asserting mechanism of [bar-lev-fox-2017] exactly when generation
cannot be primed and modal-specific accounts such as [simons-2005] unconditionally
(`fits_iff`).

## Implementation notes

A derivation is represented by the finite set of sub-computations it runs online; the
paper's hypothesis for *some* and number words with free choice left open is `spectrum`,
and `Fits` compares an account's predicted between-category priming with the observed
pattern. Within-category priming, the higher enrichment rate for number words, and the
experiments' picture-similarity controls are not represented.

## References

* [meyer-feiman-2021]
* [bar-lev-fox-2017]
* [fox-2007]
* [simons-2005]
-/

@[expose] public section

namespace MeyerFeiman2021

/-- The sub-computations an account of an enriched reading may run: generating alternatives,
negating them, and, in the free-choice mechanism of [bar-lev-fox-2017], asserting them. -/
inductive Step where
  | generate
  | negate
  | assert
  deriving DecidableEq

/-- A point on the implicature spectrum: the sub-computations of the core mechanism that run
online, the others having their output stored, where alternatives generated online cannot
have been pre-negated. -/
def Spectrum (o : Finset Step) : Prop :=
  o ⊆ {.generate, .negate} ∧ (.generate ∈ o → .negate ∈ o)

instance : DecidablePred Spectrum := λ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem spectrum_iff (o : Finset Step) :
    Spectrum o ↔ o = {.generate, .negate} ∨ o = {.negate} ∨ o = ∅ := by
  constructor
  · rintro ⟨hsub, himp⟩
    have ha : Step.assert ∉ o := λ h => by simpa using hsub h
    by_cases hn : Step.negate ∈ o
    · by_cases hg : Step.generate ∈ o
      · left; ext s; cases s <;> simp [hg, hn, ha]
      · right; left; ext s; cases s <;> simp [hg, hn, ha]
    · right; right; ext s; cases s <;> simp [hn, mt himp hn, ha]
  · rintro (rfl | rfl | rfl) <;> decide

/-- Two derivations prime each other when some sub-computation that can be primed runs online
in both. -/
def Primes (primeable o o' : Finset Step) : Prop := ∃ s ∈ primeable, s ∈ o ∧ s ∈ o'

/-- The three categories of enriched reading tested. -/
inductive Category where
  | some
  | number
  | freeChoice
  deriving DecidableEq

/-- Between-category priming observed: *some* and number words prime each other in both
directions, and free-choice disjunction primes neither and is primed by neither. -/
def primed : Category → Category → Bool
  | .some, .number | .number, .some => true
  | _, _ => false

/-- An account assigns each category the sub-computations its enriched reading runs online; it
fits the data when it predicts between-category priming exactly where observed. -/
def Fits (primeable : Finset Step) (account : Category → Finset Step) : Prop :=
  ∀ a b, a ≠ b → (primed a b ↔ Primes primeable (account a) (account b))

/-- The paper's hypothesis, with the free-choice derivation `fc` left open: *some* generates
and negates its alternatives online, and number words store their alternatives, the count
list, and negate them online. -/
def spectrum (fc : Finset Step) : Category → Finset Step
  | .some => {.generate, .negate}
  | .number => {.negate}
  | .freeChoice => fc

theorem negate_primeable {primeable fc : Finset Step}
    (h : Primes primeable (spectrum fc .some) (spectrum fc .number)) : .negate ∈ primeable := by
  obtain ⟨s, hs, -, h⟩ := h
  simp only [spectrum, Finset.mem_singleton] at h
  exact h ▸ hs

theorem fits_iff (primeable fc : Finset Step) :
    Fits primeable (spectrum fc) ↔
      .negate ∈ primeable ∧ ¬ Primes primeable (spectrum fc .some) fc := by
  constructor
  · intro h
    refine ⟨negate_primeable ((h .some .number (by decide)).mp rfl), λ hp => ?_⟩
    exact absurd ((h .some .freeChoice (by decide)).mpr hp) (by decide)
  · rintro ⟨hn, hfc⟩ a b hab
    have hnum : ¬ Primes primeable {.negate} fc := λ ⟨s, hs, h₁, h₂⟩ =>
      hfc ⟨s, hs, Finset.mem_insert_of_mem h₁, h₂⟩
    cases a <;> cases b <;>
      simp only [primed, spectrum, Bool.false_eq_true, false_iff, true_iff]
    · exact absurd rfl hab
    · exact ⟨.negate, hn, by decide, by decide⟩
    · exact hfc
    · exact ⟨.negate, hn, by decide, by decide⟩
    · exact absurd rfl hab
    · exact hnum
    · exact λ ⟨s, hs, h₁, h₂⟩ => hfc ⟨s, hs, h₂, h₁⟩
    · exact λ ⟨s, hs, h₁, h₂⟩ => hnum ⟨s, hs, h₂, h₁⟩
    · exact absurd rfl hab

theorem recursive_not_fits (primeable : Finset Step) :
    ¬ Fits primeable (spectrum {.generate, .negate}) := by
  rw [fits_iff]
  rintro ⟨hn, h⟩
  exact h ⟨.negate, hn, by decide, by decide⟩

theorem inclusion_fits_iff (primeable : Finset Step) :
    Fits primeable (spectrum {.generate, .assert}) ↔
      .negate ∈ primeable ∧ .generate ∉ primeable := by
  rw [fits_iff]
  refine and_congr_right λ _ => ⟨λ h hg => h ⟨.generate, hg, by decide, by decide⟩, ?_⟩
  rintro hg ⟨s, hs, h₁, h₂⟩
  cases s <;> simp_all [spectrum]

theorem modal_fits_iff (primeable : Finset Step) :
    Fits primeable (spectrum ∅) ↔ .negate ∈ primeable := by
  rw [fits_iff]
  simp [Primes]

end MeyerFeiman2021
