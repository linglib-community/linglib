module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Mathlib.Order.WithBot

/-!
# Spector (2016): Comparing Exhaustivity Operators

This file formalizes the worked cases of [spector-2016], which compares the exhaustivity
operator based on minimal worlds, `exhMW`, with the operator of [fox-2007] based on innocent
exclusion, `exhIE`. The paper's general results live in the substrate: the minimal-world
operator entails the innocent-exclusion operator, an alternative is innocently excludable
exactly when the minimal worlds falsify it, closing the alternatives under conjunction makes
the two operators coincide (`exhMW_eq_exhIE_of_infClosed`), and closing them under
disjunction changes neither (`exhIE_sUnion_image_powerset`). Here are the illustrations and the
practical consequences. With a single alternative the operators agree (`elementary`). For a
disjunction with only its disjuncts as alternatives, the minimal-world operator returns the
exclusive reading while innocent exclusion is vacuous (`exhMW_or`, `exhIE_or`); adding the
conjunction as an alternative leaves the order on worlds, and so the minimal worlds,
unchanged (`leALT_or_and_iff`) and makes innocent exclusion exclusive too (`exhIE_or_and`).
The paper's shortcut for computing innocent exclusion over a large alternative set, running
the minimal-world operator over the elementary propositions instead, is illustrated on
*either Mary came, or both Peter and Sue did* (`exhMW_or_and_three`). Finally, a vacuous
minimal-world operator makes innocent exclusion vacuous (`exhIE_eq_of_exhMW_eq`), which
settles the infinite case of *there are at least n stars* against the alternatives *exactly
m* and *at least m* for every `m` ([schwarz-2013]): every world with at least `n` stars, or
infinitely many, is minimal (`exhMW_stars`, `exhIE_stars`).

## Implementation notes

The third operator the paper compares, which denies every non-entailed alternative, and the
theorem that innocent exclusion over the alternatives of [sauerland-2004] equals the
minimal-world operator over the elementary sentences are not formalized; the shortcut is
shown by computing the minimal worlds directly. Independence of the disjuncts is the
existence of a world verifying one disjunct alone, assumed only where a case needs it. The
alternative sets of the illustrations are the paper's, without the prejacent, which the
substrate's compatible sets carry separately.

## References

* [spector-2016]
* [fox-2007]
* [sauerland-2004]
* [schwarz-2013]
-/

@[expose] public section

namespace Spector2016

open Exhaustification Set

variable {World : Type*}

/-! ### The elementary case -/

theorem exhMW_pair {φ ψ : Set World} (hne : (φ \ ψ).Nonempty) : exhMW {φ, ψ} φ = φ \ ψ := by
  obtain ⟨w, hwφ, hwψ⟩ := hne
  ext u
  constructor
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, fun hψu ↦ hmin ⟨w, hwφ, fun a ha haw ↦ ?_, fun h ↦ hwψ (h ψ (Or.inr rfl) hψu)⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact absurd haw hwψ
  · rintro ⟨hu, hψu⟩
    refine ⟨hu, ?_⟩
    rintro ⟨v, hv, -, hnle⟩
    refine hnle fun a ha hau ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hv
    · exact absurd hau hψu

theorem elementary {φ ψ : Set World} (hne : (φ \ ψ).Nonempty) :
    exhMW {φ, ψ} φ = φ \ ψ ∧ exhIE {φ, ψ} φ = φ \ ψ :=
  ⟨exhMW_pair hne, exhIE_pair_sdiff φ hne⟩

/-! ### Disjunction with and without a conjunctive alternative -/

variable {A B : Set World}

theorem exhMW_or (hA : (A \ B).Nonempty) : exhMW {A, B} (A ∪ B) = (A \ B) ∪ (B \ A) := by
  obtain ⟨w, hwA, hwB⟩ := hA
  ext u
  constructor
  · rintro ⟨hu, hmin⟩
    by_cases hAu : u ∈ A
    · refine Or.inl ⟨hAu, fun hBu ↦ hmin ⟨w, Or.inl hwA, fun a ha haw ↦ ?_, fun h ↦ ?_⟩⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact hAu
        · exact absurd haw hwB
      · exact hwB (h B (Or.inr rfl) hBu)
    · rcases hu with hAu' | hBu
      · exact absurd hAu' hAu
      · exact Or.inr ⟨hBu, hAu⟩
  · rintro (⟨hAu, hBu⟩ | ⟨hBu, hAu⟩)
    · refine ⟨Or.inl hAu, ?_⟩
      rintro ⟨v, hv, hle, hnle⟩
      have hAv : v ∈ A := by
        rcases hv with hAv | hBv
        · exact hAv
        · exact absurd (hle B (Or.inr rfl) hBv) hBu
      refine hnle fun a ha hau ↦ ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hAv
      · exact absurd hau hBu
    · refine ⟨Or.inr hBu, ?_⟩
      rintro ⟨v, hv, hle, hnle⟩
      have hBv : v ∈ B := by
        rcases hv with hAv | hBv
        · exact absurd (hle A (Or.inl rfl) hAv) hAu
        · exact hBv
      refine hnle fun a ha hau ↦ ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact absurd hau hAu
      · exact hBv

theorem exhIE_or (hA : (A \ B).Nonempty) (hB : (B \ A).Nonempty) :
    exhIE {A, B} (A ∪ B) = A ∪ B := by
  rw [exhIE_eq_setOf_exhMW_subset_compl {A, B} (A ∪ B), exhMW_or hA]
  obtain ⟨w, hwA, hwB⟩ := hA
  obtain ⟨w', hw'B, hw'A⟩ := hB
  ext u
  refine ⟨fun h ↦ h.1, fun hu ↦ ⟨hu, fun a ha hsub ↦ ?_⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact absurd hwA (hsub (Or.inl ⟨hwA, hwB⟩))
  · exact absurd hw'B (hsub (Or.inr ⟨hw'B, hw'A⟩))

theorem exhMW_congr {ALT ALT' : Set (Set World)} (φ : Set World)
    (h : ∀ u v, (u ≤[ALT] v) ↔ (u ≤[ALT'] v)) : exhMW ALT φ = exhMW ALT' φ := by
  ext u
  show (φ u ∧ ¬ ∃ v, φ v ∧ v <[ALT] u) ↔ (φ u ∧ ¬ ∃ v, φ v ∧ v <[ALT'] u)
  simp only [ltALT, h]

theorem leALT_or_and_iff (u v : World) : (u ≤[{A, B, A ∩ B}] v) ↔ (u ≤[{A, B}] v) := by
  constructor
  · intro h a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact h _ (Or.inl rfl)
    · exact h _ (Or.inr (Or.inl rfl))
  · intro h a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact h _ (Or.inl rfl)
    · exact h _ (Or.inr rfl)
    · exact fun ⟨hAu, hBu⟩ ↦ ⟨h _ (Or.inl rfl) hAu, h _ (Or.inr rfl) hBu⟩

theorem exhMW_or_and (hA : (A \ B).Nonempty) :
    exhMW {A, B, A ∩ B} (A ∪ B) = (A \ B) ∪ (B \ A) :=
  (exhMW_congr (A ∪ B) (leALT_or_and_iff (A := A) (B := B))).trans (exhMW_or hA)

theorem exhIE_or_and (hA : (A \ B).Nonempty) (hB : (B \ A).Nonempty) :
    exhIE {A, B, A ∩ B} (A ∪ B) = (A \ B) ∪ (B \ A) := by
  rw [exhIE_eq_setOf_exhMW_subset_compl {A, B, A ∩ B} (A ∪ B), exhMW_or_and hA]
  obtain ⟨w, hwA, hwB⟩ := hA
  obtain ⟨w', hw'B, hw'A⟩ := hB
  ext u
  constructor
  · rintro ⟨hu, h⟩
    have hnot : u ∉ A ∩ B := h (A ∩ B) (Or.inr (Or.inr rfl)) fun x hx ⟨hxA, hxB⟩ ↦ by
      rcases hx with ⟨-, hx⟩ | ⟨-, hx⟩
      · exact hx hxB
      · exact hx hxA
    rcases hu with hAu | hBu
    · exact Or.inl ⟨hAu, fun hBu ↦ hnot ⟨hAu, hBu⟩⟩
    · exact Or.inr ⟨hBu, fun hAu ↦ hnot ⟨hAu, hBu⟩⟩
  · intro hu
    refine ⟨?_, fun a ha hsub ↦ ?_⟩
    · rcases hu with ⟨hAu, -⟩ | ⟨hBu, -⟩
      · exact Or.inl hAu
      · exact Or.inr hBu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact absurd hwA (hsub (Or.inl ⟨hwA, hwB⟩))
      · exact absurd hw'B (hsub (Or.inr ⟨hw'B, hw'A⟩))
      · rintro ⟨hAu, hBu⟩
        rcases hu with ⟨-, h⟩ | ⟨-, h⟩
        · exact h hBu
        · exact h hAu

/-! ### The shortcut -/

variable {m p s : Set World}

theorem exhMW_or_and_three (hm : ∃ w, w ∈ m ∧ w ∉ p ∧ w ∉ s) :
    exhMW {m, p, s} (m ∪ (p ∩ s)) = (m \ (p ∪ s)) ∪ ((p ∩ s) \ m) := by
  obtain ⟨w, hwm, hwp, hws⟩ := hm
  ext u
  constructor
  · rintro ⟨hu, hmin⟩
    by_cases hmu : u ∈ m
    · refine Or.inl ⟨hmu, fun hpsu ↦ hmin ⟨w, Or.inl hwm, fun a ha haw ↦ ?_, fun h ↦ ?_⟩⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact hmu
        · exact absurd haw hwp
        · exact absurd haw hws
      · rcases hpsu with hpu | hsu
        · exact hwp (h p (Or.inr (Or.inl rfl)) hpu)
        · exact hws (h s (Or.inr (Or.inr rfl)) hsu)
    · rcases hu with hmu' | hpsu
      · exact absurd hmu' hmu
      · exact Or.inr ⟨hpsu, hmu⟩
  · rintro (⟨hmu, hpsu⟩ | ⟨⟨hpu, hsu⟩, hmu⟩)
    · refine ⟨Or.inl hmu, ?_⟩
      rintro ⟨v, hv, hle, hnle⟩
      have hmv : v ∈ m := by
        rcases hv with hmv | ⟨hpv, -⟩
        · exact hmv
        · exact (hpsu (Or.inl (hle p (Or.inr (Or.inl rfl)) hpv))).elim
      refine hnle fun a ha hau ↦ ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact hmv
      · exact (hpsu (Or.inl hau)).elim
      · exact (hpsu (Or.inr hau)).elim
    · refine ⟨Or.inr ⟨hpu, hsu⟩, ?_⟩
      rintro ⟨v, hv, hle, hnle⟩
      have hpsv : v ∈ p ∧ v ∈ s := by
        rcases hv with hmv | hpsv
        · exact absurd (hle m (Or.inl rfl) hmv) hmu
        · exact hpsv
      refine hnle fun a ha hau ↦ ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact absurd hau hmu
      · exact hpsv.1
      · exact hpsv.2

/-! ### Infinitely many alternatives -/

theorem exhIE_eq_of_exhMW_eq {ALT : Set (Set World)} {φ : Set World}
    (h : exhMW ALT φ = φ) : exhIE ALT φ = φ :=
  Set.Subset.antisymm (exhIE_subset ALT φ)
    fun u hu ↦ exhMW_subset_exhIE ALT φ (by rw [h]; exact hu)

/-- Worlds with a number of stars, or infinitely many. -/
abbrev Stars := WithTop ℕ

/-- *There are exactly n stars*. -/
def exactly (n : ℕ) : Set Stars := {w | w = n}

/-- *There are at least n stars*. -/
def atLeast (n : ℕ) : Set Stars := {w | (n : Stars) ≤ w}

/-- The alternatives of *at least n* are every *exactly m* and every *at least m*. -/
def starsALT : Set (Set Stars) := range exactly ∪ range atLeast

theorem eq_of_leALT_stars {u v : Stars} (h : u ≤[starsALT] v) : u = v := by
  induction u using WithTop.recTopCoe with
  | top =>
    induction v using WithTop.recTopCoe with
    | top => rfl
    | coe k =>
      have := h (atLeast (k + 1)) (Or.inr ⟨k + 1, rfl⟩) le_top
      exact absurd (WithTop.coe_le_coe.1 this) (by omega)
  | coe n => exact (h (exactly n) (Or.inl ⟨n, rfl⟩) rfl).symm

theorem exhMW_stars (n : ℕ) : exhMW starsALT (atLeast n) = atLeast n := by
  refine Set.Subset.antisymm (exhMW_subset _ _) fun u hu ↦ ⟨hu, ?_⟩
  rintro ⟨v, -, hle, hnle⟩
  have := eq_of_leALT_stars hle
  subst this
  exact hnle (leALT_refl _ _)

theorem exhIE_stars (n : ℕ) : exhIE starsALT (atLeast n) = atLeast n :=
  exhIE_eq_of_exhMW_eq (exhMW_stars n)

end Spector2016
