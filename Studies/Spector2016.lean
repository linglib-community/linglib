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
unchanged (`satisfied_or_and_subset_iff`) and makes innocent exclusion exclusive too
(`exhIE_or_and`). The paper's shortcut for computing innocent exclusion over a large
alternative set, running the minimal-world operator over the elementary propositions instead,
is illustrated on *either Mary came, or both Peter and Sue did* (`exhMW_or_and_three`).
Finally, a vacuous minimal-world operator makes innocent exclusion vacuous
(`exhIE_eq_of_exhMW_eq`), which settles the infinite case of *there are at least n stars*
against the alternatives *exactly m* and *at least m* for every `m` ([schwarz-2013]): every
world with at least `n` stars, or infinitely many, is minimal (`exhMW_stars`, `exhIE_stars`).

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
open Preorder (satisfied)

variable {World : Type*}

/-! ### The elementary case -/

theorem exhMW_pair {φ ψ : Set World} (hne : (φ \ ψ).Nonempty) : exhMW {φ, ψ} φ = φ \ ψ := by
  obtain ⟨w, hwφ, hwψ⟩ := hne
  ext u
  constructor
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, fun hψu ↦ hwψ (hmin hwφ ?_ ⟨Or.inr rfl, hψu⟩).2⟩
    rintro a ⟨rfl | rfl, haw⟩
    · exact ⟨Or.inl rfl, hu⟩
    · exact absurd haw hwψ
  · rintro ⟨hu, hψu⟩
    refine ⟨hu, fun v hv _ a ⟨ha, hau⟩ ↦ ⟨ha, ?_⟩⟩
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
    · refine Or.inl ⟨hAu, fun hBu ↦ hwB (hmin (Or.inl hwA) ?_ ⟨Or.inr rfl, hBu⟩).2⟩
      rintro a ⟨rfl | rfl, haw⟩
      · exact ⟨Or.inl rfl, hAu⟩
      · exact absurd haw hwB
    · exact Or.inr ⟨hu.resolve_left hAu, hAu⟩
  · rintro (⟨hAu, hBu⟩ | ⟨hBu, hAu⟩)
    · refine ⟨Or.inl hAu, fun v hv hle a ⟨ha, hau⟩ ↦ ⟨ha, ?_⟩⟩
      have hAv : v ∈ A := hv.resolve_right fun hBv ↦ hBu (hle ⟨Or.inr rfl, hBv⟩).2
      rcases ha with rfl | rfl
      · exact hAv
      · exact absurd hau hBu
    · refine ⟨Or.inr hBu, fun v hv hle a ⟨ha, hau⟩ ↦ ⟨ha, ?_⟩⟩
      have hBv : v ∈ B := hv.resolve_left fun hAv ↦ hAu (hle ⟨Or.inl rfl, hAv⟩).2
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
    (h : ∀ u v, satisfied (· ∈ ·) ALT u ⊆ satisfied (· ∈ ·) ALT v ↔
      satisfied (· ∈ ·) ALT' u ⊆ satisfied (· ∈ ·) ALT' v) :
    exhMW ALT φ = exhMW ALT' φ := by
  ext u
  simp only [mem_exhMW, MinimalFor, h]

theorem satisfied_or_and_subset_iff (u v : World) :
    satisfied (· ∈ ·) {A, B, A ∩ B} u ⊆ satisfied (· ∈ ·) {A, B, A ∩ B} v ↔
      satisfied (· ∈ ·) {A, B} u ⊆ satisfied (· ∈ ·) {A, B} v := by
  constructor
  · rintro h a ⟨rfl | rfl, hau⟩
    · exact ⟨Or.inl rfl, (h ⟨Or.inl rfl, hau⟩).2⟩
    · exact ⟨Or.inr rfl, (h ⟨Or.inr (Or.inl rfl), hau⟩).2⟩
  · rintro h a ⟨rfl | rfl | rfl, hau⟩
    · exact ⟨Or.inl rfl, (h ⟨Or.inl rfl, hau⟩).2⟩
    · exact ⟨Or.inr (Or.inl rfl), (h ⟨Or.inr rfl, hau⟩).2⟩
    · exact ⟨Or.inr (Or.inr rfl), (h ⟨Or.inl rfl, hau.1⟩).2, (h ⟨Or.inr rfl, hau.2⟩).2⟩

theorem exhMW_or_and (hA : (A \ B).Nonempty) :
    exhMW {A, B, A ∩ B} (A ∪ B) = (A \ B) ∪ (B \ A) :=
  (exhMW_congr (A ∪ B) (satisfied_or_and_subset_iff (A := A) (B := B))).trans (exhMW_or hA)

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
    · refine Or.inl ⟨hmu, fun hpsu ↦ ?_⟩
      have hle : satisfied (· ∈ ·) {m, p, s} w ⊆ satisfied (· ∈ ·) {m, p, s} u := by
        rintro a ⟨rfl | rfl | rfl, haw⟩
        · exact ⟨Or.inl rfl, hmu⟩
        · exact absurd haw hwp
        · exact absurd haw hws
      rcases hpsu with hpu | hsu
      · exact hwp (hmin (Or.inl hwm) hle ⟨Or.inr (Or.inl rfl), hpu⟩).2
      · exact hws (hmin (Or.inl hwm) hle ⟨Or.inr (Or.inr rfl), hsu⟩).2
    · exact Or.inr ⟨hu.resolve_left hmu, hmu⟩
  · rintro (⟨hmu, hpsu⟩ | ⟨⟨hpu, hsu⟩, hmu⟩)
    · refine ⟨Or.inl hmu, fun v hv hle a ⟨ha, hau⟩ ↦ ⟨ha, ?_⟩⟩
      have hmv : v ∈ m :=
        hv.resolve_right fun hpsv ↦ hpsu (Or.inl (hle ⟨Or.inr (Or.inl rfl), hpsv.1⟩).2)
      rcases ha with rfl | rfl | rfl
      · exact hmv
      · exact (hpsu (Or.inl hau)).elim
      · exact (hpsu (Or.inr hau)).elim
    · refine ⟨Or.inr ⟨hpu, hsu⟩, fun v hv hle a ⟨ha, hau⟩ ↦ ⟨ha, ?_⟩⟩
      have hpsv : v ∈ p ∧ v ∈ s := hv.resolve_left fun hmv ↦ hmu (hle ⟨Or.inl rfl, hmv⟩).2
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

theorem eq_of_satisfied_subset_stars {u v : Stars}
    (h : satisfied (· ∈ ·) starsALT u ⊆ satisfied (· ∈ ·) starsALT v) : u = v := by
  induction u using WithTop.recTopCoe with
  | top =>
    induction v using WithTop.recTopCoe with
    | top => rfl
    | coe k =>
      have : ⊤ ∈ atLeast (k + 1) := le_top (a := ((k + 1 : ℕ) : Stars))
      exact absurd (WithTop.coe_le_coe.1 (h ⟨Or.inr ⟨k + 1, rfl⟩, this⟩).2) (by omega)
  | coe n => exact (h ⟨Or.inl ⟨n, rfl⟩, rfl⟩).2.symm

theorem exhMW_stars (n : ℕ) : exhMW starsALT (atLeast n) = atLeast n :=
  Set.Subset.antisymm exhMW_subset fun _ hu ↦
    ⟨hu, fun _ _ hle ↦ by rw [eq_of_satisfied_subset_stars hle]⟩

theorem exhIE_stars (n : ℕ) : exhIE starsALT (atLeast n) = atLeast n :=
  exhIE_eq_of_exhMW_eq (exhMW_stars n)

end Spector2016
