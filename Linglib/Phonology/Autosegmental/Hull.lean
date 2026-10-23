/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# The association hull

`AR.hull m` closes each node of melody tier `m` to the interval hull of its links on every
other tier: a melody node links to a position iff that position lies between two of its
links. Applied after OCP fusion, the hull of the fused H's links is the plateau of
Hyman and Katamba's plateauing rule (`Phonology/Tone/Plateauing`). The hull of a melody
with several nodes can violate the No-Crossing Constraint, since two interleaved hulls cross;
the rule applies to the fused representation, whose melody is a single node.

## Main results

* `AR.link_hull_left`: a melody node links to the positions between two of its links.
* `AR.link_subset_hull`: the hull extends the link relation.
* `AR.link_hull_convex`: each melody node's links form an interval.

## References

* [hyman-katamba-2010]
-/

@[expose] public section

namespace Autosegmental

namespace AR

variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*} (m : ι) (X : AR τ)

/-- The hull closes each tier-`m` node's association set to its interval hull on each
other tier. -/
def hull : AR τ :=
  fromRel X.word fun i j p q ↦
    (i = m ∧ ∃ q₁ < (X.word j).length, ∃ q₂ < (X.word j).length,
      X.Link i j p q₁ ∧ X.Link i j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂) ∨ (i ≠ m ∧ j ≠ m ∧ X.Link i j p q)

@[simp] theorem word_hull : (X.hull m).word = X.word := rfl

theorem link_hull_left {j : ι} (hj : m ≠ j) {p q : ℕ} (hq : q < (X.word j).length) :
    (X.hull m).Link m j p q ↔
      ∃ q₁ q₂, X.Link m j p q₁ ∧ X.Link m j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂ := by
  rw [hull, link_fromRel]
  constructor
  · rintro ⟨-, -, -, (⟨-, q₁, -, q₂, -, hfl⟩ | ⟨hne, -, -⟩) | (⟨rfl, -⟩ | ⟨-, hne, -⟩)⟩
    · exact ⟨q₁, q₂, hfl⟩
    · exact absurd rfl hne
    · exact absurd rfl hj
    · exact absurd rfl hne
  · rintro ⟨q₁, q₂, h₁, h₂, hle₁, hle₂⟩
    exact ⟨hj, h₁.lt_left, hq,
      .inl (.inl ⟨rfl, q₁, h₁.lt_right, q₂, h₂.lt_right, h₁, h₂, hle₁, hle₂⟩)⟩

theorem link_hull_of_ne {i j : ι} (hi : i ≠ m) (hj : j ≠ m) (p q : ℕ) :
    (X.hull m).Link i j p q ↔ X.Link i j p q := by
  rw [hull, link_fromRel]
  constructor
  · rintro ⟨-, -, -, (⟨rfl, -⟩ | ⟨-, -, hl⟩) | (⟨rfl, -⟩ | ⟨-, -, hl⟩)⟩
    · exact absurd rfl hi
    · exact hl
    · exact absurd rfl hj
    · exact hl.symm
  · intro hl
    exact ⟨hl.ne, hl.lt_left, hl.lt_right, .inl (.inr ⟨hi, hj, hl⟩)⟩

theorem link_subset_hull {i j : ι} {p q : ℕ} (h : X.Link i j p q) : (X.hull m).Link i j p q := by
  rcases eq_or_ne m i with rfl | hi
  · rcases eq_or_ne m j with rfl | hj
    · exact absurd rfl h.ne
    · exact (X.link_hull_left m hj h.lt_right).mpr ⟨q, q, h, h, le_rfl, le_rfl⟩
  · rcases eq_or_ne m j with rfl | hj
    · exact ((X.link_hull_left m hi h.lt_left).mpr ⟨p, p, h.symm, h.symm, le_rfl, le_rfl⟩).symm
    · exact (X.link_hull_of_ne m (Ne.symm hi) (Ne.symm hj) p q).mpr h

theorem link_hull_convex {j : ι} (hj : m ≠ j) {p q₁ q q₂ : ℕ} (hq : q < (X.word j).length)
    (h₁ : (X.hull m).Link m j p q₁) (h₂ : (X.hull m).Link m j p q₂)
    (hle₁ : q₁ ≤ q) (hle₂ : q ≤ q₂) : (X.hull m).Link m j p q := by
  obtain ⟨a₁, -, ha₁, -, hle₃, -⟩ := (X.link_hull_left m hj h₁.lt_right).mp h₁
  obtain ⟨-, a₂, -, ha₂, -, hle₄⟩ := (X.link_hull_left m hj h₂.lt_right).mp h₂
  exact (X.link_hull_left m hj hq).mpr ⟨a₁, a₂, ha₁, ha₂, by omega, by omega⟩

end AR

end Autosegmental
