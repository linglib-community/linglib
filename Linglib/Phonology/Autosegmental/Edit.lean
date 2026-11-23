/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Adding and erasing association lines

`X.addLine i j p q` is the representation `X` with one more line, from position `p` of tier `i`
to position `q` of tier `j`, and `X.eraseLine i j p q` is `X` without that line. Both keep the
words of `X`, and `link_addLine` and `link_eraseLine` say which lines the results have. Spreading
an autosegment is an `addLine`, delinking an `eraseLine`.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} {X : AR τ}

section Edit

variable [DecidableEq ι] (X) (i j : ι) (p q : ℕ)

/-- The representation with one more line, from position `p` of tier `i` to position `q` of tier
`j`; a line out of range or within a tier is not added. -/
def addLine : AR τ :=
  fromRel X.word fun i' j' p' q' ↦ X.Link i' j' p' q' ∨ (i' = i ∧ j' = j ∧ p' = p ∧ q' = q)

/-- The representation without the line from position `p` of tier `i` to position `q` of tier
`j`. -/
def eraseLine : AR τ :=
  fromRel X.word fun i' j' p' q' ↦ X.Link i' j' p' q' ∧
    ¬ (i' = i ∧ j' = j ∧ p' = p ∧ q' = q) ∧ ¬ (i' = j ∧ j' = i ∧ p' = q ∧ q' = p)

@[simp] theorem word_addLine : (X.addLine i j p q).word = X.word := rfl

@[simp] theorem word_eraseLine : (X.eraseLine i j p q).word = X.word := rfl

variable {X i j p q} {i' j' : ι} {p' q' : ℕ}

theorem link_addLine : (X.addLine i j p q).Link i' j' p' q' ↔ X.Link i' j' p' q' ∨
    i ≠ j ∧ p < (X.word i).length ∧ q < (X.word j).length ∧
      (i' = i ∧ j' = j ∧ p' = p ∧ q' = q ∨ i' = j ∧ j' = i ∧ p' = q ∧ q' = p) := by
  simp only [addLine, link_fromRel]
  constructor
  · rintro ⟨hne, hp, hq, (h | ⟨rfl, rfl, rfl, rfl⟩) | (h | ⟨rfl, rfl, rfl, rfl⟩)⟩
    · exact .inl h
    · exact .inr ⟨hne, hp, hq, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact .inl h.symm
    · exact .inr ⟨hne.symm, hq, hp, .inr ⟨rfl, rfl, rfl, rfl⟩⟩
  · rintro (h | ⟨hne, hp, hq, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩)
    · exact ⟨h.ne, h.lt_left, h.lt_right, .inl (.inl h)⟩
    · exact ⟨hne, hp, hq, .inl (.inr ⟨rfl, rfl, rfl, rfl⟩)⟩
    · exact ⟨hne.symm, hq, hp, .inr (.inr ⟨rfl, rfl, rfl, rfl⟩)⟩

theorem link_eraseLine : (X.eraseLine i j p q).Link i' j' p' q' ↔ X.Link i' j' p' q' ∧
    ¬ (i' = i ∧ j' = j ∧ p' = p ∧ q' = q) ∧ ¬ (i' = j ∧ j' = i ∧ p' = q ∧ q' = p) := by
  simp only [eraseLine, link_fromRel]
  constructor
  · rintro ⟨-, -, -, ⟨h, h₁, h₂⟩ | ⟨h, h₁, h₂⟩⟩
    · exact ⟨h, h₁, h₂⟩
    · exact ⟨h.symm, fun ⟨a, b, c, d⟩ ↦ h₂ ⟨b, a, d, c⟩, fun ⟨a, b, c, d⟩ ↦ h₁ ⟨b, a, d, c⟩⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨h.ne, h.lt_left, h.lt_right, .inl ⟨h, h₁, h₂⟩⟩

end Edit

end Autosegmental.AR
