/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Skeleton
public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# Tangale tone processes and the elision cascade

Tangale has two tonemes, H and L. High Tone Spread links an H at a morpheme or word boundary to
the following tone-bearing unit as well, giving that unit a falling contour, and Left Line
Delinking then erases the original line, so the H shifts one unit rightward. Segmentally, the
elision of a final vowel creates a final consonant cluster that u-epenthesis repairs, which gives
the perfective alternation *pon-go* ~ *pon-ug*: the suffix surfaces faithful at a prosodic
boundary and elided and repaired phrase-medially. Hartmann and Zimmermann read that boundary as
the prosodic reflex of perfective focus, and `boundary_audible` shows that blocking the cascade
is perceptible.

## Main definitions

* `Tone`: the two tonemes.
* `hts`, `lld`: High Tone Spread and Left Line Delinking on a link relation.
* `Phonotactic`, `ve`, `epenthesize`: the cluster constraints, final-vowel elision and
  u-epenthesis on CV skeletons.

## Main results

* `hts_surfacesWith_H`, `lld_hts_shift`: spreading creates the falling contour, and delinking
  shifts the H.
* `boundary_audible`: the boundary and phrase-medial forms differ and both satisfy the cluster
  constraints.

## References

* [kidda-1985]
* [hartmann-zimmermann-2004]
-/

@[expose] public section

namespace Tangale

open Autosegmental

/-- The two Tangale tonemes ([kidda-1985] §1.16). Extralow is a phonetic realization, and
falling contours arise only from spread. -/
inductive Tone where
  | H | L
  deriving DecidableEq, Repr

/-- High Tone Spread ([kidda-1985] (31)) spreads the toneme at `i`, an H linked to TBU `j`
at a morpheme or word boundary, onto the following TBU. -/
def hts (L : Bool → Bool → ℕ → ℕ → Prop) (i j : ℕ) (b b' : Bool) (p q : ℕ) : Prop :=
  L b b' p q ∨ b = true ∧ b' = false ∧ p = i ∧ q = j + 1

/-- Left Line Delinking ([kidda-1985] (35a)) erases the original (left) line
    after the toneme has spread rightward. -/
def lld (L : Bool → Bool → ℕ → ℕ → Prop) (i j : ℕ) (b b' : Bool) (p q : ℕ) : Prop :=
  L b b' p q ∧ ¬ (b = true ∧ b' = false ∧ p = i ∧ q = j)

instance (L : Bool → Bool → ℕ → ℕ → Prop) [∀ b b', DecidableRel (L b b')] (i j : ℕ)
    (b b' : Bool) : DecidableRel (hts L i j b b') :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance (L : Bool → Bool → ℕ → ℕ → Prop) [∀ b b', DecidableRel (L b b')] (i j : ℕ)
    (b b' : Bool) : DecidableRel (lld L i j b b') :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

variable {ws : ∀ b, List (TwoTier Tone Unit b)} {L : Bool → Bool → ℕ → ℕ → Prop}
  [∀ b b', DecidableRel (L b b')]

/-- Spread creates the falling contour (§4.6), since the docked TBU surfaces with H
    on top of whatever it already bore. -/
theorem hts_surfacesWith_H {i j : ℕ} (hH : (ws true)[i]? = some Tone.H)
    (hj : j + 1 < (ws false).length) :
    (AR.fromRel ws (hts L i j)).SurfacesWith Tone.H (j + 1) := by
  rcases List.getElem?_eq_some_iff.mp hH with ⟨hi, -⟩
  exact ⟨i, AR.link_fromRel.mpr ⟨by decide, hi, hj, .inl (.inr ⟨rfl, rfl, rfl, rfl⟩)⟩, hH⟩

/-- Spread followed by Left Line Delinking shifts the H one TBU rightward
    ((34)), as the docked TBU keeps the new line and the source loses the
    original. -/
theorem lld_hts_shift {i j : ℕ} (hH : (ws true)[i]? = some Tone.H)
    (hj : j + 1 < (ws false).length) (hne : j + 1 ≠ j)
    (hor : ∀ p q, ¬ L false true p q) :
    (AR.fromRel ws (lld (hts L i j) i j)).SurfacesWith Tone.H (j + 1) ∧
      ¬ (AR.fromRel ws (lld (hts L i j) i j)).Link true false i j := by
  rcases List.getElem?_eq_some_iff.mp hH with ⟨hi, -⟩
  constructor
  · refine ⟨i, AR.link_fromRel.mpr
      ⟨by decide, hi, hj, .inl ⟨.inr ⟨rfl, rfl, rfl, rfl⟩, ?_⟩⟩, hH⟩
    rintro ⟨-, -, -, h⟩
    exact hne h
  · rintro h
    rcases AR.link_fromRel.mp h with
      ⟨-, -, -, ⟨-, hno⟩ | ⟨hraw | ⟨hfalse, -⟩, -⟩⟩
    · exact hno ⟨rfl, rfl, rfl, rfl⟩
    · exact hor _ _ hraw
    · exact absurd hfalse (by decide)

/-! ### The elision cascade (Ch. 2)

Final-vowel elision builds consonant clusters; the cluster
constraints then force u-epenthesis. On the perfective suffix this
yields [kidda-1985]'s (4a) alternation `pón-é + gó → pon-go`
(clause-final, faithful) vs `pon-ug` (phrase-medial, elided and
repaired) — the alternation whose blocking under focus is
[hartmann-zimmermann-2004]'s prosodic reflex. -/

/-- The cluster constraints ([kidda-1985] p. 64) ban initial clusters, medial three-consonant
clusters, and word-final clusters. -/
def Phonotactic (w : Skeleton) : Prop :=
  ¬ [Slot.C, Slot.C] <+: w ∧
  ¬ [Slot.C, Slot.C, Slot.C] <:+: w ∧
  ¬ [Slot.C, Slot.C] <:+ w

instance (w : Skeleton) : Decidable (Phonotactic w) :=
  inferInstanceAs (Decidable (¬ _ ∧ ¬ _ ∧ ¬ _))

/-- Final-vowel elision (§2.2) deletes a word-final vowel. It is triggered by suffixation,
compounding, and phrase-medial position, and blocked at a prosodic boundary. -/
def ve (w : Skeleton) : Skeleton :=
  if w.getLast? = some Slot.V then w.dropLast else w

/-- u-epenthesis ((4)) repairs a word-final cluster by inserting the vowel between the
penultimate and ultimate consonants. -/
def epenthesize (w : Skeleton) : Skeleton :=
  if [Slot.C, Slot.C] <:+ w then w.dropLast ++ [Slot.V, Slot.C] else w

/-- *pón-é* 'knew' ((4a)). -/
def ponE : Skeleton := [.C, .V, .C, .V]
/-- The perfective suffix *gó*. -/
def go : Skeleton := [.C, .V]

/-- The boundary form has word-internal elision only, so the suffix surfaces faithful
(*pon-go*; before a focused constituent, *wai-gó lánda* of [hartmann-zimmermann-2004] (25)). -/
def blockedForm : Skeleton := ve ponE ++ go

/-- In the phrase-medial form, phrasal elision hits the suffix vowel and epenthesis repairs
the final cluster (*pon-ug ŋâi* 'knew Ngai'). -/
def elidedForm : Skeleton := epenthesize (ve (ve ponE ++ go))

/-- The cascade is audible. Both outputs are phonotactically licit and they differ, so blocking
phrasal elision (the prosodic boundary of the perfective focus reflex) is perceptible. -/
theorem boundary_audible :
    blockedForm ≠ elidedForm ∧
    Phonotactic blockedForm ∧ Phonotactic elidedForm := by decide

end Tangale
