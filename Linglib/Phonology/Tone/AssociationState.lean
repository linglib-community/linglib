/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Basic
public import Linglib.Phonology.Autosegmental.OCP
public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Tone.Basic

/-!
# Words of tone-bearing units

Jardine's string rendering of a tonal word records, for each tone-bearing unit, whether it is
associated to an H tone (`H`) or unassociated (`O`, his Ø). A word over these two letters is its
length together with [its set of high positions](##Tone.eq_of_highs_eq), so a length-preserving
map on such words is an operation on sets of positions. The word reads back into a two-tier
autosegmental representation by `AssociationState.toAR`.

## References

* [jardine-2016a]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Tone

/-! ### The tone-bearing-unit alphabet -/

/-- A tone-bearing unit's association state is `H` for a TBU associated to a H tone and `O`
for an unspecified TBU (Jardine's Ø). -/
inductive AssociationState | H | O
  deriving DecidableEq, Repr

instance : Fintype AssociationState := ⟨{.H, .O}, fun a ↦ by cases a <;> decide⟩

/-- The positions of a word that are associated to an H tone. -/
def highs (w : List AssociationState) : Set ℕ := {i | w[i]? = some .H}

@[simp] theorem mem_highs {w : List AssociationState} {i : ℕ} : i ∈ highs w ↔ w[i]? = some .H :=
  Iff.rfl

/-- A word is determined by its length and its high positions. -/
theorem eq_of_highs_eq {w w' : List AssociationState} (hl : w.length = w'.length)
    (h : highs w = highs w') : w = w' := by
  refine List.ext_getElem hl fun i h₁ h₂ ↦ ?_
  have hi : w[i]? = some .H ↔ w'[i]? = some .H := Set.ext_iff.mp h i
  rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at hi
  cases hw : w[i] <;> cases hw' : w'[i] <;> simp_all

theorem eq_replicate_O_iff {w : List AssociationState} :
    w = List.replicate w.length .O ↔ .H ∉ w :=
  ⟨fun h hH ↦ by rw [h] at hH; simp at hH, fun h ↦ List.eq_replicate_iff.mpr
    ⟨rfl, fun b hb ↦ by cases b; exacts [absurd hb h, rfl]⟩⟩

/-! ### Words as representations

A word reads back into a two-tier autosegmental representation, one timing slot per unit. -/

open Autosegmental

namespace AssociationState

/-- A TBU contributes its H tone to the melody if it is H-toned, and nothing otherwise. -/
def melody : AssociationState → List TRN
  | .H => [.H]
  | .O => []

@[simp] theorem melody_H : melody .H = [.H] := rfl

@[simp] theorem melody_O : melody .O = [] := rfl

theorem length_melody (a : AssociationState) : (melody a).length = if a = .H then 1 else 0 := by
  cases a <;> rfl

theorem sum_length_melody (w : List AssociationState) :
    (w.map fun a => (melody a).length).sum = w.count .H := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, Nat.add_comm]

/-- A TBU translates into the primitive with one timing slot carrying the TBU's melody
(Jardine's reading of the string as a representation). -/
def toAR (a : AssociationState) : AR (TwoTier TRN Unit) := AR.primitive (melody a) ()

@[simp] theorem word_toAR_upper (a : AssociationState) : (toAR a).word .upper = melody a := rfl

@[simp] theorem word_toAR_lower (a : AssociationState) : (toAR a).word .lower = [()] := rfl

@[simp] theorem link_toAR (a : AssociationState) (p q : ℕ) :
    (toAR a).Link .upper .lower p q ↔ p < (melody a).length ∧ q = 0 := by
  simp [toAR]

@[simp] theorem word_prod_map_toAR_upper (w : List AssociationState) :
    (w.map toAR).prod.word .upper = List.replicate (w.count .H) TRN.H := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, List.replicate_succ]

@[simp] theorem word_prod_map_toAR_lower (w : List AssociationState) :
    (w.map toAR).prod.word .lower = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, List.replicate_succ]

theorem link_prod_map_toAR (w : List AssociationState) (p j : ℕ) :
    (w.map toAR).prod.Link .upper .lower p j ↔
      p = (w.take j).count .H ∧ w[j]? = some .H := by
  have hoff : AR.tierOffset toAR .upper w j = (w.take j).count .H := by
    simp only [AR.tierOffset, word_toAR_upper, sum_length_melody]
  rw [AR.link_prod_map_of_length_eq_one toAR fun _ ↦ rfl]
  simp only [link_toAR, hoff, and_true, length_melody, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hj, hle, hlt⟩
    split_ifs at hlt with h
    · exact ⟨by omega, hj, h⟩
    · omega
  · rintro ⟨rfl, hj, h⟩
    exact ⟨hj, le_rfl, by simp [h]⟩

theorem link_collapse_prod_map_toAR (w : List AssociationState) (k j : ℕ) :
    ((w.map toAR).prod.collapse .upper).Link .upper .lower k j ↔ k = 0 ∧ w[j]? = some .H := by
  rw [AR.link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : Tier.lower ≠ Tier.upper),
    link_prod_map_toAR, word_prod_map_toAR_upper, OCP.runIdx_replicate]
  constructor
  · rintro ⟨p, q, ⟨-, h⟩, rfl, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨_, j, ⟨rfl, h⟩, rfl, rfl⟩

end AssociationState

end Tone
