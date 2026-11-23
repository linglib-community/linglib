/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.SuccPred.Tree
public import Linglib.Phonology.Autosegmental.Edit
public import Linglib.Phonology.Autosegmental.Realization
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Spreading a tier

Spreading a tier from the `m`th symbol of a realization onto the `n`th is a change of lines,
`AR.spreadTier`: the token of the `n`th symbol on the tier above is delinked from its own token
and linked to that of the `m`th (`link_spreadTier`). When the primitives have at most one token
on the two tiers, the result has no crossing lines exactly when no symbol strictly between the
two has a line between those tiers (`noCrossing_spreadTier_iff`): a symbol with a token there
blocks, and one without is transparent.

## References

* [sagey-1986]
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [DecidableEq ι] (T : ParentTree ι)

variable {S : Type*} (g₀ : S → AR τ) {w : List S} {j : ι} {m n : ℕ}

/-- Spreading tier `j` from the `m`th symbol of a realization onto the `n`th: the token of the
`n`th symbol on the tier above `j` is delinked from its own token on `j` and linked to that of
the `m`th symbol. -/
def spreadTier (w : List S) (j : ι) (m n : ℕ) : AR τ :=
  ((w.map g₀).prod.eraseLine (T.parent j) j (tierOffset g₀ (T.parent j) w n)
      (tierOffset g₀ j w n)).addLine
    (T.parent j) j (tierOffset g₀ (T.parent j) w n) (tierOffset g₀ j w m)


/-- Spreading a tier crosses no line exactly when no symbol strictly between the two has a line
between that tier and the one above it. -/
theorem noCrossing_spreadTier_iff (hj : j ≠ T.root)
    (hp : ∀ s, ((g₀ s).word (T.parent j)).length ≤ 1) (hc : ∀ s, ((g₀ s).word j).length ≤ 1)
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ []) (hw : (w.map g₀).prod.NoCrossing) :
    (spreadTier T g₀ w j m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ (g₀ w[k]).Link (T.parent j) j 0 0 := by
  have hij : T.parent j ≠ j := fun h ↦ hj (T.eq_root_of_iterate_eq (n := 1) one_ne_zero h)
  have huIoo : ∀ k, k ∈ Set.uIoo m n ↔ m < k ∧ k < n ∨ n < k ∧ k < m := fun k ↦ by
    simp only [Set.uIoo, Set.mem_Ioo, inf_lt_iff, lt_sup_iff]
    omega
  have hX : ∀ {p q}, (w.map g₀).prod.Link (T.parent j) j p q ↔ ∃ k, ∃ hk : k < w.length,
      p = tierOffset g₀ (T.parent j) w k ∧ q = tierOffset g₀ j w k ∧
        (g₀ w[k]).Link (T.parent j) j 0 0 := link_prod_map_of_length_le_one hp hc
  have mono := fun i ↦ tierOffset_mono g₀ i w
  have strict : ∀ {i : ι} {k k' : ℕ} (hk : k < w.length), k < k' → (g₀ w[k]).word i ≠ [] →
      tierOffset g₀ i w k < tierOffset g₀ i w k' := fun {i k k'} hk hlt hne ↦
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (List.length_pos_iff.2 hne))
      (tierOffset_add_length_le g₀ i w hlt hk)
  have hpn : tierOffset g₀ (T.parent j) w n < ((w.map g₀).prod.word (T.parent j)).length := by
    rw [← tierOffset_length]
    exact strict hn hn hnp
  have hqm : tierOffset g₀ j w m < ((w.map g₀).prod.word j).length := by
    rw [← tierOffset_length]
    exact strict hm hm hmj
  have hZ : ∀ {i' j' p q}, (spreadTier T g₀ w j m n).Link i' j' p q ↔
      ((w.map g₀).prod.Link i' j' p q ∧
        ¬ (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w n) ∧
        ¬ (i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w n ∧
          q = tierOffset g₀ (T.parent j) w n)) ∨
      (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w m ∨
        i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w m ∧
          q = tierOffset g₀ (T.parent j) w n) := by
    intro i' j' p q
    rw [spreadTier, link_addLine, link_eraseLine, word_eraseLine]
    exact or_congr_right
      ((and_iff_right hij).trans ((and_iff_right hpn).trans (and_iff_right hqm)))
  constructor
  · intro hnc k hk hkmn hl
    have hki : (g₀ w[k]).word (T.parent j) ≠ [] := List.ne_nil_of_length_pos hl.lt_left
    have hkj : (g₀ w[k]).word j ≠ [] := List.ne_nil_of_length_pos hl.lt_right
    have nc := isNonCrossing_lines_iff.1 (hnc (T.parent j) j)
    have hnew : (spreadTier T g₀ w j m n).Link (T.parent j) j
        (tierOffset g₀ (T.parent j) w n) (tierOffset g₀ j w m) :=
      hZ.2 (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    rcases (huIoo k).1 hkmn with ⟨hmk, hkn⟩ | ⟨hnk, hkm⟩
    · have hold : (spreadTier T g₀ w j m n).Link (T.parent j) j
          (tierOffset g₀ (T.parent j) w k) (tierOffset g₀ j w k) :=
        hZ.2 (.inl ⟨hX.2 ⟨k, hk, rfl, rfl, hl⟩, fun h ↦ (strict hk hkn hki).ne h.2.2.1,
          fun h ↦ hij h.1⟩)
      exact absurd (nc hold hnew (strict hk hkn hki)) (not_le.2 (strict hm hmk hmj))
    · have hold : (spreadTier T g₀ w j m n).Link (T.parent j) j
          (tierOffset g₀ (T.parent j) w k) (tierOffset g₀ j w k) :=
        hZ.2 (.inl ⟨hX.2 ⟨k, hk, rfl, rfl, hl⟩, fun h ↦ (strict hn hnk hnp).ne' h.2.2.1,
          fun h ↦ hij h.1⟩)
      exact absurd (nc hnew hold (strict hn hnk hnp)) (not_le.2 (strict hk hkm hkj))
  · intro hR i' j'
    refine isNonCrossing_lines_iff.2 fun p q p' q' h₁ h₂ hlt ↦ ?_
    have key₁ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ (T.parent j) w k < tierOffset g₀ (T.parent j) w n →
          tierOffset g₀ j w k ≤ tierOffset g₀ j w m := fun {k} hk hl h ↦ by
      have hkn : k < n := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hmk ↦ hR k hk ((huIoo k).2 (.inl ⟨hmk, hkn⟩)) hl)
    have key₂ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ (T.parent j) w n < tierOffset g₀ (T.parent j) w k →
          tierOffset g₀ j w m ≤ tierOffset g₀ j w k := fun {k} hk hl h ↦ by
      have hnk : n < k := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hkm ↦ hR k hk ((huIoo k).2 (.inr ⟨hnk, hkm⟩)) hl)
    have key₃ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ j w k < tierOffset g₀ j w m →
          tierOffset g₀ (T.parent j) w k ≤ tierOffset g₀ (T.parent j) w n := fun {k} hk hl h ↦ by
      have hkm : k < m := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hnk ↦ hR k hk ((huIoo k).2 (.inr ⟨hnk, hkm⟩)) hl)
    have key₄ : ∀ {k} (hk : k < w.length), (g₀ w[k]).Link (T.parent j) j 0 0 →
        tierOffset g₀ j w m < tierOffset g₀ j w k →
          tierOffset g₀ (T.parent j) w n ≤ tierOffset g₀ (T.parent j) w k := fun {k} hk hl h ↦ by
      have hmk : m < k := lt_of_not_ge fun hge ↦ absurd (mono _ hge) (not_le.2 h)
      exact mono _ (le_of_not_gt fun hkn ↦ hR k hk ((huIoo k).2 (.inl ⟨hmk, hkn⟩)) hl)
    rcases hZ.1 h₁ with ⟨hx₁, -, -⟩ | ⟨hi₁, hj₁, hp₁, hq₁⟩ | ⟨hi₁, hj₁, hp₁, hq₁⟩ <;>
      rcases hZ.1 h₂ with ⟨hx₂, -, -⟩ | ⟨hi₂, hj₂, hp₂, hq₂⟩ | ⟨hi₂, hj₂, hp₂, hq₂⟩
    · exact isNonCrossing_lines_iff.1 (hw i' j') hx₁ hx₂ hlt
    · subst hi₂ hj₂ hp₂ hq₂
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₁
      exact key₁ hk hl hlt
    · subst hi₂ hj₂ hp₂ hq₂
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₁.symm
      exact key₃ hk hl hlt
    · subst hi₁ hj₁ hp₁ hq₁
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₂
      exact key₂ hk hl hlt
    · subst hp₁ hp₂
      exact absurd hlt (lt_irrefl _)
    · exact absurd (hi₁.symm.trans hi₂) hij
    · subst hi₁ hj₁ hp₁ hq₁
      obtain ⟨k, hk, rfl, rfl, hl⟩ := hX.1 hx₂.symm
      exact key₄ hk hl hlt
    · exact absurd (hi₂.symm.trans hi₁) hij
    · subst hp₁ hp₂
      exact absurd hlt (lt_irrefl _)


theorem link_spreadTier (hj : j ≠ T.root) (hm : m < w.length)
    (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ []) (hnp : (g₀ w[n]).word (T.parent j) ≠ [])
    {i' j' : ι} {p q : ℕ} :
    (spreadTier T g₀ w j m n).Link i' j' p q ↔
      ((w.map g₀).prod.Link i' j' p q ∧
        ¬ (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w n) ∧
        ¬ (i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w n ∧
          q = tierOffset g₀ (T.parent j) w n)) ∨
      (i' = T.parent j ∧ j' = j ∧ p = tierOffset g₀ (T.parent j) w n ∧
          q = tierOffset g₀ j w m ∨
        i' = j ∧ j' = T.parent j ∧ p = tierOffset g₀ j w m ∧
          q = tierOffset g₀ (T.parent j) w n) := by
  have hij : T.parent j ≠ j := fun h ↦ hj (T.eq_root_of_iterate_eq (n := 1) one_ne_zero h)
  rw [spreadTier, link_addLine, link_eraseLine, word_eraseLine]
  exact or_congr_right ((and_iff_right hij).trans
    ((and_iff_right (tierOffset_lt_length g₀ _ w hn hnp)).trans
      (and_iff_right (tierOffset_lt_length g₀ _ w hm hmj))))


end Autosegmental.AR
