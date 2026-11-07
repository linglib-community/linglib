/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.StrictlyLocal
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Language

/-!
# Tier-based strictly local languages

This file defines the tier-based strictly `k`-local languages. A grammar is a tier, a decidable
set of symbols, with a strictly local grammar read on the projection that erases the symbols off
the tier, so a constraint binds tier-adjacent symbols across any material off it. On the whole
alphabet as tier the grammar is strictly local, so [the class contains the strictly local
languages](##Language.IsStrictlyLocal.toIsTierStrictlyLocal), and star-freeness survives
preimages under erasure, so [the class is star-free](##Language.IsTierStrictlyLocal.isStarFree).
For `2 ≤ k` a language is tier-based strictly `k`-local [exactly when the symbols off some tier
are freely insertable and deletable and the language is closed under suffix substitution across
middles with one projection](##Language.isTierStrictlyLocal_iff_exists_tier).

## Implementation notes

The projection is `List.filter` by the `decide` of the tier, already a `Bool` tier in the sense
of `Language.IsTierBased`. It is padded with `k - 1` boundaries on each side, as in Lambert's
anchored models. Under Heinz, Rawal and Tanner's single boundary, a word whose projection has
fewer than `k - 2` symbols has no `k`-factors and so lies in every language of width `k`.

## Errata

In Heinz, Rawal and Tanner's paper:
* The permitted set of the dissimilation language on p. 60 omits `⋊⋉` as well as `bb` and `cc`,
  so the language excludes the words with no tier symbol.
* Strictly local languages are not closed under prefixes and suffixes (§4.3): their own
  `aa*(b + c)` on p. 59 contains `aab` but neither `aa` nor `b`.

## References

* [heinz-rawal-tanner-2011]
* [mcnaughton-papert-1971]
* [lambert-2023]
-/

@[expose] public section

variable {α : Type*}

/-- A **tier-based strictly local grammar** over `α` is a tier, a decidable set of symbols,
together with a strictly local grammar read on the projection to the tier. The locality width
is an argument of `language`. -/
structure TierStrictlyLocalGrammar (α : Type*) where
  /-- The symbols on the tier; the others are erased before the strictly local test. -/
  tier : α → Prop
  /-- Decidability of the tier, needed to project. -/
  [decTier : DecidablePred tier]
  /-- The permitted factors of the projection. -/
  permitted : StrictlyLocalGrammar α

namespace TierStrictlyLocalGrammar

attribute [instance] decTier

variable {k : ℕ} {G : TierStrictlyLocalGrammar α} {w : List α}

/-- The language generated at width `k` is the preimage, under erasure of the symbols off the
tier, of the strictly `k`-local language of `permitted`. -/
def language (k : ℕ) (G : TierStrictlyLocalGrammar α) : Language α :=
  {w | w.filter (G.tier ·) ∈ G.permitted.language k}

@[simp] lemma mem_language : w ∈ G.language k ↔ w.filter (G.tier ·) ∈ G.permitted.language k :=
  Iff.rfl

theorem mem_language_append_cons_of_not_tier {a : α} (ha : ¬ G.tier a) (u v : List α) :
    u ++ a :: v ∈ G.language k ↔ u ++ v ∈ G.language k := by
  simp [List.filter_append, ha]

end TierStrictlyLocalGrammar

namespace Language

/-- A language is **tier-based strictly `k`-local** when some tier-based strictly local grammar
generates it at width `k`. -/
def IsTierStrictlyLocal (L : Language α) (k : ℕ) : Prop :=
  ∃ G : TierStrictlyLocalGrammar α, G.language k = L

variable {L : Language α} {k : ℕ}

/-! ## Inclusions -/

/-- Strictly local languages are tier-based strictly local ([heinz-rawal-tanner-2011],
Theorem 3), on the tier of the whole alphabet. -/
theorem IsStrictlyLocal.toIsTierStrictlyLocal (h : L.IsStrictlyLocal k) :
    L.IsTierStrictlyLocal k := by
  obtain ⟨G, rfl⟩ := h
  exact ⟨⟨fun _ ↦ True, G⟩, by ext w; simp⟩

/-- A tier-based strictly local language in which every symbol is visible, deleting it from some
string changing membership, is strictly local, since its tier is the whole alphabet. -/
theorem IsTierStrictlyLocal.isStrictlyLocal (h : L.IsTierStrictlyLocal k)
    (hvis : ∀ a, ∃ u v, ¬ (u ++ a :: v ∈ L ↔ u ++ v ∈ L)) : L.IsStrictlyLocal k := by
  obtain ⟨G, rfl⟩ := h
  have htier (a : α) : G.tier a := by
    by_contra ha
    obtain ⟨u, v, huv⟩ := hvis a
    exact huv (G.mem_language_append_cons_of_not_tier ha u v)
  refine ⟨G.permitted, Set.ext fun w ↦ ?_⟩
  rw [TierStrictlyLocalGrammar.mem_language,
    List.filter_eq_self.2 fun a _ ↦ decide_eq_true (htier a)]

/-! ## Lambert's characterization -/

/-- `L` is closed under `T`-preprojective suffix substitution at width `k`
([lambert-2023], Definition 1) when two members whose middles project to one tier string of at
least `k - 1` symbols admit the crossover of their suffixes. -/
def PreprojectiveSuffixSubstitutionClosed (L : Language α) (T : α → Prop) [DecidablePred T]
    (k : ℕ) : Prop :=
  ∀ u₁ x₁ v₁ u₂ x₂ v₂ : List α, x₁.filter (T ·) = x₂.filter (T ·) →
    k - 1 ≤ (x₁.filter (T ·)).length → u₁ ++ x₁ ++ v₁ ∈ L → u₂ ++ x₂ ++ v₂ ∈ L →
      u₁ ++ x₁ ++ v₂ ∈ L

theorem IsTierStrictlyLocal.exists_tier (h : L.IsTierStrictlyLocal k) :
    ∃ (T : α → Prop) (_ : DecidablePred T), (∀ u v a, ¬ T a → (u ++ a :: v ∈ L ↔ u ++ v ∈ L)) ∧
      L.PreprojectiveSuffixSubstitutionClosed T k := by
  obtain ⟨G, rfl⟩ := h
  refine ⟨G.tier, inferInstance, fun u v a ha ↦ G.mem_language_append_cons_of_not_tier ha u v,
    fun u₁ x₁ v₁ u₂ x₂ v₂ hx hlen h₁ h₂ ↦ ?_⟩
  have hSSC := (show (G.permitted.language k).IsStrictlyLocal k from ⟨_, rfl⟩)
    |>.suffixSubstitutionClosed
  rw [TierStrictlyLocalGrammar.mem_language] at h₁ h₂ ⊢
  simp only [List.filter_append] at h₁ h₂ ⊢
  rw [← hx] at h₂
  set p := x₁.filter (G.tier ·)
  have hsplit : p = p.rdrop (k - 1) ++ p.rtake (k - 1) := (List.rdrop_append_rtake _ _).symm
  rw [hsplit] at h₁ h₂ ⊢
  simpa only [List.append_assoc] using
    hSSC (u₁.filter _ ++ p.rdrop (k - 1)) (v₁.filter _)
      (u₂.filter _ ++ p.rdrop (k - 1)) (v₂.filter _) (p.rtake (k - 1))
      (by simp; omega) (by simpa only [List.append_assoc] using h₁)
      (by simpa only [List.append_assoc] using h₂)

/-- **Lambert's characterization of the tier-based strictly local languages**
([lambert-2023], Theorem 1). For `2 ≤ k`, a language is tier-based strictly `k`-local exactly
when some tier has freely insertable and deletable off-tier symbols and closes the language
under preprojective suffix substitution. -/
theorem isTierStrictlyLocal_iff_exists_tier (hk : 2 ≤ k) :
    L.IsTierStrictlyLocal k ↔
      ∃ (T : α → Prop) (_ : DecidablePred T),
        (∀ u v a, ¬ T a → (u ++ a :: v ∈ L ↔ u ++ v ∈ L)) ∧
          L.PreprojectiveSuffixSubstitutionClosed T k := by
  refine ⟨IsTierStrictlyLocal.exists_tier, fun ⟨T, _, hinv, hL⟩ ↦ ?_⟩
  have hfilter (u w : List α) : u ++ w ∈ L ↔ u ++ w.filter (T ·) ∈ L := by
    induction w generalizing u with
    | nil => rfl
    | cons a w ih =>
      by_cases ha : T a
      · simpa [ha] using ih (u ++ [a])
      · simpa [ha] using (hinv u w a ha).trans (ih u)
  let S : Language α := {v | v ∈ L ∧ ∀ a ∈ v, T a}
  have hS : S.IsStrictlyLocal k := by
    refine (isStrictlyLocal_iff_suffixSubstitutionClosed hk).2
      fun u₁ v₁ u₂ v₂ x hx ⟨h₁, h₁T⟩ ⟨h₂, h₂T⟩ ↦ ⟨?_, ?_⟩
    · have hxT : x.filter (T ·) = x := List.filter_eq_self.2 fun a ha ↦
        decide_eq_true (h₁T a (by simp [ha]))
      exact hL u₁ x v₁ u₂ x v₂ rfl (by rw [hxT, hx]) h₁ h₂
    · intro a ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · exact h₁T a (by simp [ha])
      · exact h₁T a (by simp [ha])
      · exact h₂T a (by simp [ha])
  obtain ⟨G, hG⟩ := hS
  refine ⟨⟨T, G⟩, Set.ext fun w ↦ ?_⟩
  rw [TierStrictlyLocalGrammar.mem_language, hG]
  constructor
  · rintro ⟨h, -⟩
    simpa using (hfilter [] w).2 (by simpa using h)
  · intro h
    exact ⟨by simpa using (hfilter [] w).1 (by simpa using h),
      fun a ha ↦ of_decide_eq_true (List.mem_filter.1 ha).2⟩

/-- **Tier-based strictly local languages are star-free** ([heinz-rawal-tanner-2011],
Theorem 6). Over a finite alphabet a tier-based strictly local language is the preimage of a
strictly local language under erasure, and star-freeness survives that preimage. -/
theorem IsTierStrictlyLocal.isStarFree [Finite α] (h : L.IsTierStrictlyLocal k) :
    L.IsStarFree := by
  obtain ⟨G, rfl⟩ := h
  exact (IsStrictlyLocal.isStarFree ⟨G.permitted, rfl⟩).preimage_filter _

end Language
