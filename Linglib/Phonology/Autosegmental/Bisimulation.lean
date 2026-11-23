/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree

/-!
# Bisimulation of representations along a tree of tiers

Two representations along a tree of tiers are bisimilar under a relation `R` between their
tokens, `AR.IsBisim T Y Z R`, when related tokens stand on the same tier with the same label and
each child of one is related to a child of the other. Related tokens then reach related tokens
by descending lines (`IsBisim.exists_mem_descendants`), so a slot of one representation reads
what the related slot of the other reads (`IsBisim.reads_iff`). Material that no slot dominates,
such as an autosegment left floating by delinking, plays no part.

## TODO

* Spreading by a change of lines and spreading by a change of values are bisimilar, which is
  `Phonology.FeatureGeometry.reads_linkNode_iff`; so are a representation and its OCP collapse.
* A representation along a tree of tiers is a Kripke model with `AR.children` as its
  accessibility, and `IsBisim` is bisimulation of such models (`Logic/Team/Bisimulation.lean`).
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] {T : ParentTree ι}
  {Y Z : AR τ}

/-- `R` relates tokens of `Y` to tokens of `Z` on the same tier, with the same label, and matches
their children in both directions. -/
structure IsBisim (T : ParentTree ι) (Y Z : AR τ) (R : ι → ℕ → ℕ → Prop) : Prop where
  /-- Related tokens carry the same label. -/
  label : ∀ ⦃j q q'⦄, R j q q' → (Y.word j)[q]? = (Z.word j)[q']?
  /-- A child of a token of `Y` is related to a child of the related token of `Z`. -/
  forth : ∀ ⦃i p p' j q⦄, R i p p' → (j, q) ∈ Y.children T (i, p) →
    ∃ q', (j, q') ∈ Z.children T (i, p') ∧ R j q q'
  /-- A child of a token of `Z` is related to a child of the related token of `Y`. -/
  back : ∀ ⦃i p p' j q'⦄, R i p p' → (j, q') ∈ Z.children T (i, p') →
    ∃ q, (j, q) ∈ Y.children T (i, p) ∧ R j q q'

theorem mem_descendants_succ_of_mem {X : AR τ} {d : ℕ} {v c u : ι × ℕ}
    (hc : c ∈ X.children T v) (hu : u ∈ X.descendants T d c) :
    u ∈ X.descendants T (d + 1) v := by
  rw [descendants]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨c, hc, hu⟩)

theorem IsBisim.exists_mem_descendants {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) (d : ℕ) :
    ∀ {i p p' j q}, R i p p' → (j, q) ∈ Y.descendants T d (i, p) →
      ∃ q', (j, q') ∈ Z.descendants T d (i, p') ∧ R j q q' := by
  induction d with
  | zero =>
    intro i p p' j q hR hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (by simpa [descendants] using hq : (j, q) = (i, p))
    exact ⟨p', by simp [descendants], hR⟩
  | succ d ih =>
    intro i p p' j q hR hq
    rw [descendants, Finset.mem_insert, Finset.mem_biUnion] at hq
    obtain hq | ⟨⟨i₁, p₁⟩, hc, hq⟩ := hq
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      exact ⟨p', mem_descendants_self _ _, hR⟩
    · obtain ⟨p₁', hc', hR'⟩ := h.forth hR hc
      obtain ⟨q', hq', hR''⟩ := ih hR' hq
      exact ⟨q', mem_descendants_succ_of_mem hc' hq', hR''⟩

/-- The converse of a bisimulation is a bisimulation. -/
theorem IsBisim.symm {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) :
    IsBisim T Z Y fun j q' q ↦ R j q q' :=
  ⟨fun _ _ _ hR ↦ (h.label hR).symm, fun _ _ _ _ _ hR hc ↦ h.back hR hc,
    fun _ _ _ _ _ hR hc ↦ h.forth hR hc⟩

/-- Reading does not tell bisimilar slots apart. -/
theorem IsBisim.reads_iff {R : ι → ℕ → ℕ → Prop} (h : IsBisim T Y Z R) {k k' : ℕ}
    (hR : R T.root k k') {j : ι} {b : τ j} : Y.Reads T k j b ↔ Z.Reads T k' j b := by
  have hsymm := h.symm
  constructor
  · rintro ⟨q, -, hq, hb⟩
    obtain ⟨q', hq', hR'⟩ := h.exists_mem_descendants _ hR hq
    have hb' : (Z.word j)[q']? = some b := (h.label hR').symm.trans hb
    exact ⟨q', Finset.mem_range.2 (List.getElem?_eq_some_iff.1 hb').1, hq', hb'⟩
  · rintro ⟨q', -, hq', hb'⟩
    obtain ⟨q, hq, hR'⟩ := hsymm.exists_mem_descendants _ hR hq'
    have hb : (Y.word j)[q]? = some b := (h.label hR').trans hb'
    exact ⟨q, Finset.mem_range.2 (List.getElem?_eq_some_iff.1 hb).1, hq, hb⟩

end Autosegmental.AR
