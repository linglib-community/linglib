/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.KripkeModel.Basic
public import Linglib.Phonology.Autosegmental.OCP
public import Linglib.Phonology.Autosegmental.TierTree.TwoTier

/-!
# The OCP-merging collapse as a bisimulation

The OCP-merging collapse of a tier that no tier hangs from is bisimilar to the representation,
each position related to its run index (`exists_isBisimulation_collapse`), so it changes the
labels no slot bears (`mem_melody_collapse_iff`). On two tiers, collapsing the autosegments
changes what no slot surfaces with (`surfacesWith_collapse_upper_iff`).

## References

* [jardine-2019]
* [mccarthy-1981]
-/

@[expose] public section

open ModalLogic

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] {T : ParentTree ι}
  {X Y Z : AR τ}

section Collapse

open OCP

variable {m : ι} [DecidableEq (τ m)]

/-- Collapsing a tier that no tier hangs from is bisimilar to the representation, each
position to its run index. -/
theorem exists_isBisimulation_collapse (hm : ∀ t, t ≠ T.root → T.parent t ≠ m) :
    ∃ r, (X.toKripkeModel T).IsBisimulation ((X.collapse m).toKripkeModel T) r ∧
      ∀ k < (X.word T.root).length,
        r (T.root, k) (T.root, repointIdx m (runIdx (X.word m)) T.root k) := by
  refine ⟨_, isBisimulation_toKripkeModel (R := fun i p p' ↦ p < (X.word i).length ∧
    p' = repointIdx m (runIdx (X.word m)) i p) ?_ ?_ ?_,
    fun k hk ↦ ⟨T.root, k, _, rfl, rfl, hk, rfl⟩⟩
  · rintro j q _ ⟨hq, rfl⟩
    rcases eq_or_ne j m with rfl | hj
    · rw [repointIdx_self, word_collapse_self, getElem?_collapse_runIdx hq]
    · rw [repointIdx_of_ne hj, word_collapse_of_ne _ _ hj]
  · rintro i p _ j q ⟨hp, rfl⟩ hc
    obtain ⟨hpar, hr, hl⟩ := mem_children.1 hc
    exact ⟨_, mem_children.2 ⟨hpar, hr, link_collapse.2 ⟨p, q, hl, rfl, rfl⟩⟩, hl.lt_right, rfl⟩
  · rintro i p _ j q' ⟨hp, rfl⟩ hc
    obtain ⟨hpar, hr, hl⟩ := mem_children.1 hc
    obtain rfl : T.parent j = i := hpar
    replace hl : (X.collapse m).Link (T.parent j) j
      (repointIdx m (runIdx (X.word m)) (T.parent j) p) q' := hl
    obtain ⟨p₀, q₀, hl₀, hp₀, rfl⟩ := link_collapse.1 hl
    have hi := hm j hr
    rw [repointIdx_of_ne hi, repointIdx_of_ne hi] at hp₀
    subst hp₀
    exact ⟨q₀, mem_children.2 ⟨rfl, hr, hl₀⟩, hl₀.lt_right, rfl⟩

/-- Collapsing a tier that no tier hangs from changes the labels no slot bears. -/
theorem mem_melody_collapse_iff (hm : ∀ t, t ≠ T.root → T.parent t ≠ m) (hroot : m ≠ T.root)
    {k : ℕ} {j : ι} {b : τ j} : b ∈ (X.collapse m).melody T k j ↔ b ∈ X.melody T k j := by
  obtain ⟨r, hB, hr⟩ := exists_isBisimulation_collapse (X := X) hm
  by_cases hk : k < (X.word T.root).length
  · have h := hr k hk
    rw [repointIdx_of_ne (Ne.symm hroot)] at h
    exact (hB.mem_melody_iff h).symm
  · exact iff_of_false
      (notMem_melody_of_length_le
        (by rw [word_collapse_of_ne _ _ (Ne.symm hroot)]; exact not_lt.1 hk))
      (notMem_melody_of_length_le (not_lt.1 hk))

end Collapse

section TwoTier

open Tier

universe u

variable {α β : Type u} [DecidableEq α] {X : AR (TwoTier α β)} {a : α} {j : ℕ}

/-- Collapsing the autosegments changes what no slot surfaces with. -/
theorem surfacesWith_collapse_upper_iff :
    (X.collapse upper).SurfacesWith a j ↔ X.SurfacesWith a j := by
  rw [← mem_melody_twoTier_upper_iff, ← mem_melody_twoTier_upper_iff]
  exact mem_melody_collapse_iff (fun _ _ ↦ (by decide : lower ≠ upper)) (by decide)

end TwoTier

end Autosegmental.AR
