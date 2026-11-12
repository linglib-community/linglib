/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# OCP-merging collapse of autosegmental representations

Merging melody nodes moves the positions of the melody tier along a monotone map.
`X.repoint m w f` reads melody tier `m` as the word `w`, moves each of its positions `p` to
`f p`, and [carries the links along](##Autosegmental.AR.link_repoint), so a merged node keeps
every line of the nodes merged into it, and a monotone repointing
[preserves the NCC](##Autosegmental.AR.NoCrossing.repoint). `AR.collapse m` is the repointing
that destutters the tier word (`OCP.collapse`) through the run index `runIdx`, merging every run
of identical melody nodes; a melody `Hⁿ` collapses to one `H` linked to `n` timing slots. The
collapse [is OCP-clean](##Autosegmental.AR.isCleanAt_collapse), and collapsing a clean tier
[changes nothing](##Autosegmental.AR.IsCleanAt.collapse_eq). On two tiers the collapse of the
upper tier [repoints each line](##Autosegmental.AR.link_collapse_upper_lower) through the run
index of that tier. Collapsing a realization `(w.map g₀).prod`
merges every run of its melody. Jardine and Heinz instead merge only at the seam of each
concatenation (`Autosegmental/MergeAR.lean`), and the two agree when the primitives are
OCP-clean, as in Jardine's tonal realization.

## References

* [jardine-2019]
* [jardine-heinz-2015]
* [jardine-2016b]
-/

@[expose] public section

namespace Autosegmental

open OCP

/-! ### Repointing a tier -/

section RepointIdx
variable {ι : Type*} [DecidableEq ι] (m : ι)

/-- Positions on tier `m` move along `f`; positions on the other tiers stay. -/
def repointIdx (f : ℕ → ℕ) (i : ι) (p : ℕ) : ℕ := if i = m then f p else p

variable {m} {f : ℕ → ℕ}

@[simp] theorem repointIdx_self (p : ℕ) : repointIdx m f m p = f p := by simp [repointIdx]

@[simp] theorem repointIdx_of_ne {i : ι} (h : i ≠ m) (p : ℕ) : repointIdx m f i p = p := by
  simp [repointIdx, h]

theorem repointIdx_monotone (hf : Monotone f) (i : ι) : Monotone (repointIdx m f i) := by
  unfold repointIdx
  split_ifs
  exacts [hf, monotone_id]

end RepointIdx

namespace AR

section Repoint
variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*} (X : AR τ) (m : ι)
  (w : List (τ m)) {f : ℕ → ℕ} (hf : ∀ p < (X.word m).length, f p < w.length)

/-- `X` with tier `m` read as the word `w` and its positions moved along `f`, the lines
following the positions they join. -/
def repoint : AR τ :=
  X.map (Function.update X.word m w) (repointIdx m f) fun i p hp ↦ by
    unfold repointIdx
    split_ifs with h
    · subst h
      simpa using hf p hp
    · simpa [Function.update_of_ne h] using hp

@[simp] theorem word_repoint_self : (X.repoint m w hf).word m = w := by simp [repoint]

@[simp] theorem word_repoint_of_ne {i : ι} (h : i ≠ m) : (X.repoint m w hf).word i = X.word i := by
  simp [repoint, h]

variable {X m w}

/-- The lines of a repointing are the repointed lines. -/
theorem link_repoint {i j : ι} {r s : ℕ} :
    (X.repoint m w hf).Link i j r s ↔
      ∃ p q, X.Link i j p q ∧ repointIdx m f i p = r ∧ repointIdx m f j q = s :=
  link_map

/-- A monotone repointing preserves the NCC. -/
theorem NoCrossing.repoint (hmono : Monotone f) (h : X.NoCrossing) :
    (X.repoint m w hf).NoCrossing :=
  NoCrossing.map _ _ _ (fun i ↦ (repointIdx_monotone hmono i).monotoneOn _) h

end Repoint

/-! ### The collapse -/

section Collapse
variable {ι : Type*} {τ : ι → Type*} (X : AR τ) (m : ι)

/-- `X` is **OCP-clean** at melody tier `m` when that tier word has no adjacent repeats. -/
def IsCleanAt : Prop := IsClean (X.word m)

variable [DecidableEq ι] [DecidableEq (τ m)]

variable {X m} in
theorem IsCleanAt.repointIdx_runIdx (h : X.IsCleanAt m) {i : ι} {p : ℕ}
    (hp : p < (X.word i).length) : repointIdx m (runIdx (X.word m)) i p = p := by
  rcases eq_or_ne i m with rfl | hi
  · exact (repointIdx_self p).trans (runIdx_clean h hp)
  · exact repointIdx_of_ne hi p

/-- The **OCP-merging collapse** of melody tier `m` merges every run of identical melody nodes,
repointing the tier through its run index. -/
def collapse : AR τ :=
  X.repoint m (OCP.collapse (X.word m)) fun _ hp ↦ runIdx_lt_collapse_length _ hp

@[simp] theorem word_collapse_self : (X.collapse m).word m = OCP.collapse (X.word m) :=
  word_repoint_self ..

@[simp] theorem word_collapse_of_ne {i : ι} (h : i ≠ m) : (X.collapse m).word i = X.word i :=
  word_repoint_of_ne _ _ _ _ h

variable {X m}

theorem link_collapse {i j : ι} {r s : ℕ} :
    (X.collapse m).Link i j r s ↔
      ∃ p q, X.Link i j p q ∧ repointIdx m (runIdx (X.word m)) i p = r ∧
        repointIdx m (runIdx (X.word m)) j q = s :=
  link_repoint _

/-- The collapse is OCP-clean at the collapsed tier. -/
theorem isCleanAt_collapse : (X.collapse m).IsCleanAt m := by
  simpa [IsCleanAt] using isClean_collapse (X.word m)

/-- The collapse preserves the NCC, since it repoints links monotonically. -/
theorem NoCrossing.collapse (h : X.NoCrossing) : (X.collapse m).NoCrossing :=
  h.repoint _ (runIdx_monotone _)

/-- Collapsing a representation that is clean at `m` changes nothing. -/
theorem IsCleanAt.collapse_eq (h : X.IsCleanAt m) : X.collapse m = X := by
  refine ext (funext fun i ↦ ?_) fun i j r s ↦ ?_
  · rcases eq_or_ne i m with rfl | hi
    · exact (word_collapse_self X i).trans h.collapse_eq
    · exact word_collapse_of_ne X m hi
  · rw [link_collapse]
    constructor
    · rintro ⟨p, q, hl, rfl, rfl⟩
      rwa [h.repointIdx_runIdx hl.lt_left, h.repointIdx_runIdx hl.lt_right]
    · intro hl
      exact ⟨r, s, hl, h.repointIdx_runIdx hl.lt_left, h.repointIdx_runIdx hl.lt_right⟩

end Collapse

/-! ### Collapsing the upper tier of a representation on two tiers -/

open Tier in
theorem link_collapse_upper_lower {τ : Tier → Type*} [DecidableEq (τ upper)] {X : AR τ}
    {r s : ℕ} :
    (X.collapse upper).Link upper lower r s ↔
      ∃ p, X.Link upper lower p s ∧ runIdx (X.word upper) p = r := by
  rw [link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : lower ≠ upper)]
  exact ⟨fun ⟨p, q, hl, hr, hs⟩ ↦ ⟨p, hs ▸ hl, hr⟩, fun ⟨p, hl, hr⟩ ↦ ⟨p, s, hl, hr, rfl⟩⟩

end AR

end Autosegmental
