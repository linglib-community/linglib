/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.Form

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
melody is computed on forms: `Form.collapse`
[presents it](##Autosegmental.Form.toAR_collapse). Collapsing a realization `(w.map g₀).prod`
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

universe u

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

/-! ### Collapsing the melody of a representation on two tiers -/

theorem link_collapse_true_false {α β : Type u} [DecidableEq α] [DecidableEq β]
    {X : AR (TwoTier α β)} {r s : ℕ} :
    (X.collapse true).Link true false r s ↔
      ∃ p, X.Link true false p s ∧ runIdx (X.word true) p = r := by
  rw [link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : false ≠ true)]
  exact ⟨fun ⟨p, q, hl, hr, hs⟩ ↦ ⟨p, hs ▸ hl, hr⟩, fun ⟨p, hl, hr⟩ ↦ ⟨p, s, hl, hr, rfl⟩⟩

end AR

namespace Form

variable {α β : Type*} [DecidableEq α] (f : Form α β)

/-- The OCP merge of a form destutters its upper tier and repoints each line through the run
index, so a merged autosegment keeps every line of the autosegments merged into it. -/
def collapse : Form α β where
  upper := OCP.collapse f.upper
  lower := f.lower
  lines := f.lines.image (Prod.map (runIdx f.upper) id)
  lt_of_mem_lines h := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
    exact ⟨runIdx_lt_collapse_length _ (f.lt_of_mem_lines hp).1, (f.lt_of_mem_lines hp).2⟩

@[simp] theorem upper_collapse : f.collapse.upper = OCP.collapse f.upper := rfl

@[simp] theorem lower_collapse : f.collapse.lower = f.lower := rfl

theorem mem_lines_collapse {r s : ℕ} :
    (r, s) ∈ f.collapse.lines ↔ ∃ p, (p, s) ∈ f.lines ∧ runIdx f.upper p = r := by
  simp only [collapse, Finset.mem_image, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
  exact ⟨fun ⟨p, q, h, hr, hs⟩ ↦ ⟨p, hs ▸ h, hr⟩, fun ⟨p, h, hr⟩ ↦ ⟨p, s, h, hr, rfl⟩⟩

/-- The merged form presents the collapse of the presented representation. -/
theorem toAR_collapse {α β : Type u} [DecidableEq α] [DecidableEq β] (f : Form α β) :
    f.collapse.toAR = f.toAR.collapse true :=
  AR.ext_of_true_false (by simp) (by simp) fun r s ↦ by
    simp [AR.link_collapse_true_false, mem_lines_collapse]

end Form

end Autosegmental
