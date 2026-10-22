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
`f p`, and carries the links along, so a merged node keeps every line of the nodes merged into
it. `AR.collapse m` is the repointing that destutters the tier word (`OCP.collapse`) through the
run index `runIdx`, merging every run of identical melody nodes; a melody `Hⁿ` collapses to one
`H` linked to `n` timing slots. Collapsing a realization `(w.map g₀).prod` merges every run of
its melody. Jardine and Heinz instead merge only at the seam of each concatenation
(`Autosegmental/MergeAR.lean`), and the two agree when the primitives are OCP-clean, as in
Jardine's tonal realization.

## Main definitions

* `AR.repoint`: a representation with one tier moved along a map of its positions.
* `AR.collapse`: the OCP merge of melody tier `m`.
* `AR.IsCleanAt`: no adjacent repeats on melody tier `m`.
* `MergedLinks`: the lines of a two-tier presentation with its melody collapsed.

## Main results

* `AR.link_repoint`, `AR.noCrossing_repoint`: repointing carries the links, and a monotone
  repointing preserves the NCC.
* `AR.isCleanAt_collapse`, `AR.noCrossing_collapse`: the collapse is OCP-clean and preserves
  the NCC; `AR.IsCleanAt.collapse_eq`: collapsing a clean tier changes nothing.
* `AR.collapse_ofWords`, `AR.prod_ofWords_collapse`: collapsing a presentation, or a realized
  string of presentations, gives a presentation.

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : ι → Type*} (X : AR τ) (m : ι)
  (w : List (τ m)) {f : ℕ → ℕ} (hf : ∀ p < (X.word m).length, f p < w.length)

/-- `X` with tier `m` read as the word `w` and its positions moved along `f`, the lines
following the positions they join. -/
def repoint : AR τ :=
  X.map (Function.update X.word m w) fun i p ↦ ⟨repointIdx m f i p, by
    unfold repointIdx
    split_ifs with h
    · subst h
      simpa using hf p p.2
    · simp [Function.update_of_ne h]⟩

@[simp] theorem word_repoint_self : (X.repoint m w hf).word m = w := by simp [repoint, map]

@[simp] theorem word_repoint_of_ne {i : ι} (h : i ≠ m) : (X.repoint m w hf).word i = X.word i := by
  simp [repoint, map, h]

variable {X m w}

/-- The lines of a repointing are the repointed lines. -/
theorem link_repoint {i j : ι} {r s : ℕ} :
    (X.repoint m w hf).Link i j r s ↔
      ∃ p q, X.Link i j p q ∧ repointIdx m f i p = r ∧ repointIdx m f j q = s := by
  rw [repoint, link_map]
  constructor
  · rintro ⟨⟨p, q⟩, hx, rfl, rfl⟩
    exact ⟨p, q, mem_lines.1 hx, rfl, rfl⟩
  · rintro ⟨p, q, ⟨hp, hq, h⟩, rfl, rfl⟩
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), h, rfl, rfl⟩

/-- A monotone repointing preserves the NCC. -/
theorem NoCrossing.repoint (hmono : Monotone f) (h : X.NoCrossing) :
    (X.repoint m w hf).NoCrossing :=
  NoCrossing.map _ _ (fun i _ _ hab ↦ repointIdx_monotone hmono i hab) h

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

variable [Fintype ι]

/-- The **OCP-merging collapse** of melody tier `m` merges every run of identical melody nodes,
repointing the tier through its run index. -/
def collapse : AR τ :=
  X.repoint m (OCP.collapse (X.word m)) fun _ hp ↦ runIdx_lt_collapse_length _ hp

@[simp] theorem word_collapse_self : (X.collapse m).word m = OCP.collapse (X.word m) :=
  word_repoint_self ..

@[simp] theorem word_collapse_of_ne {i : ι} (h : i ≠ m) : (X.collapse m).word i = X.word i :=
  word_repoint_of_ne _ _ _ _ h

variable {X m}

/-- The lines of a collapse are the lines repointed through the run index. -/
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

/-! ### Collapsing two-tier presentations

In the two-tier case, with the melody over `true`, collapsing a presentation gives the
presentation whose melody is destuttered and whose lines are repointed through the run index of
the melody. -/

section MergedOfWords

universe u
variable {α β : Type u} [DecidableEq α]

/-- A line of an OCP-merged presentation is a line of the presentation with its melody position
repointed through the run index of the melody. -/
def _root_.Autosegmental.MergedLinks (melody : List α) (Lk : ℕ → ℕ → Prop) (r s : ℕ) : Prop :=
  ∃ p < melody.length, Lk p s ∧ runIdx melody p = r

instance (melody : List α) (Lk : ℕ → ℕ → Prop) [DecidableRel Lk] :
    DecidableRel (MergedLinks melody Lk) :=
  fun _ _ ↦ inferInstanceAs (Decidable (∃ _ < _, _))

/-- Melody-to-timing lines of a two-tier collapse at the melody tier. -/
theorem link_collapse_true_false {X : AR (TwoTier α β)} [DecidableEq β] {r s : ℕ} :
    (X.collapse true).Link true false r s ↔
      ∃ p < (X.word true).length, X.Link true false p s ∧ runIdx (X.word true) p = r := by
  rw [link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : false ≠ true)]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    exact ⟨p, hl.lt_left, hl, rfl⟩
  · rintro ⟨p, -, hl, rfl⟩
    exact ⟨p, s, hl, rfl, rfl⟩

variable [DecidableEq β] {as : List α} {bs : List β} {L : ℕ → ℕ → Prop} [DecidableRel L]

/-- Collapsing the melody of a presentation gives a presentation. -/
theorem collapse_ofWords :
    (ofWords as bs L).collapse true = ofWords (OCP.collapse as) bs (MergedLinks as L) :=
  ext_of_true_false (by simp) (by simp) fun r s ↦ by
    rw [link_collapse_true_false, link_ofWords]
    simp only [word_ofWords_true, link_ofWords, MergedLinks]
    constructor
    · rintro ⟨p, hp, ⟨-, hs, hl⟩, rfl⟩
      exact ⟨runIdx_lt_collapse_length _ hp, hs, p, hp, hl, rfl⟩
    · rintro ⟨-, hs, p, hp, hl, rfl⟩
      exact ⟨p, hp, ⟨hp, hs, hl⟩, rfl⟩

variable {S : Type*} (as : S → List α) (bs : S → List β) (L : S → ℕ → ℕ → Prop)
  [∀ s, DecidableRel (L s)]

/-- The merged realization of a string of presentations is one presentation. -/
theorem prod_ofWords_collapse (w : List S) :
    (w.map fun s ↦ ofWords (as s) (bs s) (L s)).prod.collapse true =
      ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w)) := by
  rw [prod_ofWords, collapse_ofWords]

end MergedOfWords

end AR

end Autosegmental
