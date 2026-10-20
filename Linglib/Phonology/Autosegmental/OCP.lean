/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OCP
public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# OCP-merging collapse of autosegmental representations

Merging melody nodes moves the positions of the melody tier along a monotone map.
`X.repoint m w f` reads melody tier `m` as the word `w`, moves each of its positions `p` to
`f p`, and carries the links along, so a merged node keeps every line of the nodes merged into
it. `AR.collapse m` is the repointing that destutters the tier word (`OCP.collapse`) through the
run index `runIdx`, merging every run of identical melody nodes; a melody `Hⁿ` collapses to one
`H` linked to `n` timing slots. `realizeMerged` is the realization of a string followed by the
collapse. Jardine and Heinz instead merge only at the seam of each concatenation
(`Autosegmental/MergeConcat.lean`), and the two agree when the primitives are OCP-clean, as in
Jardine's tonal realization.

## Main definitions

* `AR.repoint`: a representation with one tier moved along a map of its positions.
* `AR.collapse`: the OCP merge of melody tier `m`.
* `AR.IsCleanAt`: no adjacent repeats on melody tier `m`.
* `realizeMerged`: the realization of a string, collapsed.
* `MergedLinks`: the lines of the merged realization of a string of two-tier presentations.

## Main results

* `AR.link_repoint`, `AR.noCrossing_repoint`: repointing carries the links, and a monotone
  repointing preserves the NCC.
* `AR.isCleanAt_collapse`, `AR.noCrossing_collapse`: the collapse is OCP-clean and preserves
  the NCC.
* `AR.isCleanAt_iff_isOCPClean`: tier-word cleanliness is Axiom 6 on the normal form.
* `AR.free_realizeMerged_ofWords_iff`: the merged realization of a string of presentations
  reads as one presentation.

## References

* [jardine-2019]
* [jardine-heinz-2015]
* [jardine-2016b]
-/

@[expose] public section

namespace Autosegmental

open OCP

/-! ### Repointing a tier -/

section Repoint
variable {ι : Type*} [DecidableEq ι] {τ : ι → Type*} (m : ι)

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

variable [Finite ι] (X : TieredAR ι τ) [Finite X.obj.V] (m)

/-- `X` with tier `m` read as the word `w` and its positions moved along `f`, the links
following the positions they join. -/
noncomputable def AR.repoint (w : List (τ m)) (f : ℕ → ℕ) : TieredAR ι τ :=
  AR.ofData (Function.update X.tierWord m w) fun i j r s ↦
    ∃ p q, X.link i j p q ∧ repointIdx m f i p = r ∧ repointIdx m f j q = s

variable {X m} {w : List (τ m)}

instance : Finite (X.repoint m w f).obj.V := inferInstanceAs (Finite (AR.ofData _ _).obj.V)

@[simp] theorem AR.tierWord_repoint_self : (X.repoint m w f).tierWord m = w := by
  simp [AR.repoint]

@[simp] theorem AR.tierWord_repoint_of_ne {i : ι} (h : i ≠ m) :
    (X.repoint m w f).tierWord i = X.tierWord i := by
  simp [AR.repoint, h]

@[simp] theorem AR.tierLength_repoint_self : (X.repoint m w f).tierLength m = w.length := by
  rw [← AR.length_tierWord, AR.tierWord_repoint_self]

@[simp] theorem AR.tierLength_repoint_of_ne {i : ι} (h : i ≠ m) :
    (X.repoint m w f).tierLength i = X.tierLength i := by
  rw [← AR.length_tierWord, AR.tierWord_repoint_of_ne h, AR.length_tierWord]

/-- The links of a repointing are the repointed links, when `f` keeps tier `m` in bounds. -/
theorem AR.link_repoint (hf : ∀ p < X.tierLength m, f p < w.length) (i j : ι) (r s : ℕ) :
    (X.repoint m w f).link i j r s ↔
      ∃ p q, X.link i j p q ∧ repointIdx m f i p = r ∧ repointIdx m f j q = s := by
  have hlt {i : ι} {p : ℕ} (hp : p < X.tierLength i) :
      repointIdx m f i p < (Function.update X.tierWord m w i).length := by
    rcases eq_or_ne i m with rfl | h
    · simpa using hf p hp
    · simpa [h] using hp
  show (AR.ofData _ _).link i j r s ↔ _
  rw [AR.link_ofData]
  constructor
  · rintro ⟨-, -, -, h | ⟨p, q, hl, rfl, rfl⟩⟩
    exacts [h, ⟨q, p, AR.link_symm hl, rfl, rfl⟩]
  · rintro ⟨p, q, hl, rfl, rfl⟩
    obtain ⟨hp, hq, -⟩ := id hl
    refine ⟨fun hij ↦ ?_, hlt hp, hlt hq, Or.inl ⟨p, q, hl, rfl, rfl⟩⟩
    subst hij
    exact AR.not_link_self_tier i p q hl

/-- A monotone repointing preserves the NCC. -/
theorem AR.noCrossing_repoint (hf : ∀ p < X.tierLength m, f p < w.length) (hmono : Monotone f)
    (h : NoCrossing X.obj.edges X.obj.arcs) :
    NoCrossing (X.repoint m w f).obj.edges (X.repoint m w f).obj.arcs := by
  rw [AR.noCrossing_iff] at h ⊢
  intro i j ⟨r, s⟩ hl ⟨r', s'⟩ hl' hrr'
  obtain ⟨p, q, hpq, rfl, rfl⟩ := (AR.link_repoint hf i j r s).mp hl
  obtain ⟨p', q', hpq', rfl, rfl⟩ := (AR.link_repoint hf i j r' s').mp hl'
  exact repointIdx_monotone hmono j (h i j (show (p, q) ∈ _ from hpq)
    (show (p', q') ∈ _ from hpq') ((repointIdx_monotone hmono i).reflect_lt hrr'))

end Repoint

/-! ### The collapse -/

section Collapse
variable {ι : Type*} {τ : ι → Type*} (X : TieredAR ι τ) [Finite X.obj.V] (m : ι)

/-- `X` is **OCP-clean** at melody tier `m` when that tier word has no adjacent repeats. -/
def AR.IsCleanAt : Prop := IsClean (X.tierWord m)

variable {X m} [DecidableEq ι] [DecidableEq (τ m)] in
theorem AR.IsCleanAt.repointIdx_runIdx (h : X.IsCleanAt m) {i : ι} {p : ℕ}
    (hp : p < X.tierLength i) : repointIdx m (runIdx (X.tierWord m)) i p = p := by
  rcases eq_or_ne i m with rfl | hi
  · exact (repointIdx_self p).trans (runIdx_clean h (by simpa using hp))
  · exact repointIdx_of_ne hi p

variable [DecidableEq ι] [Finite ι] [DecidableEq (τ m)]

/-- The **OCP-merging collapse** of melody tier `m` merges every run of identical melody nodes,
repointing the tier through its run index. -/
noncomputable def AR.collapse : TieredAR ι τ :=
  X.repoint m (OCP.collapse (X.tierWord m)) (runIdx (X.tierWord m))

instance : Finite (X.collapse m).obj.V := inferInstanceAs (Finite (X.repoint m _ _).obj.V)

@[simp] theorem AR.tierWord_collapse_self :
    (X.collapse m).tierWord m = OCP.collapse (X.tierWord m) :=
  AR.tierWord_repoint_self

@[simp] theorem AR.tierWord_collapse_of_ne {i : ι} (h : i ≠ m) :
    (X.collapse m).tierWord i = X.tierWord i :=
  AR.tierWord_repoint_of_ne h

@[simp] theorem AR.tierLength_collapse_of_ne {i : ι} (h : i ≠ m) :
    (X.collapse m).tierLength i = X.tierLength i :=
  AR.tierLength_repoint_of_ne h

/-- The links of a collapse are the links repointed through the run index. -/
theorem AR.link_collapse (i j : ι) (r s : ℕ) :
    (X.collapse m).link i j r s ↔
      ∃ p q, X.link i j p q ∧ repointIdx m (runIdx (X.tierWord m)) i p = r ∧
        repointIdx m (runIdx (X.tierWord m)) j q = s :=
  AR.link_repoint (fun _ hp ↦ runIdx_lt_collapse_length _ (by simpa using hp)) i j r s

/-- The collapse is OCP-clean at the collapsed tier. -/
theorem AR.isCleanAt_collapse : (X.collapse m).IsCleanAt m := by
  simpa [AR.IsCleanAt] using isClean_collapse (X.tierWord m)

/-- The collapse preserves the NCC, since it repoints links monotonically. -/
theorem AR.noCrossing_collapse (h : NoCrossing X.obj.edges X.obj.arcs) :
    NoCrossing (X.collapse m).obj.edges (X.collapse m).obj.arcs :=
  AR.noCrossing_repoint (fun _ hp ↦ runIdx_lt_collapse_length _ (by simpa using hp))
    (runIdx_monotone _) h

variable {X m}

/-- Collapsing a representation that is clean at `m` changes nothing. -/
noncomputable def AR.IsCleanAt.collapseFullIso (h : X.IsCleanAt m) :
    Graph.Iso (X.collapse m).obj X.obj :=
  AR.fullIsoOfReaderEq
    (fun i ↦ by
      rcases eq_or_ne i m with rfl | hi
      · simpa using IsClean.collapse_eq h
      · simp [hi])
    fun i j r s ↦ by
      rw [AR.link_collapse]
      constructor
      · rintro ⟨p, q, hl, rfl, rfl⟩
        obtain ⟨hp, hq, -⟩ := id hl
        rwa [h.repointIdx_runIdx hp, h.repointIdx_runIdx hq]
      · intro hl
        obtain ⟨hp, hq, -⟩ := id hl
        exact ⟨r, s, hl, h.repointIdx_runIdx hp, h.repointIdx_runIdx hq⟩

end Collapse

section RealizeMerged
variable {ι : Type*} [DecidableEq ι] [Finite ι] {τ : ι → Type*} (m : ι) [DecidableEq (τ m)]
variable {S : Type*}

/-- The collapsed realization at melody tier `m` realizes a string and then merges every run of
its melody. Over OCP-clean primitives it is the realization by merging concatenation
(`AR.nonempty_fullIso_realizeMerged`). -/
noncomputable def realizeMerged (g₀ : S → TieredAR ι τ)
    [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    TieredAR ι τ :=
  (AR.realize g₀ w).collapse m

instance (g₀ : S → TieredAR ι τ) [∀ s, Finite (g₀ s).obj.V] (w : List S) :
    Finite (realizeMerged m g₀ w).obj.V :=
  inferInstanceAs (Finite ((AR.realize g₀ w).collapse m).obj.V)

end RealizeMerged

/-! ### The merged realization of word primitives

In the two-tier case, with the melody over `true`, the merged realization of a string of
presentations reads as one presentation whose melody is destuttered and whose lines are
repointed through the run index of the melody. -/

section MergedOfWords

universe u
variable {α β : Type u} [DecidableEq α] {S : Type*}

/-- A line of an OCP-merged realization is a line of the realization with its melody position
repointed through the run index of the melody. -/
def MergedLinks (melody : List α) (Lk : ℕ → ℕ → Prop) (r s : ℕ) : Prop :=
  ∃ p < melody.length, Lk p s ∧ runIdx melody p = r

instance (melody : List α) (Lk : ℕ → ℕ → Prop) [DecidableRel Lk] :
    DecidableRel (MergedLinks melody Lk) :=
  fun _ _ ↦ by unfold MergedLinks; infer_instance

/-- Melody-to-timing lines of a two-tier collapse at the melody tier. -/
theorem AR.link_collapse_true_false (X : TieredAR Bool (TwoTier α β)) [Finite X.obj.V]
    (r s : ℕ) :
    (X.collapse true).link true false r s ↔
      ∃ p < X.tierLength true, X.link true false p s ∧ runIdx (X.tierWord true) p = r := by
  rw [AR.link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : false ≠ true)]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    obtain ⟨hp, -, -⟩ := id hl
    exact ⟨p, hp, hl, rfl⟩
  · rintro ⟨p, hp, hl, rfl⟩
    exact ⟨p, s, hl, rfl, rfl⟩

variable (as : S → List α) (bs : S → List β) (L : S → ℕ → ℕ → Prop)

theorem AR.tierWord_realizeMerged_ofWords_true (w : List S) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).tierWord true =
      OCP.collapse (w.map as).flatten := by
  simp [realizeMerged, AR.tierWord_realize_ofWords_true]

theorem AR.tierWord_realizeMerged_ofWords_false (w : List S) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).tierWord false =
      (w.map bs).flatten := by
  simp [realizeMerged, AR.tierWord_realize_ofWords_false]

theorem AR.link_realizeMerged_ofWords (w : List S) (r s : ℕ) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).link true false r s ↔
      MergedLinks (w.map as).flatten (BlockLinks as bs L w) r s := by
  show ((AR.realize _ w).collapse true).link true false r s ↔ _
  rw [AR.link_collapse_true_false]
  simp only [AR.link_realize_ofWords, AR.tierWord_realize_ofWords_true, MergedLinks,
    AR.tierLength_realize, AR.tierLength_ofWords_true, List.length_flatten, List.map_map,
    Function.comp_def]

/-- The tier words of the merged realization are those of its presentation. -/
theorem AR.tierWord_realizeMerged_eq_tierWord_ofWords (w : List S) (i : Bool) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).tierWord i =
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).tierWord i := by
  cases i
  · exact (AR.tierWord_realizeMerged_ofWords_false as bs L w).trans AR.tierWord_ofWords_false.symm
  · exact (AR.tierWord_realizeMerged_ofWords_true as bs L w).trans AR.tierWord_ofWords_true.symm

/-- The lines of the merged realization are those of its presentation. -/
theorem AR.link_realizeMerged_iff_link_ofWords (w : List S) (i j : Bool) (p q : ℕ) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).link i j p q ↔
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).link i j p q :=
  AR.link_iff_of_true_false (fun r s ↦ by
    rw [AR.link_realizeMerged_ofWords, AR.link_ofWords]
    constructor
    · rintro ⟨p, hp, hl, rfl⟩
      exact ⟨runIdx_lt_collapse_length _ hp, (hl.lt as bs L).2, p, hp, hl, rfl⟩
    · exact fun h ↦ h.2.2) i j p q

theorem AR.free_realizeMerged_ofWords_iff
    (B : List {F : TieredAR Bool (TwoTier α β) // Finite F.obj.V}) (w : List S) :
    (realizeMerged true (fun s ↦ AR.ofWords (as s) (bs s) (L s)) w).Free B ↔
      (AR.ofWords (OCP.collapse (w.map as).flatten) (w.map bs).flatten
        (MergedLinks (w.map as).flatten (BlockLinks as bs L w))).Free B :=
  AR.free_congr (AR.tierWord_realizeMerged_eq_tierWord_ofWords as bs L w)
    (AR.link_realizeMerged_iff_link_ofWords as bs L w) B

end MergedOfWords

section Axiom6Bridge
variable {ι : Type*} {τ : ι → Type*} (X : TieredAR ι τ) (m : ι)

/-- On a normal form, one position covers another in the arc order iff it is its immediate
successor. -/
theorem AR.covering_normalize [Finite X.obj.V] {i : ι}
    {p q : Fin (X.tierLength i)} :
    ((X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ∧
        ∀ u, ¬ ((X.normalize).obj.arcs.Adj ⟨i, p⟩ u ∧
          (X.normalize).obj.arcs.Adj u ⟨i, q⟩)) ↔
      (q : ℕ) = p + 1 := by
  constructor
  · rintro ⟨hpq, hcov⟩
    rw [AR.arcs_normalize] at hpq
    by_contra hne
    have hmid : (p : ℕ) + 1 < q := by
      have := Fin.lt_def.mp hpq; omega
    have hq := q.isLt
    refine hcov ⟨i, ⟨(p : ℕ) + 1, by omega⟩⟩ ⟨?_, ?_⟩
    · exact (AR.arcs_normalize _ _ _).mpr
        (show (p : ℕ) < (p : ℕ) + 1 by omega)
    · exact (AR.arcs_normalize _ _ _).mpr
        (show (p : ℕ) + 1 < (q : ℕ) from hmid)
  · intro hsucc
    refine ⟨(AR.arcs_normalize _ _ _).mpr
      (show (p : ℕ) < (q : ℕ) by omega), ?_⟩
    rintro ⟨j, u⟩ ⟨h1, h2⟩
    rcases eq_or_ne i j with rfl | hij
    · rw [AR.arcs_normalize] at h1 h2
      have := Fin.lt_def.mp h1
      have := Fin.lt_def.mp h2
      omega
    · exact AR.arcs_normalize_ne hij p u h1

/-- Cleanliness fails at a successor pair exactly when its labels repeat. -/
private theorem AR.label_normalize_succ [Finite X.obj.V]
    {p : ℕ} (hp1 : p + 1 < X.tierLength m) (hp : p < X.tierLength m) :
    (X.normalize).obj.label ⟨m, ⟨p, hp⟩⟩ = (X.normalize).obj.label ⟨m, ⟨p + 1, hp1⟩⟩ ↔
      (X.tierWord m)[p]'(by simp; omega) = (X.tierWord m)[p + 1]'(by simp; omega) := by
  rw [AR.label_normalize, AR.label_normalize,
    ← AR.tierWord_getElem (p := ⟨p, hp⟩),
    ← AR.tierWord_getElem (p := ⟨p + 1, hp1⟩)]
  exact ⟨fun h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2, fun h ↦ congrArg (Sigma.mk m) h⟩

/-- Tier-word cleanliness is Axiom 6 of [jardine-2016b] on the normal form. -/
theorem AR.isCleanAt_iff_isOCPClean [Finite X.obj.V] :
    X.IsCleanAt m ↔
      IsOCPClean (X.normalize).obj.arcs (X.normalize).obj.label Sigma.fst m := by
  constructor
  · rintro h ⟨i, p⟩ ⟨j, q⟩ hpq hcov htier heq
    rcases eq_or_ne i j with rfl | hij
    · obtain rfl : m = i := by
        symm; simpa [AR.label_normalize] using htier
      have hsucc : (q : ℕ) = (p : ℕ) + 1 := (X.covering_normalize).mp ⟨hpq, hcov⟩
      have hq1 : (p : ℕ) + 1 < X.tierLength m := hsucc ▸ q.isLt
      rw [show q = ⟨(p : ℕ) + 1, hq1⟩ from Fin.ext hsucc] at heq
      have hp' : (p : ℕ) + 1 < (X.tierWord m).length := by
        simp only [AR.length_tierWord]
        omega
      exact List.isChain_iff_getElem.mp h p hp'
        ((X.label_normalize_succ m hq1 p.isLt).mp heq)
    · exact AR.arcs_normalize_ne hij p q hpq
  · intro h
    refine List.isChain_iff_getElem.mpr fun p hp heq ↦ ?_
    have hlen : p + 1 < X.tierLength m := by
      simpa only [AR.length_tierWord] using hp
    have hplt : p < X.tierLength m := by omega
    have hcover := (X.covering_normalize
      (p := ⟨p, hplt⟩) (q := ⟨p + 1, hlen⟩) (i := m)).mpr rfl
    exact h hcover.1 hcover.2 (by simp [AR.label_normalize])
      ((X.label_normalize_succ m hlen hplt).mpr heq)

end Axiom6Bridge

end Autosegmental
