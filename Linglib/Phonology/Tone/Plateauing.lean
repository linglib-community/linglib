/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Linglib.Core.Data.List.TakeDrop
public import Linglib.Core.Computability.ShuffleIdeal
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Phonology.Autosegmental.OCP
public import Linglib.Phonology.Autosegmental.TwoTier
public import Linglib.Phonology.Autosegmental.Hull
public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.Tone.Surfacing

/-!
# Unbounded tonal plateauing

Hyman and Katamba's plateauing rule for Luganda makes every tone-bearing unit between two
H-toned units surface H. Over Jardine's string rendering, a word over `AssociationState` records
each timing unit's association state (`H` associated to a H tone, `O` unassociated), and `utp`, a
`Tone.Surfacing` process, rewrites it pointwise by its surfacing predicate, the two-sided window
`H ∈ w.take (i + 1) ∧ H ∈ w.drop i` asking for an H at or before `i` and one at or after it. The
map is `utp.map`, the surfacing set `plateau`.

What surfaces is the representation. The string reads back into two-tier autosegmental
representations by `AssociationState.toAR`, and the output representation `plateauAR w` is the
OCP-merged input, hull-closed — fusion then spreading. Timing slot `i` surfaces with H in
`plateauAR w` exactly when `utp.Surfaces w i` (`utp.surfaces_iff_surfacesWith_plateauAR`).

The map is the flagship *unbounded circumambient* process: whether a position changes
depends on unboundedly distant material on **both** sides, in the strong witness form
`utp.isUnboundedCircumambient` — perturbing either far side alone reverts the change — with the
weaker `utp.twoSidedUnboundedDependence` as a corollary. `Studies/MeinhardtEtAl2024` excludes
the map from the non-interacting bimachines, and `Studies/LamontOHaraSmith2019` shows it weakly
deterministic in Heinz and Lai's sense.

## Main definitions

* `Tone.AssociationState` — the H/Ø string alphabet, a timing unit's association to an H tone
  (distinct from `Tone.TBUKind`, the phonological typology of timing units).
* `Tone.AssociationState.toAR`, `Tone.plateauAR` — the translation of a timing unit into a one-slot
  representation, and the output representation (OCP-merged input, hull-closed).
* `Tone.utp` — plateauing as a `Tone.Surfacing` process; `utp.map` the map.
* `Tone.plateau` — the set of surfacing positions.

## Main results

* `utp.surfaces_iff_surfacesWith_plateauAR` — surfacing is H-linkedness in the output
  representation.
* `utp.map_getElem?_H_iff` / `utp.map_getElem?_O_iff` — pointwise characterization of the map.
* `utp.map_eq_plateau_indicator`, `plateau_eq_Icc` — the output is the indicator word of an
  interval, from the first trigger to the last.
* `utp.map_toneless`, `utp.map_single`, `utp.map_plateau` — the rule schemata: toneless words
  and lone Hs are unchanged; everything between the outermost Hs surfaces H.
* `utp.map_getElem?_H_of_getElem?_H`, `utp.map_mono`, `utp.map_map` — plateauing is a closure
  operator in the pointwise H-order: extensive, monotone, idempotent.
* `utp.mem_range_map_iff` — the outputs of plateauing are the words without an `H O H`
  subsequence.
* `utp.isUnboundedCircumambient` — deleting either flanking H reverts the plateau target, at
  every distance.

## References

* [hyman-katamba-2010]
* [jardine-2016a]
-/

@[expose] public section

namespace Tone

/-! ### The tone-bearing-unit alphabet -/

/-- A tone-bearing unit's association state is `H` for a TBU associated to a H tone and `O`
for an unspecified TBU (Jardine's Ø). -/
inductive AssociationState | H | O
  deriving DecidableEq, Repr

/-! ### The output representation

The string reads back into two-tier representations, and plateauing on representations is
OCP-fusion followed by hull-closure of the association lines (Hyman and Katamba's rule as an
operation on structures). -/

open Autosegmental Subregular

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

@[simp] theorem word_toAR_true (a : AssociationState) : (toAR a).word true = melody a := rfl

@[simp] theorem word_toAR_false (a : AssociationState) : (toAR a).word false = [()] := rfl

@[simp] theorem link_toAR (a : AssociationState) (p q : ℕ) :
    (toAR a).Link true false p q ↔ p < (melody a).length ∧ q = 0 := by
  simp [toAR]

@[simp] theorem word_prod_map_toAR_true (w : List AssociationState) :
    (w.map toAR).prod.word true = List.replicate (w.count .H) TRN.H := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [ih, List.replicate_succ]

@[simp] theorem word_prod_map_toAR_false (w : List AssociationState) :
    (w.map toAR).prod.word false = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih, List.replicate_succ]

theorem link_prod_map_toAR (w : List AssociationState) (p j : ℕ) :
    (w.map toAR).prod.Link true false p j ↔
      p = (w.take j).count .H ∧ w[j]? = some .H := by
  have hoff : AR.tierOffset toAR true w j = (w.take j).count .H := by
    simp only [AR.tierOffset, word_toAR_true, sum_length_melody]
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
    ((w.map toAR).prod.collapse true).Link true false k j ↔ k = 0 ∧ w[j]? = some .H := by
  rw [AR.link_collapse]
  simp only [repointIdx_self, repointIdx_of_ne (by decide : false ≠ true),
    link_prod_map_toAR, word_prod_map_toAR_true, OCP.runIdx_replicate]
  constructor
  · rintro ⟨p, q, ⟨-, h⟩, rfl, rfl⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨_, j, ⟨rfl, h⟩, rfl, rfl⟩

end AssociationState

/-- The output representation, in coordinates, is the OCP-merge and then the hull, both at the
melody tier. -/
def plateauAR (w : List AssociationState) : AR (TwoTier TRN Unit) :=
  ((w.map AssociationState.toAR).prod.collapse true).hull true

theorem link_plateauAR (w : List AssociationState) (k j : ℕ) :
    (plateauAR w).Link true false k j ↔ k = 0 ∧ .H ∈ w.take (j + 1) ∧ .H ∈ w.drop j := by
  by_cases hj : j < w.length
  · unfold plateauAR
    rw [AR.link_hull_left true _ (by decide)
      (by simpa using hj :
        j < (((w.map AssociationState.toAR).prod.collapse true).word false).length)]
    simp only [AssociationState.link_collapse_prod_map_toAR, List.mem_take_iff_getElem?,
      List.mem_drop_iff_getElem?, Nat.lt_succ_iff]
    constructor
    · rintro ⟨q₁, q₂, ⟨rfl, h₁⟩, ⟨-, h₂⟩, hle₁, hle₂⟩
      exact ⟨rfl, ⟨q₁, hle₁, h₁⟩, q₂, hle₂, h₂⟩
    · rintro ⟨rfl, ⟨q₁, hle₁, h₁⟩, q₂, hle₂, h₂⟩
      exact ⟨q₁, q₂, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩, hle₁, hle₂⟩
  · refine iff_of_false (fun h => hj ?_) fun ⟨_, _, h⟩ => hj (List.lt_length_of_mem_drop h)
    simpa [plateauAR] using h.lt_right

theorem surfacesWith_plateauAR (w : List AssociationState) (j : ℕ) :
    (plateauAR w).SurfacesWith TRN.H j ↔ .H ∈ w.take (j + 1) ∧ .H ∈ w.drop j := by
  simp only [AR.SurfacesWith, link_plateauAR, and_assoc, exists_eq_left]
  refine and_congr_right fun hA => and_iff_left_of_imp fun _ => ?_
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (List.count_pos_iff.mpr (List.take_subset _ _ hA)).ne'
  simp [plateauAR, hn]

/-! ### The plateauing process -/

/-- Unbounded tonal plateauing is the surfacing process in which TBU `i` surfaces H iff some
H-toned TBU lies at or before it and some at or after it. -/
@[simps hi lo]
def utp : Surfacing AssociationState where
  hi := .H
  lo := .O
  Surfaces w i := .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i
  hi_ne_lo := by decide
  lt_length h := List.lt_length_of_mem_drop h.2
  surfaces_of_hi h :=
    ⟨List.mem_take_iff_getElem?.mpr ⟨_, Nat.lt_succ_self _, h⟩,
      List.mem_drop_iff_getElem?.mpr ⟨_, le_rfl, h⟩⟩
  decSurfaces w i := inferInstanceAs (Decidable (_ ∧ _))

variable {w : List AssociationState} {i j k : ℕ}

theorem utp.surfaces_def : utp.Surfaces w i ↔ .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i :=
  Iff.rfl

/-- What surfaces is the representation. `utp.Surfaces w i` is the H-linkedness of timing slot
`i` in the output representation `plateauAR w`, the OCP-merged, hull-closed realization. -/
theorem utp.surfaces_iff_surfacesWith_plateauAR :
    utp.Surfaces w i ↔ (plateauAR w).SurfacesWith TRN.H i :=
  (surfacesWith_plateauAR w i).symm

theorem utp.surfaces_iff :
    utp.Surfaces w i ↔ (∃ j ≤ i, w[j]? = some .H) ∧ ∃ j ≥ i, w[j]? = some .H := by
  rw [utp.surfaces_def, List.mem_take_iff_getElem?, List.mem_drop_iff_getElem?]
  simp

theorem utp.surfaces_of_le_of_le (hi : utp.Surfaces w i) (hk : utp.Surfaces w k)
    (hij : i ≤ j) (hjk : j ≤ k) : utp.Surfaces w j :=
  utp.surfaces_def.mpr
    ⟨w.take_subset_take_left (by omega) (utp.surfaces_def.mp hi).1,
      w.drop_subset_drop_left (by omega) (utp.surfaces_def.mp hk).2⟩

theorem utp.H_mem_of_surfaces (h : utp.Surfaces w i) : .H ∈ w :=
  List.take_subset _ _ (utp.surfaces_def.mp h).1

theorem utp.surfaces_reverse (hi : i < w.length) :
    utp.Surfaces w.reverse i ↔ utp.Surfaces w (w.length - 1 - i) := by
  rw [utp.surfaces_def, utp.surfaces_def, List.take_reverse, List.drop_reverse,
    List.mem_reverse, List.mem_reverse,
    show w.length - (i + 1) = w.length - 1 - i from by omega,
    show w.length - i = (w.length - 1 - i) + 1 from by omega, and_comm]

theorem utp.surfaces_split {a : AssociationState} (h : w[i]? = some a) :
    utp.Surfaces w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rcases eq_or_ne a .H with rfl | ha
  · simp [utp.surfaces_of_hi h]
  · obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    rw [utp.surfaces_def, List.take_add_one, h, List.drop_eq_getElem_cons hi, hia]
    simp [ha, Ne.symm ha]

theorem utp.map_getElem? :
    (utp.map w)[i]? =
      w[i]?.map fun _ => if utp.Surfaces w i then AssociationState.H else AssociationState.O :=
  Surfacing.map_getElem? utp

theorem utp.map_getElem?_H_iff : (utp.map w)[j]? = some .H ↔ utp.Surfaces w j :=
  utp.map_getElem?_hi_iff

theorem utp.map_getElem?_O_iff :
    (utp.map w)[j]? = some .O ↔ j < w.length ∧ ¬ utp.Surfaces w j :=
  utp.map_getElem?_lo_iff

theorem utp.map_reverse : utp.map w.reverse = (utp.map w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · rw [utp.map_getElem?, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa using hi), Surfacing.map_length, utp.map_getElem?]
    simp only [utp.surfaces_reverse hi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ### The plateau set -/

/-- The plateau of `w` is the set of positions that surface H. -/
def plateau (w : List AssociationState) : Finset ℕ := utp.support w

@[simp] theorem mem_plateau : j ∈ plateau w ↔ utp.Surfaces w j := utp.mem_support

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w :=
  ⟨fun ⟨_, hj⟩ => utp.H_mem_of_surfaces (mem_plateau.mp hj), fun hw =>
    have ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    ⟨i, mem_plateau.mpr (utp.surfaces_of_hi hi)⟩⟩

/-- `utp.map` writes the indicator word of its plateau. -/
theorem utp.map_eq_plateau_indicator :
    utp.map w
      = (List.range w.length).map fun i =>
          if i ∈ plateau w then AssociationState.H else AssociationState.O :=
  utp.map_eq_indicator

theorem plateau_eq_Icc_of {lo hi : ℕ} (hlo : w[lo]? = some .H) (hhi : w[hi]? = some .H)
    (hb : ∀ j, w[j]? = some .H → lo ≤ j ∧ j ≤ hi) : plateau w = Finset.Icc lo hi := by
  ext j
  rw [mem_plateau, Finset.mem_Icc, utp.surfaces_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    have hb₁ := hb j₁ h₁; have hb₂ := hb j₂ h₂; omega
  · exact fun hj => ⟨⟨lo, hj.1, hlo⟩, hi, hj.2, hhi⟩

/-- The plateau is an interval, from the first trigger to the last. -/
theorem plateau_eq_Icc (hne : (plateau w).Nonempty) :
    plateau w = Finset.Icc ((plateau w).min' hne) ((plateau w).max' hne) := by
  ext j
  rw [Finset.mem_Icc]
  refine ⟨fun hj => ⟨(plateau w).min'_le j hj, (plateau w).le_max' j hj⟩, fun ⟨h₁, h₂⟩ =>
    mem_plateau.mpr (utp.surfaces_of_le_of_le (mem_plateau.mp ((plateau w).min'_mem hne))
      (mem_plateau.mp ((plateau w).max'_mem hne)) h₁ h₂)⟩

/-! ### Closure laws

Plateauing is a closure operator in the pointwise H-order: extensive
(`utp.map_getElem?_H_of_getElem?_H`), monotone (`utp.map_mono`), idempotent (`utp.map_map`). The
engine is convexity: the output's Hs are the plateau, an interval, so plateauing the
output surfaces nothing new (`utp.surfaces_map`). -/

/-- Every H survives plateauing. -/
theorem utp.map_getElem?_H_of_getElem?_H (h : w[i]? = some .H) :
    (utp.map w)[i]? = some .H :=
  utp.map_getElem?_hi_of_getElem?_hi h

theorem utp.surfaces_mono {w' : List AssociationState}
    (hw : ∀ j : ℕ, w[j]? = some AssociationState.H → w'[j]? = some AssociationState.H)
    (h : utp.Surfaces w i) :
    utp.Surfaces w' i := by
  obtain ⟨⟨l, hl, hlH⟩, r, hr, hrH⟩ := utp.surfaces_iff.mp h
  exact utp.surfaces_iff.mpr ⟨⟨l, hl, hw l hlH⟩, r, hr, hw r hrH⟩

/-- Plateauing is monotone, pointwise more Hs in giving pointwise more Hs out. -/
theorem utp.map_mono {w' : List AssociationState}
    (hw : ∀ j : ℕ, w[j]? = some AssociationState.H → w'[j]? = some AssociationState.H) (j : ℕ)
    (h : (utp.map w)[j]? = some AssociationState.H) : (utp.map w')[j]? = some AssociationState.H :=
  utp.map_getElem?_H_iff.mpr (utp.surfaces_mono hw (utp.map_getElem?_H_iff.mp h))

theorem utp.H_mem_map : .H ∈ utp.map w ↔ .H ∈ w :=
  ⟨fun h => have ⟨_, hi⟩ := List.mem_iff_getElem?.mp h
    utp.H_mem_of_surfaces (utp.map_getElem?_H_iff.mp hi),
   fun h => have ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    List.mem_iff_getElem?.mpr ⟨i, utp.map_getElem?_H_of_getElem?_H hi⟩⟩

theorem utp.surfaces_map : utp.Surfaces (utp.map w) i ↔ utp.Surfaces w i := by
  constructor
  · intro h
    obtain ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩ := utp.surfaces_iff.mp h
    rw [utp.map_getElem?_H_iff] at h₁ h₂
    obtain ⟨⟨l, hl, hlH⟩, -⟩ := utp.surfaces_iff.mp h₁
    obtain ⟨-, r, hr, hrH⟩ := utp.surfaces_iff.mp h₂
    exact utp.surfaces_iff.mpr ⟨⟨l, by omega, hlH⟩, r, by omega, hrH⟩
  · exact fun h => utp.surfaces_iff.mpr ⟨⟨i, le_rfl, utp.map_getElem?_H_iff.mpr h⟩,
      i, le_rfl, utp.map_getElem?_H_iff.mpr h⟩

@[simp] theorem plateau_map : plateau (utp.map w) = plateau w := by
  ext j
  rw [mem_plateau, mem_plateau, utp.surfaces_map]

/-- Plateauing is idempotent, a plateau being already closed. -/
@[simp] theorem utp.map_map : utp.map (utp.map w) = utp.map w := by
  rw [utp.map_eq_plateau_indicator (w := utp.map w), plateau_map, Surfacing.map_length,
    ← utp.map_eq_plateau_indicator]

/-! ### The outputs of plateauing

A word is an output of plateauing exactly when plateauing fixes it, and it is fixed exactly
when no `O` lies between two `H`s: the outputs are the words without an `H O H` subsequence. -/

theorem utp.map_eq_self_iff : utp.map w = w ↔ ∀ i, utp.Surfaces w i → w[i]? = some .H := by
  refine ⟨fun h i hi => h ▸ utp.map_getElem?_H_iff.mpr hi, fun h => List.ext_getElem? fun i => ?_⟩
  by_cases hi : i < w.length
  · by_cases hs : utp.Surfaces w i
    · rw [utp.map_getElem?_H_iff.mpr hs, h i hs]
    · rw [utp.map_getElem?_O_iff.mpr ⟨hi, hs⟩]
      obtain ⟨a, ha⟩ : ∃ a, w[i]? = some a := ⟨w[i], List.getElem?_eq_getElem hi⟩
      cases a with
      | H => exact absurd (utp.surfaces_of_hi ha) hs
      | O => exact ha.symm
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by omega)]

theorem utp.range_map : Set.range utp.map = Function.fixedPoints utp.map :=
  Set.ext fun w => ⟨fun ⟨_, hv⟩ => hv ▸ utp.map_map, fun h => ⟨w, h⟩⟩

theorem HOH_sublist_iff :
    [AssociationState.H, .O, .H].Sublist w ↔ ∃ i, utp.Surfaces w i ∧ w[i]? = some .O := by
  simp only [List.cons_sublist_iff, List.nil_sublist, and_true, utp.surfaces_iff]
  constructor
  · rintro ⟨r₁, r₂, rfl, h₁, s₁, s₂, rfl, h₂, t₁, t₂, rfl, h₃⟩
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp h₁
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h₂
    obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp h₃
    have ha' := (List.getElem?_eq_some_iff.mp ha).1
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨r₁.length + j, ⟨⟨a, by omega, ?_⟩, r₁.length + s₁.length + b, by omega, ?_⟩, ?_⟩
    · rwa [List.getElem?_append_left ha']
    · rw [List.getElem?_append_right (by omega),
        show r₁.length + s₁.length + b - r₁.length = s₁.length + b by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]
      exact hb
    · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left hj']
      exact hj
  · rintro ⟨i, ⟨⟨a, hai, ha⟩, c, hic, hc⟩, hi⟩
    have hai' : a < i := lt_of_le_of_ne hai fun h => by subst h; simp_all
    have hic' : i < c := lt_of_le_of_ne hic fun h => by subst h; simp_all
    refine ⟨w.take (a + 1), w.drop (a + 1), (List.take_append_drop _ _).symm,
      List.mem_take_iff_getElem?.mpr ⟨a, by omega, ha⟩,
      (w.drop (a + 1)).take (i - a), w.drop (i + 1), ?_,
      List.mem_take_iff_getElem?.mpr ⟨i - (a + 1), by omega, ?_⟩,
      w.drop (i + 1), [], (List.append_nil _).symm,
      List.mem_drop_iff_getElem?.mpr ⟨c, by omega, hc⟩⟩
    · conv_lhs => rw [← List.take_append_drop (i - a) (w.drop (a + 1))]
      rw [List.drop_drop]
      congr 2
      omega
    · rw [List.getElem?_drop, show a + 1 + (i - (a + 1)) = i by omega]
      exact hi

/-- The outputs of plateauing are the words without an `H O H` subsequence. -/
theorem utp.mem_range_map_iff : w ∈ Set.range utp.map ↔ w ∉ Language.shuffleIdeal [.H, .O, .H] := by
  rw [utp.range_map, Function.mem_fixedPoints, Function.IsFixedPt, utp.map_eq_self_iff,
    Language.mem_shuffleIdeal, HOH_sublist_iff]
  push Not
  refine forall_congr' fun i ↦ ⟨fun h hs ↦ by simp [h hs], fun h hs ↦ ?_⟩
  have := utp.lt_length hs
  cases ha : w[i]? with
  | none => simp_all
  | some a => cases a <;> simp_all

/-! ### The plateauing rule

The rule schemata as theorems about `utp` rather than clauses of its definition. -/

/-- A toneless word is unchanged. -/
theorem utp.map_toneless (n : ℕ) : utp.map (List.replicate n .O) = List.replicate n .O := by
  have h : plateau (List.replicate n AssociationState.O) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (by simp)
  simp [utp.map_eq_plateau_indicator, h, List.map_const']

/-- A word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp.map_single (m n : ℕ) :
    utp.map (List.replicate m .O ++ .H :: List.replicate n .O)
      = List.replicate m .O ++ .H :: List.replicate n .O := by
  have hH : ∀ j, (List.replicate m AssociationState.O ++ AssociationState.H ::
      List.replicate n AssociationState.O)[j]? = some AssociationState.H ↔ j = m := fun j => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate]
    split_ifs <;> simp_all <;> omega
  rw [utp.map_eq_plateau_indicator, plateau_eq_Icc_of ((hH m).mpr rfl) ((hH m).mpr rfl)
    fun j hj => by rw [hH j] at hj; omega]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.getElem_cons,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- Everything between the outermost Hs surfaces H; the medial material `w` is
arbitrary. -/
theorem utp.map_plateau (m p : ℕ) (w : List AssociationState) :
    utp.map (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
      = List.replicate m .O ++ (List.replicate (w.length + 2) .H ++ List.replicate p .O) := by
  have hb : ∀ j, (List.replicate m AssociationState.O ++ AssociationState.H ::
      (w ++ AssociationState.H :: List.replicate p AssociationState.O))[j]? =
        some AssociationState.H → m ≤ j ∧ j ≤ m + 1 + w.length := fun j hj => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate] at hj
    split_ifs at hj <;> first | omega | simp_all
  rw [utp.map_eq_plateau_indicator, plateau_eq_Icc_of (by simp) (by
      simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
        List.length_replicate]
      split_ifs <;> first | rfl | omega) hb]
  refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- No plateau without two Hs; `HØØH ↦ HHHH`. -/
example : utp.map [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp.map [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp.map [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-! ### Unbounded circumambience

Whether the target surfaces is controlled by unboundedly distant flanks: instantiate
the flank-witness template with `2d+2` toneless TBUs between the flanks. -/

/-- UTP is unbounded circumambient. Its trigger is the two-sided window conjunction, so deleting
either flanking H reverts the plateau target. -/
theorem utp.isUnboundedCircumambient : IsUnboundedCircumambient utp.map :=
  utp.isUnboundedCircumambient_of_surfaces_iff fun _ _ => utp.surfaces_def

theorem utp.twoSidedUnboundedDependence : TwoSidedUnboundedDependence utp.map :=
  utp.isUnboundedCircumambient.twoSidedUnboundedDependence

end Tone
