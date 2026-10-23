/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.TakeDrop
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Phonology.Subregular.Docking

/-!
# Tonal surfacing processes

A **surfacing process** bundles the analysis [jardine-2016a] gives tone-string maps: a
marked tone value, and a context predicate `Surfaces w i` saying position `i` of `w`
surfaces with it. The induced rewrite `Surfacing.map` writes the marked tone exactly at
the surfacing positions and the default elsewhere; `Surfacing.support` is the surfacing
set. Owning the context predicate on the process is what lets rival processes coexist:
unbounded tonal plateauing (`Tone.utp`) and Copperbelt Bemba high-tone
spreading (`Studies/Yolyan2025`) instantiate the same structure with very different
predicates — plateauing's is convex and its map a closure operator, spreading's is
neither — so only the genuinely shared API lives here.

The laws are the shared minimum: surfacing positions are in-domain (`lt_length`), the
marked tone is faithful — an underlying marked tone always surfaces (`surfaces_of_hi`) —
and the two written values are distinct (`hi_ne_lo`), which makes the pointwise
characterizations (`map_getElem?_hi_iff`, `map_getElem?_lo_iff`) read the map exactly.

A surfacing process writes the default at every non-surfacing position, which is the whole
story over a two-letter alphabet; over a richer alphabet the general positional rewrite is
`Subregular.Docking`, which docks a change at the positions its context picks out and keeps
the rest, and a surfacing process on a two-letter word is the case `Surfacing.toDocking`
(`Surfacing.toDocking_map`).

## Main definitions

* `Surfacing`, `Surfacing.map`, `Surfacing.support` — the process, its rewrite and its
  surfacing set.
* `Surfacing.toDocking` — a surfacing process as a docking process.

## References

* [jardine-2016a]
-/

@[expose] public section

namespace Tone

/-- A tonal surfacing process over the alphabet `α`: a marked tone `hi`, a default `lo`,
and the context predicate saying which positions of a word surface with the mark. -/
structure Surfacing (α : Type*) where
  /-- The marked (surfacing) tone value. -/
  hi : α
  /-- The default value written at non-surfacing positions. -/
  lo : α
  /-- Position `i` of `w` surfaces with the marked tone. -/
  Surfaces : List α → ℕ → Prop
  /-- The two written values are distinct. -/
  hi_ne_lo : hi ≠ lo
  /-- Surfacing positions are in-domain. -/
  lt_length : ∀ {w : List α} {i : ℕ}, Surfaces w i → i < w.length
  /-- Faithfulness: an underlying marked tone surfaces. -/
  surfaces_of_hi : ∀ {w : List α} {i : ℕ}, w[i]? = some hi → Surfaces w i
  /-- The context predicate is decidable, so the map computes. -/
  decSurfaces : ∀ w i, Decidable (Surfaces w i)

namespace Surfacing

variable {α : Type*} (P : Surfacing α) {w : List α} {i j : ℕ}

instance (w : List α) (i : ℕ) : Decidable (P.Surfaces w i) := P.decSurfaces w i

/-- The induced rewrite: the marked tone exactly at the surfacing positions. -/
def map (w : List α) : List α := w.mapIdx fun i _ => if P.Surfaces w i then P.hi else P.lo

@[simp] theorem map_nil : P.map [] = [] := rfl

@[simp] theorem map_length : (P.map w).length = w.length := by simp [map]

theorem map_getElem? :
    (P.map w)[i]? = w[i]?.map fun _ => if P.Surfaces w i then P.hi else P.lo := by
  simp [map, List.getElem?_mapIdx]

theorem map_getElem?_hi_iff : (P.map w)[j]? = some P.hi ↔ P.Surfaces w j := by
  rw [map_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, -, ha⟩
    by_contra hs
    rw [ite_eq_right hs] at ha
    exact P.hi_ne_lo ha.symm
  · exact fun hs => ⟨w[j]'(P.lt_length hs), List.getElem?_eq_getElem (P.lt_length hs),
      ite_eq_left hs⟩

theorem map_getElem?_lo_iff :
    (P.map w)[j]? = some P.lo ↔ j < w.length ∧ ¬ P.Surfaces w j := by
  rw [map_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hout⟩
    refine ⟨(List.getElem?_eq_some_iff.mp ha).1, fun hs => ?_⟩
    rw [ite_eq_left hs] at hout
    exact P.hi_ne_lo hout
  · exact fun ⟨hj, hs⟩ => ⟨w[j], List.getElem?_eq_getElem hj, ite_eq_right hs⟩

theorem map_getElem?_hi_of_getElem?_hi (h : w[i]? = some P.hi) :
    (P.map w)[i]? = some P.hi :=
  P.map_getElem?_hi_iff.mpr (P.surfaces_of_hi h)

theorem Surfaces.lt_length {P : Surfacing α} {w : List α} {i : ℕ}
    (h : P.Surfaces w i) : i < w.length :=
  P.lt_length h

theorem requiresBothSides_of_flanks {xOn yOn xOff yOff : α} {n t : ℕ → ℕ}
    (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hon : ∀ d, P.Surfaces (flankWord xOn P.lo yOn (n d)) (t d))
    (hoffL : ∀ d, ¬ P.Surfaces (flankWord xOff P.lo yOn (n d)) (t d))
    (hoffR : ∀ d, ¬ P.Surfaces (flankWord xOn P.lo yOff (n d)) (t d)) :
    RequiresBothSides P.map :=
  have hlen : ∀ d, t d < (flankWord xOn P.lo yOff (n d)).length := fun d => by
    rw [length_flankWord]
    have := hn d
    omega
  RequiresBothSides.of_flanks ht hn
    (fun d => (P.map_getElem?_hi_iff.mpr (hon d)).trans_ne (by simpa using P.hi_ne_lo))
    (fun d => P.map_getElem?_lo_iff.mpr ⟨by simpa using hlen d, hoffL d⟩)
    (fun d => P.map_getElem?_lo_iff.mpr ⟨hlen d, hoffR d⟩)

theorem requiresBothSides_of_surfaces_iff
    (hiff : ∀ w i, P.Surfaces w i ↔ P.hi ∈ w.take (i + 1) ∧ P.hi ∈ w.drop i) :
    RequiresBothSides P.map :=
  P.requiresBothSides_of_flanks (xOn := P.hi) (yOn := P.hi) (xOff := P.lo) (yOff := P.lo)
    (n := fun d => 2 * d + 2) (t := fun d => d + 1) (fun d => by omega) (fun d => by omega)
    (fun d => (hiff _ _).mpr
      ⟨(mem_take_flankWord_iff P.hi_ne_lo.symm (by omega)).mpr rfl,
        (mem_drop_flankWord_iff P.hi_ne_lo.symm (by omega)).mpr rfl⟩)
    (fun d hs => absurd ((mem_take_flankWord_iff P.hi_ne_lo.symm (by omega)).mp
      ((hiff _ _).mp hs).1) P.hi_ne_lo.symm)
    (fun d hs => absurd ((mem_drop_flankWord_iff P.hi_ne_lo.symm (by omega)).mp
      ((hiff _ _).mp hs).2) P.hi_ne_lo.symm)

/-! ### The surfacing set -/

/-- The surfacing positions of `w`, as a finite set. -/
def support (w : List α) : Finset ℕ := (Finset.range w.length).filter (P.Surfaces w)

@[simp] theorem mem_support : j ∈ P.support w ↔ P.Surfaces w j := by
  simp only [support, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact P.lt_length

theorem map_eq_indicator :
    P.map w = (List.range w.length).map fun i => if i ∈ P.support w then P.hi else P.lo :=
  List.ext_getElem (by simp [map]) fun i h₁ h₂ => by simp [map, mem_support]

end Surfacing

/-- A surfacing process as a docking process: the marked tone docks at the surfacing
positions. -/
def Surfacing.toDocking {α : Type*} (P : Surfacing α) : Subregular.Docking α where
  dock _ := P.hi
  Docks := P.Surfaces
  lt_length := P.lt_length
  decDocks := P.decSurfaces

theorem Surfacing.toDocking_map {α : Type*} (P : Surfacing α) {w : List α}
    (hw : ∀ a ∈ w, a = P.hi ∨ a = P.lo) : P.toDocking.map w = P.map w := by
  refine List.ext_getElem? fun i => ?_
  rw [Subregular.Docking.map_getElem?, Surfacing.map_getElem?]
  rcases hi : w[i]? with _ | a
  · rfl
  · simp only [Option.map_some, toDocking, Option.some.injEq]
    split_ifs with hs
    · rfl
    · rcases hw a (List.mem_of_getElem? hi) with rfl | rfl
      · exact absurd (P.surfaces_of_hi hi) hs
      · rfl

end Tone
