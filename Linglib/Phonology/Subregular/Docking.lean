/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.WindowFormula
public import Linglib.Phonology.Subregular.Dependence

/-!
# Docking processes

A **docking process** is the positional rewrite of the subregular program
([chandlee-2014], [chandlee-jardine-2019]) with its context left semantic: what docking does to
a position's symbol, and a decidable predicate saying at which positions of a word it docks;
the other positions keep their symbol. It is the string function a relabelling transduction
computes, and the object over which locality is stated once: when the context is a
quantifier-free formula bounded by `l` back and `r` forward, the output at a position reads
only that window, so the map depends boundedly on both sides in the sense of
`Subregular.BoundedDependence`.

## Main definitions

* `Docking`, `Docking.map` — the process and its rewrite; `Docking.support`, the docking set.
* `Docking.ofQF` — the process with a quantifier-free context.

## Main results

* `Docking.map_getElem?` — the rewrite pointwise.
* `Docking.requiresBothSides_of_flanks` — the flank-witness template, from three docking facts.
* `Docking.ofQF_map_getElem?_congr` — with a bounded guard, the output at a position reads
  only the guard's window.
* `Docking.ofQF_boundedDependence_left`, `Docking.ofQF_boundedDependence_right` — hence bounded
  dependence on both sides.

## References

* [chandlee-2014]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace Subregular

/-- A docking process over the alphabet `α` is what docking does to a position's symbol,
together with the context predicate saying at which positions of a word it docks; the other
positions keep their symbol. -/
structure Docking (α : Type*) where
  /-- `dock a` is the change docked at a position holding `a`. -/
  dock : α → α
  /-- Position `i` of `w` is docked at. -/
  Docks : List α → ℕ → Prop
  /-- Docking positions are in-domain. -/
  lt_length : ∀ {w : List α} {i : ℕ}, Docks w i → i < w.length
  /-- The context predicate is decidable, so the map computes. -/
  decDocks : ∀ w i, Decidable (Docks w i)

namespace Docking

variable {α : Type*} (P : Docking α) {w : List α} {i : ℕ}

instance (w : List α) (i : ℕ) : Decidable (P.Docks w i) := P.decDocks w i

/-- The induced rewrite docks the change exactly at the docking positions. -/
def map (w : List α) : List α := w.mapIdx fun i a => if P.Docks w i then P.dock a else a

@[simp] theorem map_nil : P.map [] = [] := rfl

@[simp] theorem map_length : (P.map w).length = w.length := by simp [map]

theorem map_getElem? :
    (P.map w)[i]? = w[i]?.map fun a => if P.Docks w i then P.dock a else a := by
  simp [map, List.getElem?_mapIdx]

theorem map_getElem?_of_docks (h : P.Docks w i) : (P.map w)[i]? = w[i]?.map P.dock := by
  simp [map_getElem?, h]

theorem map_getElem?_of_not_docks (h : ¬ P.Docks w i) : (P.map w)[i]? = w[i]? := by
  simp [map_getElem?, h]

/-- `P.support w` is the finite set of docking positions of `w`. -/
def support (w : List α) : Finset ℕ := (Finset.range w.length).filter (P.Docks w)

@[simp] theorem mem_support : i ∈ P.support w ↔ P.Docks w i := by
  simp only [support, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact P.lt_length

/-- The flank-witness template at the docking level. A process that docks a change of the
filler at a `d`-margined target of a flank word, and does not dock there when either flank
alone is flipped, requires both sides. -/
theorem requiresBothSides_of_flanks {fill xOn yOn xOff yOff : α} {n t : ℕ → ℕ}
    (hfill : P.dock fill ≠ fill) (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hon : ∀ d, P.Docks (flankWord xOn fill yOn (n d)) (t d))
    (hoffL : ∀ d, ¬ P.Docks (flankWord xOff fill yOn (n d)) (t d))
    (hoffR : ∀ d, ¬ P.Docks (flankWord xOn fill yOff (n d)) (t d)) :
    RequiresBothSides P.map :=
  have hmid (x y : α) (d : ℕ) : (flankWord x fill y (n d))[t d]? = some fill :=
    getElem?_flankWord_mid (by have := ht d; omega) (by have := hn d; omega)
  .of_flanks (fill := fill) (xOn := xOn) (yOn := yOn) (xOff := xOff) (yOff := yOff) ht hn
    (fun d => by rw [P.map_getElem?_of_docks (hon d), hmid]; simpa using hfill)
    (fun d => by rw [P.map_getElem?_of_not_docks (hoffL d), hmid])
    (fun d => by rw [P.map_getElem?_of_not_docks (hoffR d), hmid])

/-! ### Quantifier-free contexts -/

variable [DecidableEq α]

/-- The docking process whose context is a quantifier-free formula. -/
def ofQF (φ : WindowFormula α) (dock : α → α) : Docking α where
  dock := dock
  Docks w i := i < w.length ∧ φ.Realize w i
  lt_length h := h.1
  decDocks _ _ := inferInstance

/-- With a guard bounded by `l` back and `r` forward, the output at a position reads only the
input on that window. -/
theorem ofQF_map_getElem?_congr {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r) (dock : α → α)
    {w w' : List α} (hag : ∀ j, i - l ≤ j → j ≤ i + r → w[j]? = w'[j]?) :
    ((ofQF φ dock).map w)[i]? = ((ofQF φ dock).map w')[i]? := by
  have hi := hag i (by omega) (by omega)
  have hlt : i < w.length ↔ i < w'.length := by
    simp only [← Nat.not_le, ← List.getElem?_eq_none_iff, hi]
  have hR : φ.Realize w i ↔ φ.Realize w' i := hφ.realize_congr rfl
    (fun _ _ ↦ hag _ (by omega) (by omega)) fun _ _ ↦ hag _ (by omega) (by omega)
  simp only [map_getElem?, ofQF, hi, hlt, hR]

/-- A quantifier-free docking process with a bounded guard depends boundedly on the left. -/
theorem ofQF_boundedDependence_left {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r)
    (dock : α → α) : BoundedDependence (ofQF φ dock).map .left :=
  ⟨l, fun _ _ _ h ↦ ofQF_map_getElem?_congr hφ dock fun j h₁ _ ↦
    List.drop_eq_drop_iff_getElem?.mp h j h₁⟩

/-- A quantifier-free docking process with a bounded guard depends boundedly on the right. -/
theorem ofQF_boundedDependence_right {φ : WindowFormula α} {l r : ℕ} (hφ : φ.Bounded l r)
    (dock : α → α) : BoundedDependence (ofQF φ dock).map .right :=
  ⟨r, fun _ _ _ h ↦ ofQF_map_getElem?_congr hφ dock fun j _ h₂ ↦
    List.take_eq_take_iff_getElem?.mp h j (by omega)⟩

end Docking

end Subregular
