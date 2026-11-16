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
public import Linglib.Core.Order.OrdConnected
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Phonology.Autosegmental.Hull
public import Linglib.Phonology.Tone.AssociationState

/-!
# Unbounded tonal plateauing

Hyman and Katamba's plateauing rule for Luganda makes every tone-bearing unit between two H-toned
units surface H. Over any alphabet with a letter `a` for the H-toned unit, `utp a` rewrites to `a`
the units with an `a` at or before them and an `a` at or after them (`utp.Surfaces`, the output
predicate for `a`) and keeps the others. [The positions of `a` in the output are the
order-connected hull of its positions in the input](##Tone.highs_utp), so plateauing is a closure
operator on sets of positions, and [the words it fixes](##Tone.utp_eq_self_iff), which are its
outputs, are those in which `a` occupies an interval. Whether a unit changes depends on
unboundedly distant material on both sides: [deleting either flanking `a` reverts
it](##Tone.utp_isUnboundedCircumambient). Over Jardine's two letters H and Ø the same unit is
H-linked in [the OCP-merged, hull-closed
input](##Tone.utp.surfaces_iff_surfacesWith_plateauAR).

## References

* [hyman-katamba-2010]
* [jardine-2016a]
-/

@[expose] public section

namespace Tone

open Autosegmental Subregular

variable {α : Type*} {a : α} {w : List α} {i j k : ℕ}

/-! ### The plateauing map -/

/-- The positions of `w` that hold the letter `a`. -/
def highs (a : α) (w : List α) : Set ℕ := {i | w[i]? = some a}

@[simp] theorem mem_highs : i ∈ highs a w ↔ w[i]? = some a := Iff.rfl

/-- Unit `i` of `w` surfaces `a` under plateauing when an `a` lies at or before it and one at or
after it. -/
def utp.Surfaces (a : α) (w : List α) (i : ℕ) : Prop :=
  a ∈ w.take (i + 1) ∧ a ∈ w.drop i

instance [DecidableEq α] (a : α) (w : List α) (i : ℕ) : Decidable (utp.Surfaces a w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Unbounded tonal plateauing rewrites to `a` the units that surface `a` and keeps the others. -/
def utp [DecidableEq α] (a : α) (w : List α) : List α :=
  w.mapIdx fun i b ↦ if utp.Surfaces a w i then a else b

theorem utp.surfaces_def : utp.Surfaces a w i ↔ a ∈ w.take (i + 1) ∧ a ∈ w.drop i :=
  Iff.rfl

theorem utp.Surfaces.lt_length (h : utp.Surfaces a w i) : i < w.length :=
  List.lt_length_of_mem_drop h.2

/-- An underlying `a` surfaces. -/
theorem utp.surfaces_of_getElem? (h : w[i]? = some a) : utp.Surfaces a w i :=
  ⟨List.mem_take_iff_getElem?.mpr ⟨_, Nat.lt_succ_self _, h⟩,
    List.mem_drop_iff_getElem?.mpr ⟨_, le_rfl, h⟩⟩

theorem utp.surfaces_iff :
    utp.Surfaces a w i ↔ (∃ j ≤ i, w[j]? = some a) ∧ ∃ j ≥ i, w[j]? = some a := by
  rw [utp.surfaces_def, List.mem_take_iff_getElem?, List.mem_drop_iff_getElem?]
  simp

theorem utp.surfaces_of_le_of_le (hi : utp.Surfaces a w i) (hk : utp.Surfaces a w k)
    (hij : i ≤ j) (hjk : j ≤ k) : utp.Surfaces a w j :=
  ⟨w.take_subset_take_left (by omega) hi.1, w.drop_subset_drop_left (by omega) hk.2⟩

theorem utp.mem_of_surfaces (h : utp.Surfaces a w i) : a ∈ w :=
  List.take_subset _ _ h.1

theorem utp.surfaces_reverse (hi : i < w.length) :
    utp.Surfaces a w.reverse i ↔ utp.Surfaces a w (w.length - 1 - i) := by
  rw [utp.surfaces_def, utp.surfaces_def, List.take_reverse, List.drop_reverse,
    List.mem_reverse, List.mem_reverse,
    show w.length - (i + 1) = w.length - 1 - i from by omega,
    show w.length - i = (w.length - 1 - i) + 1 from by omega, and_comm]

theorem utp.surfaces_split {b : α} (h : w[i]? = some b) :
    utp.Surfaces a w i ↔ b = a ∨ (a ∈ w.take i ∧ a ∈ w.drop (i + 1)) := by
  rcases eq_or_ne b a with rfl | hb
  · simp [utp.surfaces_of_getElem? h]
  · obtain ⟨hi, hib⟩ := List.getElem?_eq_some_iff.mp h
    rw [utp.surfaces_def, List.take_add_one, h, List.drop_eq_getElem_cons hi, hib]
    simp [hb, Ne.symm hb]

section

variable [DecidableEq α]

@[simp] theorem length_utp : (utp a w).length = w.length := by simp [utp]

theorem getElem?_utp :
    (utp a w)[i]? = w[i]?.map fun b ↦ if utp.Surfaces a w i then a else b := by
  simp [utp, List.getElem?_mapIdx]

theorem getElem?_utp_of_not_surfaces (h : ¬ utp.Surfaces a w i) : (utp a w)[i]? = w[i]? := by
  simp [getElem?_utp, h]

theorem getElem?_utp_eq_iff : (utp a w)[j]? = some a ↔ utp.Surfaces a w j := by
  refine ⟨fun h ↦ ?_, fun hs ↦ by
    simp [getElem?_utp, hs, List.getElem?_eq_getElem hs.lt_length]⟩
  by_contra hs
  exact hs (utp.surfaces_of_getElem? (getElem?_utp_of_not_surfaces hs ▸ h))

theorem utp_reverse : utp a w.reverse = (utp a w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · rw [getElem?_utp, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa using hi), length_utp, getElem?_utp]
    simp only [utp.surfaces_reverse hi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ### The plateau set -/

/-- The plateau of `w` is the set of positions that surface `a`. -/
def plateau (a : α) (w : List α) : Finset ℕ :=
  (Finset.range w.length).filter (utp.Surfaces a w)

@[simp] theorem mem_plateau : j ∈ plateau a w ↔ utp.Surfaces a w j := by
  simp only [plateau, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact utp.Surfaces.lt_length

@[simp] theorem plateau_nonempty : (plateau a w).Nonempty ↔ a ∈ w :=
  ⟨fun ⟨_, hj⟩ => utp.mem_of_surfaces (mem_plateau.mp hj), fun hw =>
    have ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    ⟨i, mem_plateau.mpr (utp.surfaces_of_getElem? hi)⟩⟩

theorem plateau_eq_Icc_of {lo hi : ℕ} (hlo : w[lo]? = some a) (hhi : w[hi]? = some a)
    (hb : ∀ j, w[j]? = some a → lo ≤ j ∧ j ≤ hi) : plateau a w = Finset.Icc lo hi := by
  ext j
  rw [mem_plateau, Finset.mem_Icc, utp.surfaces_iff]
  constructor
  · rintro ⟨⟨j₁, hj₁, h₁⟩, j₂, hj₂, h₂⟩
    have hb₁ := hb j₁ h₁; have hb₂ := hb j₂ h₂; omega
  · exact fun hj => ⟨⟨lo, hj.1, hlo⟩, hi, hj.2, hhi⟩

/-- The plateau is an interval, from the first trigger to the last. -/
theorem plateau_eq_Icc (hne : (plateau a w).Nonempty) :
    plateau a w = Finset.Icc ((plateau a w).min' hne) ((plateau a w).max' hne) := by
  ext j
  rw [Finset.mem_Icc]
  refine ⟨fun hj => ⟨(plateau a w).min'_le j hj, (plateau a w).le_max' j hj⟩, fun ⟨h₁, h₂⟩ =>
    mem_plateau.mpr (utp.surfaces_of_le_of_le (mem_plateau.mp ((plateau a w).min'_mem hne))
      (mem_plateau.mp ((plateau a w).max'_mem hne)) h₁ h₂)⟩

/-! ### Plateauing as a hull

The positions of `a` in the output are the order-connected hull of its positions in the input.
Extensivity, monotonicity and idempotence are those of the closure operator. -/

/-- The positions of `a` in `utp a w` are the order-connected hull of its positions in `w`. -/
theorem highs_utp (a : α) (w : List α) :
    highs a (utp a w) = Set.ordConnectedHull (highs a w) := by
  ext i
  rw [Set.mem_ordConnectedHull, mem_highs, getElem?_utp_eq_iff, utp.surfaces_iff]
  exact ⟨fun ⟨⟨x, hx, hxH⟩, y, hy, hyH⟩ ↦ ⟨x, hxH, y, hyH, hx, hy⟩,
    fun ⟨x, hxH, y, hyH, hx, hy⟩ ↦ ⟨⟨x, hx, hxH⟩, y, hy, hyH⟩⟩

theorem coe_plateau (a : α) (w : List α) :
    (plateau a w : Set ℕ) = Set.ordConnectedHull (highs a w) := by
  rw [← highs_utp]
  ext i
  simp [getElem?_utp_eq_iff]

/-- Every `a` survives plateauing. -/
theorem highs_subset_highs_utp (a : α) (w : List α) : highs a w ⊆ highs a (utp a w) :=
  highs_utp a w ▸ Set.ordConnectedHull.le_closure _

theorem getElem?_utp_of_getElem?_eq (h : w[i]? = some a) : (utp a w)[i]? = some a :=
  highs_subset_highs_utp a w h

/-- Plateauing is monotone: more `a`s in give more `a`s out. -/
theorem highs_utp_mono {w' : List α} (h : highs a w ⊆ highs a w') :
    highs a (utp a w) ⊆ highs a (utp a w') := by
  rw [highs_utp, highs_utp]
  exact Set.ordConnectedHull.monotone h

theorem utp.surfaces_mono {w' : List α} (hw : highs a w ⊆ highs a w')
    (h : utp.Surfaces a w i) : utp.Surfaces a w' i :=
  getElem?_utp_eq_iff.mp (highs_utp_mono hw (getElem?_utp_eq_iff.mpr h))

theorem mem_utp_iff : a ∈ utp a w ↔ a ∈ w :=
  ⟨fun h => have ⟨_, hi⟩ := List.mem_iff_getElem?.mp h
    utp.mem_of_surfaces (getElem?_utp_eq_iff.mp hi),
   fun h => have ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    List.mem_iff_getElem?.mpr ⟨i, getElem?_utp_of_getElem?_eq hi⟩⟩

theorem utp.surfaces_utp : utp.Surfaces a (utp a w) i ↔ utp.Surfaces a w i := by
  rw [← getElem?_utp_eq_iff, ← mem_highs, highs_utp, highs_utp,
    Set.ordConnectedHull.idempotent, ← highs_utp, mem_highs, getElem?_utp_eq_iff]

@[simp] theorem plateau_utp : plateau a (utp a w) = plateau a w := by
  ext j
  rw [mem_plateau, mem_plateau, utp.surfaces_utp]

/-- Plateauing is idempotent, a plateau being already closed. -/
@[simp] theorem utp_utp (w : List α) : utp a (utp a w) = utp a w := by
  refine List.ext_getElem? fun i ↦ ?_
  by_cases hs : utp.Surfaces a w i
  · rw [getElem?_utp_eq_iff.mpr hs, getElem?_utp_eq_iff.mpr (utp.surfaces_utp.mpr hs)]
  · rw [getElem?_utp_of_not_surfaces (mt utp.surfaces_utp.mp hs)]

/-! ### The outputs of plateauing

A word is an output of plateauing exactly when plateauing fixes it, and it is fixed exactly when
`a` occupies an interval, that is, when no other letter stands between two `a`s. -/

theorem utp_eq_self_iff_forall : utp a w = w ↔ ∀ i, utp.Surfaces a w i → w[i]? = some a := by
  refine ⟨fun h i hi ↦ h ▸ getElem?_utp_eq_iff.mpr hi, fun h ↦ List.ext_getElem? fun i ↦ ?_⟩
  by_cases hs : utp.Surfaces a w i
  · rw [getElem?_utp_eq_iff.mpr hs, h i hs]
  · exact getElem?_utp_of_not_surfaces hs

/-- Plateauing fixes the words in which `a` occupies an order-connected set of positions. -/
theorem utp_eq_self_iff : utp a w = w ↔ (highs a w).OrdConnected := by
  rw [utp_eq_self_iff_forall, ← Set.ordConnectedHull_eq_self_iff, ← highs_utp]
  exact ⟨fun h ↦ Set.Subset.antisymm (fun i hi ↦ h i (getElem?_utp_eq_iff.mp hi))
    (highs_subset_highs_utp a w), fun h i hi ↦ h.subset (getElem?_utp_eq_iff.mpr hi)⟩

theorem utp_of_notMem (h : a ∉ w) : utp a w = w :=
  utp_eq_self_iff_forall.mpr fun _ hs ↦ absurd (utp.mem_of_surfaces hs) h

theorem range_utp : Set.range (utp a) = Function.fixedPoints (utp a) :=
  Set.ext fun w => ⟨fun ⟨_, hv⟩ => hv ▸ utp_utp _, fun h => ⟨w, h⟩⟩

omit [DecidableEq α] in
theorem sublist_iff_exists_surfaces {b : α} (hb : b ≠ a) :
    [a, b, a].Sublist w ↔ ∃ i, utp.Surfaces a w i ∧ w[i]? = some b := by
  simp only [List.cons_sublist_iff, List.nil_sublist, and_true, utp.surfaces_iff]
  constructor
  · rintro ⟨r₁, r₂, rfl, h₁, s₁, s₂, rfl, h₂, t₁, t₂, rfl, h₃⟩
    obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h₁
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h₂
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp h₃
    have hp' := (List.getElem?_eq_some_iff.mp hp).1
    have hj' := (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨r₁.length + j, ⟨⟨p, by omega, ?_⟩, r₁.length + s₁.length + q, by omega, ?_⟩, ?_⟩
    · rwa [List.getElem?_append_left hp']
    · rw [List.getElem?_append_right (by omega),
        show r₁.length + s₁.length + q - r₁.length = s₁.length + q by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hq).1]
      exact hq
    · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left hj']
      exact hj
  · rintro ⟨i, ⟨⟨p, hpi, hp⟩, q, hiq, hq⟩, hi⟩
    have hpi' : p < i := lt_of_le_of_ne hpi fun e => by
      subst e; exact hb (Option.some.inj (hi.symm.trans hp))
    have hiq' : i < q := lt_of_le_of_ne hiq fun e => by
      subst e; exact hb (Option.some.inj (hi.symm.trans hq))
    refine ⟨w.take (p + 1), w.drop (p + 1), (List.take_append_drop _ _).symm,
      List.mem_take_iff_getElem?.mpr ⟨p, by omega, hp⟩,
      (w.drop (p + 1)).take (i - p), w.drop (i + 1), ?_,
      List.mem_take_iff_getElem?.mpr ⟨i - (p + 1), by omega, ?_⟩,
      w.drop (i + 1), [], (List.append_nil _).symm,
      List.mem_drop_iff_getElem?.mpr ⟨q, by omega, hq⟩⟩
    · conv_lhs => rw [← List.take_append_drop (i - p) (w.drop (p + 1))]
      rw [List.drop_drop]
      congr 2
      omega
    · rw [List.getElem?_drop, show p + 1 + (i - (p + 1)) = i by omega]
      exact hi

/-- The outputs of plateauing are the words with no other letter between two `a`s. -/
theorem mem_range_utp_iff :
    w ∈ Set.range (utp a) ↔ ∀ b, b ≠ a → w ∉ Language.shuffleIdeal [a, b, a] := by
  rw [range_utp, Function.mem_fixedPoints, Function.IsFixedPt, utp_eq_self_iff_forall]
  refine ⟨fun h b hb hmem ↦ ?_, fun h i hs ↦ ?_⟩
  · obtain ⟨i, hs, hib⟩ := (sublist_iff_exists_surfaces hb).mp (Language.mem_shuffleIdeal.mp hmem)
    exact hb (Option.some.inj (hib.symm.trans (h i hs)))
  · by_contra hne
    have hi := hs.lt_length
    exact h w[i] (fun e ↦ hne (by rw [List.getElem?_eq_getElem hi, e]))
      (Language.mem_shuffleIdeal.mpr ((sublist_iff_exists_surfaces
        fun e ↦ hne (by rw [List.getElem?_eq_getElem hi, e])).mpr
        ⟨i, hs, List.getElem?_eq_getElem hi⟩))

/-! ### Unbounded circumambience -/

/-- Plateauing is unbounded circumambient: a unit between two flanking `a`s surfaces `a` at every
distance, and deleting either flank leaves it as it was. -/
theorem utp_isUnboundedCircumambient {b : α} (hb : b ≠ a) : IsUnboundedCircumambient (utp a) :=
  .of_flanks (fill := b) (xOn := a) (yOn := a) (xOff := b) (yOff := b)
    (n := fun d ↦ 2 * d + 2) (t := fun d ↦ d + 1) (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by
      rw [getElem?_utp_eq_iff.mpr ⟨(mem_take_flankWord_iff hb (by omega)).mpr rfl,
        (mem_drop_flankWord_iff hb (by omega)).mpr rfl⟩]
      exact fun e ↦ hb (Option.some.inj e).symm)
    (fun d ↦ by
      rw [getElem?_utp_of_not_surfaces fun hs ↦
        hb ((mem_take_flankWord_iff hb (by omega)).mp hs.1)]
      exact getElem?_flankWord_mid (by omega) (by omega))
    (fun d ↦ by
      rw [getElem?_utp_of_not_surfaces fun hs ↦
        hb ((mem_drop_flankWord_iff hb (by omega)).mp hs.2)]
      exact getElem?_flankWord_mid (by omega) (by omega))

theorem utp_twoSidedUnboundedDependence {b : α} (hb : b ≠ a) :
    TwoSidedUnboundedDependence (utp a) :=
  (utp_isUnboundedCircumambient hb).twoSidedUnboundedDependence

end

/-! ### Words over H and Ø

Jardine's string rendering has two letters. There a word is its length and its high positions,
the plateauing rule takes the form of his three schemata, and the word reads back into a
representation: plateauing is OCP-fusion followed by hull-closure of the association lines,
Hyman and Katamba's rule as an operation on structures. -/

variable {w : List AssociationState}

/-- A word over H and Ø is determined by its length and its high positions. -/
theorem eq_of_highs_eq {w w' : List AssociationState} (hl : w.length = w'.length)
    (h : highs .H w = highs .H w') : w = w' := by
  refine List.ext_getElem hl fun i h₁ h₂ ↦ ?_
  have hi : w[i]? = some .H ↔ w'[i]? = some .H := Set.ext_iff.mp h i
  rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] at hi
  cases hw : w[i] <;> cases hw' : w'[i] <;> simp_all

theorem getElem?_utp_eq_O_iff :
    (utp .H w)[j]? = some .O ↔ j < w.length ∧ ¬ utp.Surfaces .H w j := by
  by_cases hs : utp.Surfaces .H w j
  · simp [getElem?_utp_eq_iff.mpr hs, hs]
  · rw [getElem?_utp_of_not_surfaces hs]
    refine ⟨fun h ↦ ⟨(List.getElem?_eq_some_iff.mp h).1, hs⟩, fun ⟨hj, _⟩ ↦ ?_⟩
    rw [List.getElem?_eq_getElem hj]
    cases hw : w[j] with
    | H => exact absurd (utp.surfaces_of_getElem? (by rw [List.getElem?_eq_getElem hj, hw])) hs
    | O => rfl

/-- Over H and Ø, `utp` writes the indicator word of its plateau. -/
theorem utp_eq_plateau_indicator :
    utp .H w
      = (List.range w.length).map fun i =>
          if i ∈ plateau .H w then AssociationState.H else AssociationState.O := by
  refine List.ext_getElem? fun i ↦ ?_
  rcases lt_or_ge i w.length with hi | hi
  · by_cases hs : utp.Surfaces .H w i
    · rw [getElem?_utp_eq_iff.mpr hs]
      simp [hs, hi]
    · rw [getElem?_utp_eq_O_iff.mpr ⟨hi, hs⟩]
      simp [hs, hi]
  · rw [List.getElem?_eq_none (by simpa using hi), List.getElem?_eq_none (by simpa using hi)]

/-- A toneless word is unchanged. -/
theorem utp_replicate_O (n : ℕ) : utp AssociationState.H (List.replicate n .O) = List.replicate n .O :=
  utp_of_notMem (by simp)

/-- A word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp_single (m n : ℕ) :
    utp AssociationState.H (List.replicate m .O ++ .H :: List.replicate n .O)
      = List.replicate m .O ++ .H :: List.replicate n .O := by
  have hH : ∀ j, (List.replicate m AssociationState.O ++ AssociationState.H ::
      List.replicate n AssociationState.O)[j]? = some AssociationState.H ↔ j = m := fun j => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate]
    split_ifs <;> simp_all <;> omega
  rw [utp_eq_plateau_indicator, plateau_eq_Icc_of ((hH m).mpr rfl) ((hH m).mpr rfl)
    fun j hj => by rw [hH j] at hj; omega]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.getElem_cons,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- Everything between the outermost Hs surfaces H; the medial material `w` is
arbitrary. -/
theorem utp_plateau (m p : ℕ) (w : List AssociationState) :
    utp AssociationState.H (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
      = List.replicate m .O ++ (List.replicate (w.length + 2) .H ++ List.replicate p .O) := by
  have hb : ∀ j, (List.replicate m AssociationState.O ++ AssociationState.H ::
      (w ++ AssociationState.H :: List.replicate p AssociationState.O))[j]? =
        some AssociationState.H → m ≤ j ∧ j ≤ m + 1 + w.length := fun j hj => by
    simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
      List.length_replicate] at hj
    split_ifs at hj <;> first | omega | simp_all
  rw [utp_eq_plateau_indicator, plateau_eq_Icc_of (by simp) (by
      simp only [List.getElem?_append, List.getElem?_cons, List.getElem?_replicate,
        List.length_replicate]
      split_ifs <;> first | rfl | omega) hb]
  refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_append,
    List.getElem_replicate, List.length_replicate, Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- No plateau without two Hs; `HØØH ↦ HHHH`. -/
example : utp AssociationState.H [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp AssociationState.H [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp AssociationState.H [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-- The output representation, in coordinates, is the OCP-merge and then the hull, both at the
melody tier. -/
def plateauAR (w : List AssociationState) : AR (TwoTier TRN Unit) :=
  ((w.map AssociationState.toAR).prod.collapse .upper).hull .upper

theorem link_plateauAR (w : List AssociationState) (k j : ℕ) :
    (plateauAR w).Link .upper .lower k j ↔ k = 0 ∧ .H ∈ w.take (j + 1) ∧ .H ∈ w.drop j := by
  by_cases hj : j < w.length
  · unfold plateauAR
    rw [AR.link_hull_left .upper _ (by decide)
      (by simpa using hj :
        j < (((w.map AssociationState.toAR).prod.collapse .upper).word .lower).length)]
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

/-- What surfaces is the representation. `utp.Surfaces .H w i` is the H-linkedness of timing slot
`i` in the output representation `plateauAR w`, the OCP-merged, hull-closed realization. -/
theorem utp.surfaces_iff_surfacesWith_plateauAR :
    utp.Surfaces .H w i ↔ (plateauAR w).SurfacesWith TRN.H i :=
  (surfacesWith_plateauAR w i).symm

end Tone
