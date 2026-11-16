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
units surface H. Over Jardine's string rendering the map is `utp`, which writes H at the units
with an H at or before them and an H at or after them (`utp.Surfaces`, the output predicate for
H) and Ø elsewhere. [The high positions of the output are the order-connected hull of those of
the input](##Tone.highs_utp), so plateauing is a closure operator on sets of positions, and [the
words it fixes](##Tone.utp_eq_self_iff), which are its outputs, are those whose high positions
form an interval. On representations the same unit is H-linked in [the OCP-merged, hull-closed
input](##Tone.utp.surfaces_iff_surfacesWith_plateauAR). Whether a unit changes depends on
unboundedly distant material on both sides: [deleting either flanking H reverts
it](##Tone.utp_isUnboundedCircumambient).

## References

* [hyman-katamba-2010]
* [jardine-2016a]
-/

@[expose] public section

namespace Tone

open Autosegmental Subregular

/-! ### The output representation

Plateauing on representations is OCP-fusion followed by hull-closure of the association lines,
Hyman and Katamba's rule as an operation on structures. -/

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

/-! ### The plateauing map -/

/-- Unit `i` of `w` surfaces H under plateauing when an H-toned unit lies at or before it and one
at or after it. -/
def utp.Surfaces (w : List AssociationState) (i : ℕ) : Prop :=
  .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i

instance (w : List AssociationState) (i : ℕ) : Decidable (utp.Surfaces w i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Unbounded tonal plateauing writes H at the units that surface H and Ø at the others. -/
def utp (w : List AssociationState) : List AssociationState :=
  w.mapIdx fun i _ ↦ if utp.Surfaces w i then .H else .O

variable {w : List AssociationState} {i j k : ℕ}

theorem utp.surfaces_def : utp.Surfaces w i ↔ .H ∈ w.take (i + 1) ∧ .H ∈ w.drop i :=
  Iff.rfl

theorem utp.Surfaces.lt_length (h : utp.Surfaces w i) : i < w.length :=
  List.lt_length_of_mem_drop h.2

/-- An underlying H surfaces. -/
theorem utp.surfaces_of_getElem? (h : w[i]? = some .H) : utp.Surfaces w i :=
  ⟨List.mem_take_iff_getElem?.mpr ⟨_, Nat.lt_succ_self _, h⟩,
    List.mem_drop_iff_getElem?.mpr ⟨_, le_rfl, h⟩⟩

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
  ⟨w.take_subset_take_left (by omega) hi.1, w.drop_subset_drop_left (by omega) hk.2⟩

theorem utp.H_mem_of_surfaces (h : utp.Surfaces w i) : .H ∈ w :=
  List.take_subset _ _ h.1

theorem utp.surfaces_reverse (hi : i < w.length) :
    utp.Surfaces w.reverse i ↔ utp.Surfaces w (w.length - 1 - i) := by
  rw [utp.surfaces_def, utp.surfaces_def, List.take_reverse, List.drop_reverse,
    List.mem_reverse, List.mem_reverse,
    show w.length - (i + 1) = w.length - 1 - i from by omega,
    show w.length - i = (w.length - 1 - i) + 1 from by omega, and_comm]

theorem utp.surfaces_split {a : AssociationState} (h : w[i]? = some a) :
    utp.Surfaces w i ↔ a = .H ∨ (.H ∈ w.take i ∧ .H ∈ w.drop (i + 1)) := by
  rcases eq_or_ne a .H with rfl | ha
  · simp [utp.surfaces_of_getElem? h]
  · obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    rw [utp.surfaces_def, List.take_add_one, h, List.drop_eq_getElem_cons hi, hia]
    simp [ha, Ne.symm ha]

@[simp] theorem length_utp : (utp w).length = w.length := by simp [utp]

theorem getElem?_utp :
    (utp w)[i]? =
      w[i]?.map fun _ ↦ if utp.Surfaces w i then AssociationState.H else AssociationState.O := by
  simp [utp, List.getElem?_mapIdx]

theorem getElem?_utp_eq_H_iff : (utp w)[j]? = some .H ↔ utp.Surfaces w j := by
  rw [getElem?_utp]
  refine ⟨fun h ↦ ?_, fun hs ↦ by simp [hs, List.getElem?_eq_getElem hs.lt_length]⟩
  by_contra hs
  simp [hs] at h

theorem getElem?_utp_eq_O_iff :
    (utp w)[j]? = some .O ↔ j < w.length ∧ ¬ utp.Surfaces w j := by
  rw [getElem?_utp]
  rcases lt_or_ge j w.length with hj | hj
  · by_cases hs : utp.Surfaces w j <;> simp [hs, hj]
  · simp [hj.not_gt]

theorem utp_reverse : utp w.reverse = (utp w).reverse := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < w.length
  · rw [getElem?_utp, List.getElem?_reverse (by simpa using hi),
      List.getElem?_reverse (by simpa using hi), length_utp, getElem?_utp]
    simp only [utp.surfaces_reverse hi]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-! ### The plateau set -/

/-- The plateau of `w` is the set of positions that surface H. -/
def plateau (w : List AssociationState) : Finset ℕ :=
  (Finset.range w.length).filter (utp.Surfaces w)

@[simp] theorem mem_plateau : j ∈ plateau w ↔ utp.Surfaces w j := by
  simp only [plateau, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact utp.Surfaces.lt_length

@[simp] theorem plateau_nonempty : (plateau w).Nonempty ↔ .H ∈ w :=
  ⟨fun ⟨_, hj⟩ => utp.H_mem_of_surfaces (mem_plateau.mp hj), fun hw =>
    have ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
    ⟨i, mem_plateau.mpr (utp.surfaces_of_getElem? hi)⟩⟩

/-- `utp` writes the indicator word of its plateau. -/
theorem utp_eq_plateau_indicator :
    utp w
      = (List.range w.length).map fun i =>
          if i ∈ plateau w then AssociationState.H else AssociationState.O :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by simp [utp]

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

/-! ### Plateauing as a hull

The high positions of the output are the order-connected hull of the high positions of the
input. Extensivity, monotonicity and idempotence are those of the closure operator. -/

/-- The high positions of `utp w` are the order-connected hull of the high positions of `w`. -/
theorem highs_utp (w : List AssociationState) :
    highs (utp w) = Set.ordConnectedHull (highs w) := by
  ext i
  rw [Set.mem_ordConnectedHull, mem_highs, getElem?_utp_eq_H_iff, utp.surfaces_iff]
  exact ⟨fun ⟨⟨x, hx, hxH⟩, y, hy, hyH⟩ ↦ ⟨x, hxH, y, hyH, hx, hy⟩,
    fun ⟨x, hxH, y, hyH, hx, hy⟩ ↦ ⟨⟨x, hx, hxH⟩, y, hy, hyH⟩⟩

theorem coe_plateau (w : List AssociationState) :
    (plateau w : Set ℕ) = Set.ordConnectedHull (highs w) := by
  rw [← highs_utp]
  ext i
  simp [getElem?_utp_eq_H_iff]

/-- Every H survives plateauing. -/
theorem highs_subset_highs_utp (w : List AssociationState) : highs w ⊆ highs (utp w) :=
  highs_utp w ▸ Set.ordConnectedHull.le_closure _

theorem getElem?_utp_of_getElem?_eq_H (h : w[i]? = some .H) : (utp w)[i]? = some .H :=
  highs_subset_highs_utp w h

/-- Plateauing is monotone: more Hs in give more Hs out. -/
theorem highs_utp_mono {w' : List AssociationState} (h : highs w ⊆ highs w') :
    highs (utp w) ⊆ highs (utp w') := by
  rw [highs_utp, highs_utp]
  exact Set.ordConnectedHull.monotone h

theorem utp.surfaces_mono {w' : List AssociationState} (hw : highs w ⊆ highs w')
    (h : utp.Surfaces w i) : utp.Surfaces w' i :=
  getElem?_utp_eq_H_iff.mp (highs_utp_mono hw (getElem?_utp_eq_H_iff.mpr h))

theorem H_mem_utp : .H ∈ utp w ↔ .H ∈ w :=
  ⟨fun h => have ⟨_, hi⟩ := List.mem_iff_getElem?.mp h
    utp.H_mem_of_surfaces (getElem?_utp_eq_H_iff.mp hi),
   fun h => have ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    List.mem_iff_getElem?.mpr ⟨i, getElem?_utp_of_getElem?_eq_H hi⟩⟩

/-- Plateauing is idempotent, a plateau being already closed. -/
@[simp] theorem utp_utp (w : List AssociationState) : utp (utp w) = utp w :=
  eq_of_highs_eq (by simp) <| by
    rw [highs_utp, highs_utp]
    exact Set.ordConnectedHull.idempotent _

theorem utp.surfaces_utp : utp.Surfaces (utp w) i ↔ utp.Surfaces w i := by
  rw [← getElem?_utp_eq_H_iff, ← getElem?_utp_eq_H_iff, utp_utp]

@[simp] theorem plateau_utp : plateau (utp w) = plateau w := by
  ext j
  rw [mem_plateau, mem_plateau, utp.surfaces_utp]

/-! ### The outputs of plateauing

A word is an output of plateauing exactly when plateauing fixes it, and it is fixed exactly when
its high positions form an interval, that is, when it has no `H O H` subsequence. -/

/-- Plateauing fixes the words whose high positions are order-connected. -/
theorem utp_eq_self_iff : utp w = w ↔ (highs w).OrdConnected := by
  rw [← Set.ordConnectedHull_eq_self_iff, ← highs_utp]
  exact ⟨fun h ↦ by rw [h], fun h ↦ eq_of_highs_eq (by simp) h⟩

theorem utp_eq_self_iff_forall : utp w = w ↔ ∀ i, utp.Surfaces w i → w[i]? = some .H := by
  rw [utp_eq_self_iff, ← Set.ordConnectedHull_eq_self_iff, ← highs_utp]
  exact ⟨fun h i hi ↦ h.subset (getElem?_utp_eq_H_iff.mpr hi), fun h ↦ Set.Subset.antisymm
    (fun i hi ↦ h i (getElem?_utp_eq_H_iff.mp hi)) (highs_subset_highs_utp w)⟩

theorem range_utp : Set.range utp = Function.fixedPoints utp :=
  Set.ext fun w => ⟨fun ⟨_, hv⟩ => hv ▸ utp_utp _, fun h => ⟨w, h⟩⟩

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
theorem mem_range_utp_iff : w ∈ Set.range utp ↔ w ∉ Language.shuffleIdeal [.H, .O, .H] := by
  rw [range_utp, Function.mem_fixedPoints, Function.IsFixedPt, utp_eq_self_iff_forall,
    Language.mem_shuffleIdeal, HOH_sublist_iff]
  push Not
  refine forall_congr' fun i ↦ ⟨fun h hs ↦ by simp [h hs], fun h hs ↦ ?_⟩
  have := hs.lt_length
  cases ha : w[i]? with
  | none => simp_all
  | some a => cases a <;> simp_all

/-! ### The plateauing rule

The rule schemata as theorems about `utp`, not clauses of its definition. -/

/-- A toneless word is unchanged. -/
theorem utp_replicate_O (n : ℕ) : utp (List.replicate n .O) = List.replicate n .O := by
  have h : plateau (List.replicate n AssociationState.O) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp (by simp)
  simp [utp_eq_plateau_indicator, h, List.map_const']

/-- A word with a single H is unchanged — one H cannot trigger a plateau. -/
theorem utp_single (m n : ℕ) :
    utp (List.replicate m .O ++ .H :: List.replicate n .O)
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
    utp (List.replicate m .O ++ .H :: (w ++ .H :: List.replicate p .O))
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
example : utp [.O, .O, .O, .H] = [.O, .O, .O, .H] := by decide
example : utp [.H, .O, .O, .O] = [.H, .O, .O, .O] := by decide
example : utp [.H, .O, .O, .H] = [.H, .H, .H, .H] := by decide

/-! ### Unbounded circumambience -/

/-- Plateauing is unbounded circumambient: a toneless unit between two flanking Hs surfaces H at
every distance, and deleting either flank leaves it toneless. -/
theorem utp_isUnboundedCircumambient : IsUnboundedCircumambient utp :=
  .of_flanks (fill := .O) (xOn := .H) (yOn := .H) (xOff := .O) (yOff := .O)
    (n := fun d ↦ 2 * d + 2) (t := fun d ↦ d + 1) (fun d ↦ by omega) (fun d ↦ by omega)
    (fun d ↦ by
      rw [getElem?_utp_eq_H_iff.mpr ⟨(mem_take_flankWord_iff (by decide) (by omega)).mpr rfl,
        (mem_drop_flankWord_iff (by decide) (by omega)).mpr rfl⟩]
      decide)
    (fun d ↦ getElem?_utp_eq_O_iff.mpr ⟨by rw [length_flankWord]; omega, fun hs ↦
      absurd ((mem_take_flankWord_iff (by decide) (by omega)).mp hs.1) (by decide)⟩)
    (fun d ↦ getElem?_utp_eq_O_iff.mpr ⟨by rw [length_flankWord]; omega, fun hs ↦
      absurd ((mem_drop_flankWord_iff (by decide) (by omega)).mp hs.2) (by decide)⟩)

theorem utp_twoSidedUnboundedDependence : TwoSidedUnboundedDependence utp :=
  utp_isUnboundedCircumambient.twoSidedUnboundedDependence

end Tone
