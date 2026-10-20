/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Monotone.Basic
public import Linglib.Core.Data.List.Destutter

/-!
# The Obligatory Contour Principle

The Obligatory Contour Principle (OCP) bans two identical adjacent autosegments on one tier.
Here it is categorical and bans strict identity, either on the tier itself (`IsClean`, after
Leben and McCarthy) or on a projection of it (`IsCleanOn`). Fusion, `collapse`, repairs a
violation by merging each run of identical elements into one; it is `List.destutter (· ≠ ·)`, a
retraction onto the clean tiers, as `List.dedup` is onto the lists without duplicates.
`mergeAppend` concatenates two words and merges identical elements at the seam only; the collapse
of a concatenation is the merging append of the collapses. The run index `runIdx` tracks where
each position lands under fusion.

The gradient OCP of Frisch, Pierrehumbert and Broe, which scales with the similarity of the two
consonants, is a different object and lives in that paper's study.

## Main definitions

* `OCP.IsClean`, `OCP.IsCleanOn`: no two identical adjacent elements, on the tier or on a
  projection of it.
* `OCP.collapse`: the fusion repair.
* `OCP.mergeAppend`: concatenation that merges identical elements at the seam.
* `OCP.runIdx`: the index of the run containing a position.

## Main statements

* `OCP.isClean_collapse`, `OCP.collapse_eq_self_iff`: `collapse` lands in the clean tiers and
  fixes exactly them.
* `OCP.collapse_append`: the collapse of a concatenation is the merging append of the
  collapses.
* `OCP.runIdx_append_left`, `OCP.runIdx_append_right`: the run indices of a concatenation.

## References

* [leben-1973]
* [goldsmith-1976]
* [mccarthy-1986]
* [mccarthy-prince-1995]
* [frisch-pierrehumbert-broe-2004]
* [jardine-heinz-2015]
-/

@[expose] public section

namespace OCP

variable {α β : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no two adjacent elements are identical. This is weaker than
`List.Nodup`, since `[1, 2, 1]` is clean. It is a reducible alias of `List.IsChain (· ≠ ·)`, so
that API applies. -/
abbrev IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

/-- The OCP on the tier projected from `xs` by keeping the `p`-elements and reading them
through `proj`. Flat `IsClean` is the case `p = ⊤`, `proj = id`. -/
def IsCleanOn (p : α → Prop) [DecidablePred p] (proj : α → β) (xs : List α) : Prop :=
  IsClean ((xs.filter (fun a ↦ decide (p a))).map proj)

instance decidableIsCleanOn [DecidableEq β] (p : α → Prop)
    [DecidablePred p] (proj : α → β) : DecidablePred (IsCleanOn p proj) :=
  fun _ ↦ inferInstanceAs (Decidable (IsClean _))

section
variable [DecidableEq α]

/-! ### The fusion repair -/

/-- The **fusion repair** merges each maximal run of identical adjacent elements into one. -/
def collapse (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem collapse_eq_destutter (xs : List α) : collapse xs = xs.destutter (· ≠ ·) := rfl

@[simp] theorem collapse_nil : collapse ([] : List α) = [] := by simp [collapse]

@[simp] theorem collapse_singleton (x : α) : collapse [x] = [x] := by simp [collapse]

/-- `collapse` fuses a constant run into its single autosegment. -/
@[simp] theorem collapse_replicate (n : ℕ) (a : α) :
    collapse (List.replicate (n + 1) a) = [a] :=
  List.destutter_replicate (fun h ↦ h rfl) n

/-- `collapse` lands in the OCP-clean set. -/
theorem isClean_collapse (xs : List α) : IsClean (collapse xs) :=
  List.isChain_destutter _ xs

/-- `collapse` fixes OCP-clean lists. -/
protected theorem IsClean.collapse_eq {xs : List α} (h : IsClean xs) : collapse xs = xs :=
  List.destutter_of_isChain _ xs h

/-- `collapse` fixes exactly the OCP-clean tiers, so with `isClean_collapse` it is a retraction
onto them. -/
@[simp] theorem collapse_eq_self_iff (xs : List α) : collapse xs = xs ↔ IsClean xs :=
  List.destutter_eq_self_iff _ xs

/-- The fusion repair is a retraction onto the OCP-clean set. -/
@[simp] theorem collapse_idem (xs : List α) : collapse (collapse xs) = collapse xs :=
  List.destutter_idem _ _

/-! ### Normal-form lemmas -/

@[simp] theorem collapse_eq_nil {xs : List α} : collapse xs = [] ↔ xs = [] :=
  List.destutter_eq_nil _

/-- The output of the fusion repair is a sublist of its input. -/
theorem collapse_sublist (xs : List α) : (collapse xs).Sublist xs :=
  List.destutter_sublist _ xs

/-! ### Merging at a seam

Appending with the seam merged drops the head of the second word when it repeats the last
element of the first; this is Jardine and Heinz's concatenation on a single tier. On clean words
it is the collapse of the concatenation, and the collapse of any concatenation is the merging
append of the collapses. -/

/-- Append `ys` to `xs`, dropping the head of `ys` when it repeats the last element of `xs`. -/
def mergeAppend (xs ys : List α) : List α :=
  if xs.getLast? = ys.head? then xs ++ ys.tail else xs ++ ys

/-- The position at which `ys` starts in `mergeAppend xs ys`. -/
def mergeOffset (xs ys : List α) : ℕ :=
  if xs.getLast? = ys.head? then xs.length - 1 else xs.length

/-- The position in `mergeAppend xs ys` of position `p` of `xs ++ ys`. -/
def mergeIdx (xs ys : List α) (p : ℕ) : ℕ :=
  if p < xs.length then p else mergeOffset xs ys + (p - xs.length)

variable {xs ys zs : List α}

@[simp] theorem nil_mergeAppend (ys : List α) : mergeAppend [] ys = ys := by
  cases ys <;> simp [mergeAppend]

@[simp] theorem mergeAppend_nil (xs : List α) : mergeAppend xs [] = xs := by
  unfold mergeAppend
  split_ifs with h <;> simp_all

@[simp] theorem mergeOffset_nil_left (ys : List α) : mergeOffset [] ys = 0 := by
  unfold mergeOffset
  split_ifs <;> rfl

theorem length_mergeAppend (xs ys : List α) :
    (mergeAppend xs ys).length = mergeOffset xs ys + ys.length := by
  unfold mergeAppend mergeOffset
  split_ifs with h
  · rcases xs with _ | ⟨x, xs⟩ <;> rcases ys with _ | ⟨y, ys⟩ <;> simp_all
    omega
  · simp

theorem getLast?_mergeAppend (hys : ys ≠ []) : (mergeAppend xs ys).getLast? = ys.getLast? := by
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hys
  unfold mergeAppend
  split_ifs with h
  · rcases t with _ | ⟨z, t⟩
    · simpa using h
    · exact List.getLast?_append_of_ne_nil _ (List.cons_ne_nil z t)
  · exact List.getLast?_append_of_ne_nil _ (List.cons_ne_nil y t)

theorem head?_mergeAppend (hxs : xs ≠ []) : (mergeAppend xs ys).head? = xs.head? := by
  unfold mergeAppend
  split_ifs <;> exact List.head?_append_of_ne_nil _ hxs

theorem mergeAppend_assoc (xs ys zs : List α) :
    mergeAppend (mergeAppend xs ys) zs = mergeAppend xs (mergeAppend ys zs) := by
  rcases eq_or_ne ys [] with rfl | hys
  · simp
  have hl := getLast?_mergeAppend (xs := xs) hys
  have hh := head?_mergeAppend (ys := zs) hys
  conv_lhs => rw [mergeAppend, hl]
  conv_rhs => rw [mergeAppend, hh]
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hys
  unfold mergeAppend
  split_ifs <;> simp

theorem mergeOffset_congr_right (h : ys.head? = zs.head?) :
    mergeOffset xs ys = mergeOffset xs zs := by
  simp [mergeOffset, h]

theorem mergeOffset_mergeAppend_right (hys : ys ≠ []) :
    mergeOffset xs (mergeAppend ys zs) = mergeOffset xs ys :=
  mergeOffset_congr_right (head?_mergeAppend hys)

theorem mergeOffset_mergeAppend_left (xs ys zs : List α) :
    mergeOffset (mergeAppend xs ys) zs =
      mergeOffset xs (mergeAppend ys zs) + mergeOffset ys zs := by
  rcases eq_or_ne ys [] with rfl | hys
  · simp
  have hpos := List.length_pos_iff.mpr hys
  rw [mergeOffset_mergeAppend_right hys]
  conv_lhs => rw [mergeOffset, getLast?_mergeAppend hys, length_mergeAppend]
  conv_rhs => arg 2; rw [mergeOffset]
  split_ifs <;> omega

theorem mergeIdx_of_lt {p : ℕ} (h : p < xs.length) : mergeIdx xs ys p = p := by
  simp [mergeIdx, h]

@[simp] theorem mergeIdx_length_add (a : ℕ) :
    mergeIdx xs ys (xs.length + a) = mergeOffset xs ys + a := by
  simp [mergeIdx]

theorem mergeIdx_monotone : Monotone (mergeIdx xs ys) := by
  intro p q hpq
  have : xs.length - 1 ≤ mergeOffset xs ys := by unfold mergeOffset; split_ifs <;> omega
  unfold mergeIdx
  split_ifs <;> omega

theorem mergeIdx_lt {p : ℕ} (h : p < xs.length + ys.length) :
    mergeIdx xs ys p < (mergeAppend xs ys).length := by
  rw [length_mergeAppend]
  unfold mergeIdx mergeOffset
  split_ifs with hp hc
  · have : ys ≠ [] := by rintro rfl; rcases xs with _ | ⟨x, xs⟩ <;> simp_all
    have := List.length_pos_iff.mpr this
    omega
  all_goals omega

/-- On clean words, merging at the seam is collapsing the concatenation. -/
theorem collapse_append_of_isClean (hx : IsClean xs) (hy : IsClean ys) :
    collapse (xs ++ ys) = mergeAppend xs ys :=
  List.IsChain.destutter_ne_append hx hy

/-- **The OCP congruence.** The collapse of a concatenation is the merging append of the
collapses. -/
theorem collapse_append (xs ys : List α) :
    collapse (xs ++ ys) = mergeAppend (collapse xs) (collapse ys) := by
  rw [← collapse_append_of_isClean (isClean_collapse xs) (isClean_collapse ys)]
  exact (List.destutter_append_destutter xs ys).symm

/-- Fusion keeps the last element. -/
@[simp] theorem getLast?_collapse (xs : List α) : (collapse xs).getLast? = xs.getLast? := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x _ =>
    rw [collapse_append, collapse_singleton, getLast?_mergeAppend (List.cons_ne_nil _ _)]
    simp

/-- A symbol appended to a word fuses with the word's last element when it repeats it. -/
theorem collapse_append_singleton (xs : List α) (x : α) :
    collapse (xs ++ [x]) = if xs.getLast? = some x then collapse xs else collapse xs ++ [x] := by
  rw [collapse_append, collapse_singleton, mergeAppend, getLast?_collapse]
  simp

@[simp] theorem mem_collapse {a : α} {xs : List α} : a ∈ collapse xs ↔ a ∈ xs := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [collapse_append_singleton]
    split_ifs with h
    · simpa [ih] using fun hax ↦ hax ▸ List.mem_of_getLast? h
    · simp [ih]

/-- Merging at the seam keeps clean words clean. -/
theorem isClean_mergeAppend (hx : IsClean xs) (hy : IsClean ys) : IsClean (mergeAppend xs ys) :=
  collapse_append_of_isClean hx hy ▸ isClean_collapse _

end

/-! ### The run-index map -/

section RunIndex
variable {α : Type*} [DecidableEq α] {xs ys : List α}

/-- The **run index** of position `k` in `xs` is the 0-based index of the run of identical
elements containing it, one less than the number of runs in `xs.take (k + 1)`. -/
def runIdx (xs : List α) (k : ℕ) : ℕ := (collapse (xs.take (k + 1))).length - 1

/-- Later positions sit in the same or later runs. -/
theorem runIdx_monotone (xs : List α) : Monotone (runIdx xs) := by
  intro a b hab
  unfold runIdx
  have hsub : (collapse (xs.take (a + 1))).Sublist (xs.take (b + 1)) :=
    (collapse_sublist _).trans (List.take_sublist_take_left (by omega))
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (isClean_collapse _)
  simp only [collapse_eq_destutter] at hlen ⊢
  omega

/-- The collapse of a nonempty prefix has its top run index plus one elements. -/
private theorem length_collapse_take_succ {m : ℕ} (hm : m < xs.length) :
    (collapse (xs.take (m + 1))).length = runIdx xs m + 1 := by
  have hpos : 0 < (collapse (xs.take (m + 1))).length := by
    rw [List.length_pos_iff, Ne, collapse_eq_nil, ← List.length_eq_zero_iff,
      List.length_take_of_le (by omega)]
    omega
  unfold runIdx
  omega

/-- An in-bounds position has an in-bounds run index in the collapsed tier. -/
theorem runIdx_lt_collapse_length (xs : List α) {k : ℕ} (hk : k < xs.length) :
    runIdx xs k < (collapse xs).length := by
  have hsub : (collapse (xs.take (k + 1))).Sublist xs :=
    (collapse_sublist _).trans (List.take_sublist _ _)
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (isClean_collapse _)
  rw [← collapse_eq_destutter, length_collapse_take_succ hk] at hlen
  omega

/-- On a constant tier every position lies in the single run. -/
@[simp] theorem runIdx_replicate (n : ℕ) (a : α) (k : ℕ) :
    runIdx (List.replicate n a) k = 0 := by
  unfold runIdx
  rw [List.take_replicate]
  cases hm : min (k + 1) n with
  | zero => simp
  | succ m => rw [collapse_replicate, List.length_singleton]

/-- On a clean tier `runIdx` is the identity. -/
theorem runIdx_clean (hc : IsClean xs) {k : ℕ} (h : k < xs.length) : runIdx xs k = k := by
  unfold runIdx
  rw [IsClean.collapse_eq (hc.take (k + 1)), List.length_take_of_le (by omega)]
  omega

/-! ### Run indices of a concatenation

A position of `xs ++ ys` keeps its run index in `xs` when it lies in `xs`; a position in `ys`
moves to its run index in `ys`, offset by where `collapse ys` starts in the merging append of
the collapses. -/

/-- The run index of a prefix position is unaffected by a right append. -/
theorem runIdx_append_left {k : ℕ} (h : k < xs.length) : runIdx (xs ++ ys) k = runIdx xs k := by
  unfold runIdx
  rw [List.take_append_of_le_length (by omega)]

/-- The run index of a suffix position is its run index in the suffix, offset by where the
collapsed suffix starts in the merging append of the collapses. -/
theorem runIdx_append_right {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      mergeOffset (collapse xs) (collapse ys) + runIdx ys a := by
  have h := length_collapse_take_succ (xs := xs ++ ys) (m := xs.length + a) (by simp; omega)
  have hhead : (collapse (ys.take (a + 1))).head? = (collapse ys).head? := by
    rw [collapse, collapse, List.head?_destutter, List.head?_destutter]
    cases ys <;> simp_all
  rw [show xs.length + a + 1 = xs.length + (a + 1) by omega, List.take_length_add_append,
    collapse_append, length_mergeAppend, length_collapse_take_succ ha,
    mergeOffset_congr_right hhead] at h
  omega

end RunIndex

end OCP
