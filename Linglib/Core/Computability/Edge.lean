/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Order.Nat
public import Linglib.Core.Data.List.DropRight

/-!
# Edges of a word

An `Edge` is an end of a word, `left` for its beginning and `right` for its end. The same two
values name a scan by the end it starts from, and a side of a position by the end it faces. This
file gives a word as the scan from an edge reads it, the length-`k` part of a word at an edge,
the part within a distance of a target on one side, and the reverse conjugation that exchanges
the two edges on string functions.

## Main definitions

* `Edge`, `Edge.swap`: the left or right end of a word, and the other one.
* `Edge.orient`: a word as the scan from an edge reads it.
* `Edge.takeAt`: the length-`k` prefix or suffix of a word.
* `Edge.window`: the part of a word not far from a target on one side.
* `List.revConj`: conjugation of a string function by reversal.
-/

@[expose] public section

variable {α : Type*}

/-- An `Edge` is an end of a word, `left` for its beginning and `right` for its end. A scan is
named by the edge it starts from, so the `left` scan reads a word from its beginning and the
`right` scan from its end. The two scans give function classes that are mirror images under
reversal but differ as classes of functions on unreversed strings. -/
inductive Edge | left | right
  deriving DecidableEq, Repr, Fintype

namespace Edge

/-- The other edge. -/
def swap : Edge → Edge
  | left => right
  | right => left

@[simp] theorem swap_left : left.swap = right := rfl

@[simp] theorem swap_right : right.swap = left := rfl

@[simp] theorem swap_swap (e : Edge) : e.swap.swap = e := by cases e <;> rfl

theorem swap_involutive : Function.Involutive swap := swap_swap

/-! ### Reading from an edge -/

/-- A word as the scan from an edge reads it, unchanged from the left and reversed from the
right. -/
def orient : Edge → List α → List α
  | left, xs => xs
  | right, xs => xs.reverse

@[simp] theorem orient_left (xs : List α) : left.orient xs = xs := rfl

@[simp] theorem orient_right (xs : List α) : right.orient xs = xs.reverse := rfl

@[simp] theorem orient_orient (e : Edge) (xs : List α) : e.orient (e.orient xs) = xs := by
  cases e <;> simp

theorem orient_involutive (e : Edge) : Function.Involutive (e.orient (α := α)) :=
  e.orient_orient

theorem orient_injective (e : Edge) : Function.Injective (e.orient (α := α)) :=
  e.orient_involutive.injective

@[simp] theorem orient_inj {e : Edge} {xs ys : List α} : e.orient xs = e.orient ys ↔ xs = ys :=
  e.orient_injective.eq_iff

@[simp] theorem length_orient (e : Edge) (xs : List α) : (e.orient xs).length = xs.length := by
  cases e <;> simp

theorem map_orient {β : Type*} (e : Edge) (f : α → β) (xs : List α) :
    (e.orient xs).map f = e.orient (xs.map f) := by
  cases e <;> simp

theorem filter_orient (e : Edge) (p : α → Bool) (xs : List α) :
    (e.orient xs).filter p = e.orient (xs.filter p) := by
  cases e <;> simp [List.filter_reverse]

/-! ### Edge substrings -/

variable (e : Edge) (k : ℕ) (xs : List α)

/-- The length-`k` part of `xs` at an edge, its prefix `List.take` at the left and its suffix
`List.rtake` at the right. A word shorter than `k` is returned in full. -/
def takeAt : List α :=
  match e with
  | .left  => xs.take k
  | .right => xs.rtake k

@[simp] lemma takeAt_left : Edge.left.takeAt k xs = xs.take k := rfl

@[simp] lemma takeAt_right : Edge.right.takeAt k xs = xs.rtake k := rfl

/-- An edge substring has length `min k xs.length`. -/
lemma length_takeAt : (e.takeAt k xs).length = min k xs.length := by
  cases e <;> simp

/-- For a short string the edge substring is the whole string. -/
lemma takeAt_of_length_le {k : ℕ} {xs : List α} (h : xs.length ≤ k) :
    e.takeAt k xs = xs := by
  cases e with
  | left => exact List.take_of_length_le h
  | right => exact List.rtake_of_length_le h

/-- The left-`k`-prefix of `p ++ rest` is that of `p`, when `k ≤ p.length`. -/
lemma takeAt_left_append_of_le_length {k : ℕ} (p rest : List α) (h : k ≤ p.length) :
    Edge.left.takeAt k (p ++ rest) = Edge.left.takeAt k p :=
  List.take_append_of_le_length h

/-- The right-`k`-suffix of `x ++ rest` is that of `rest`, when `k ≤ rest.length`. -/
lemma takeAt_right_append_of_le_length {k : ℕ} (x rest : List α) (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest :=
  List.rtake_append_of_le_length h

/-- `takeAt k` is idempotent, since its output already has length at most `k`. -/
lemma takeAt_idem : e.takeAt k (e.takeAt k xs) = e.takeAt k xs :=
  takeAt_of_length_le e (by rw [length_takeAt]; exact min_le_left _ _)

/-- A shorter edge substring of a longer one is the shorter edge substring. -/
lemma takeAt_takeAt_of_le {k k' : ℕ} (h : k ≤ k') (xs : List α) :
    e.takeAt k (e.takeAt k' xs) = e.takeAt k xs := by
  cases e <;> simp [List.take_take, List.rtake_rtake, h]

/-- Words with the same edge substring of some length have the same shorter ones. -/
lemma takeAt_eq_of_le {k k' : ℕ} (h : k ≤ k') {xs xs' : List α}
    (hxs : e.takeAt k' xs = e.takeAt k' xs') : e.takeAt k xs = e.takeAt k xs' := by
  rw [← takeAt_takeAt_of_le e h, hxs, takeAt_takeAt_of_le e h]

/-- Truncating the first factor of a concatenation to its edge substring leaves the edge substring
of the whole unchanged. -/
lemma takeAt_takeAt_append (ys : List α) :
    e.takeAt k (e.takeAt k xs ++ ys) = e.takeAt k (xs ++ ys) := by
  cases e with
  | left =>
    rcases le_total k xs.length with h | h
    · simp [List.take_append_of_le_length, h]
    · simp [List.take_of_length_le h]
  | right => exact List.rtake_append_rtake k xs ys

/-- Words with the same edge substring keep the same one after appending a word. -/
lemma takeAt_append_congr {k : ℕ} {xs xs' : List α} (h : e.takeAt k xs = e.takeAt k xs')
    (ys : List α) : e.takeAt k (xs ++ ys) = e.takeAt k (xs' ++ ys) := by
  rw [← takeAt_takeAt_append, h, takeAt_takeAt_append]

/-- Truncating the second factor of a concatenation to its edge substring leaves the edge
substring of the whole unchanged. -/
lemma takeAt_append_takeAt (ys : List α) :
    e.takeAt k (xs ++ e.takeAt k ys) = e.takeAt k (xs ++ ys) := by
  cases e with
  | left => simp [List.take_append, List.take_take]
  | right =>
    rcases le_total k ys.length with h | h
    · simp [List.rtake_append_of_le_length, List.rtake_rtake, h]
    · simp [List.rtake_of_length_le h]

/-- Words with the same edge substring keep the same one after prepending a word. -/
lemma takeAt_append_congr_right {k : ℕ} {ys ys' : List α} (h : e.takeAt k ys = e.takeAt k ys')
    (xs : List α) : e.takeAt k (xs ++ ys) = e.takeAt k (xs ++ ys') := by
  rw [← takeAt_append_takeAt, h, takeAt_append_takeAt]

/-- Mapping a function over a word maps it over the edge substring. -/
lemma takeAt_map {β : Type*} (g : α → β) : e.takeAt k (xs.map g) = (e.takeAt k xs).map g := by
  cases e <;> simp [List.rtake, List.map_take, List.map_drop]

/-- Over a finite alphabet there are finitely many edge substrings of a given length. -/
lemma finite_range_takeAt [Finite α] : (Set.range (e.takeAt (α := α) k)).Finite :=
  (List.finite_length_le α k).subset (Set.range_subset_iff.2 fun w ↦ by simp [length_takeAt])

/-! ### Windows -/

/-- The part of a word not `d`-far from the target `i` on the side of an edge: its suffix from
`i - d` on the left, its prefix through `i + d` on the right. -/
def window : Edge → ℕ → ℕ → List α → List α
  | .left, i, d => List.drop (i - d)
  | .right, i, d => List.take (i + d + 1)

@[simp, grind =] theorem window_left {i d : ℕ} : Edge.left.window i d xs = xs.drop (i - d) := rfl

@[simp, grind =] theorem window_right {i d : ℕ} :
    Edge.right.window i d xs = xs.take (i + d + 1) := rfl

end Edge

/-! ### Reverse conjugation

Exchanging the two edges acts on string functions by reverse conjugation. The right-scan function
classes are the `List.revConj`-images of the left-scan ones, so their theory transports along the
involution. -/

namespace List

variable {α β γ : Type*}

/-- Conjugation by `List.reverse` computes on the reversed input and reverses the result. -/
def revConj (f : List α → List β) : List α → List β := fun xs ↦ (f xs.reverse).reverse

@[simp] theorem revConj_revConj (f : List α → List β) : revConj (revConj f) = f := by
  funext xs; simp [revConj]

theorem revConj_comp (g : List β → List γ) (f : List α → List β) :
    revConj (g ∘ f) = revConj g ∘ revConj f := by
  funext xs; simp [revConj]

@[simp] theorem revConj_id : revConj (id : List α → List α) = id := by
  funext xs; simp [revConj]

@[simp] theorem revConj_map (h : α → β) : revConj (List.map h) = List.map h := by
  funext xs; simp [revConj]

/-- Pulling a language back along a reverse-conjugate reverses the pullback of the
reversed language. -/
theorem preimage_revConj (f : List α → List β) (L : Language β) :
    revConj f ⁻¹' L = Language.reverse (f ⁻¹' L.reverse) :=
  rfl

theorem revConj_eq_iff {h : List α → List β} {f : List α → List β} :
    revConj h = f ↔ h = revConj f := by
  constructor <;> rintro rfl <;> simp

end List

