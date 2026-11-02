/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Subsequential
public import Linglib.Core.Data.List.TakeDrop

/-!
# Side dependence for string functions

A string function [depends boundedly on a side](##Subregular.BoundedDependence) when one margin
serves every output coordinate: the output at `i` factors through the input not `N`-far from `i` on
that side. A length-preserving subsequential function [is bounded ahead of its
scan](##Subregular.BoundedDependence.right_of_isLeftSubsequential), so [a target flipped from
arbitrarily far on either side](##Subregular.TwoSidedUnboundedDependence) [rules out a subsequential
function in either direction](##Subregular.TwoSidedUnboundedDependence.not_isSubsequential). An
[unbounded circumambient](##Subregular.IsUnboundedCircumambient) map asks more: the change at the
target needs both sides, so a far perturbation on either side alone undoes it. Both are witnessed
by a target in a run of filler between two flanks that can be edited separately.

## Implementation notes

Coordinates index the output and the input window alike, which is informative for length-preserving
functions; for block-emitting transducers the two drift apart. A window is a list, not a set of
positions, so `BoundedDependence` factors through it without asking two inputs to have one length;
the perturbation predicates keep that condition because BMRS locality reads `w.length`.

## References

* [jardine-2016a]
* [mccollum-bakovic-mai-meinhardt-2020]
-/

@[expose] public section

namespace Subregular

open Function

variable {α β : Type*} {f : List α → List β}

/-- `f` depends boundedly on side `s` when a single margin caps, at every output
coordinate, how far input on side `s` can matter. -/
def BoundedDependence (f : List α → List β) (s : Edge) : Prop :=
  ∃ N, ∀ i, FactorsThrough (fun u ↦ (f u)[i]?) (s.window i N)

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s`. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Edge) : Prop :=
  u.length = base.length ∧ s.window i d base = s.window i d u

/-- A far perturbation leaves the target itself in place: the window on either side contains it. -/
theorem IsFarPerturbation.getElem?_eq {base u : List α} {i d : ℕ} {s : Edge}
    (h : IsFarPerturbation base u i d s) : u[i]? = base[i]? := by
  cases s
  · exact (List.drop_eq_drop_iff_getElem?.mp h.2 i (Nat.sub_le i d)).symm
  · exact (List.take_eq_take_iff_getElem?.mp h.2 i (by omega)).symm

/-- For every `d`, one base word carries a target whose output flips under a far
perturbation on either side. -/
def TwoSidedUnboundedDependence (f : List α → List β) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ (f base)[i]? ≠ (f u)[i]?

theorem TwoSidedUnboundedDependence.not_boundedDependence
    (h : TwoSidedUnboundedDependence f) (s : Edge) : ¬ BoundedDependence f s := fun ⟨N, hN⟩ ↦
  have ⟨_, i, _, hw⟩ := h N
  have ⟨_, ⟨_, hag⟩, hne⟩ := hw s
  hne (hN i hag)

/-- `f` is unbounded circumambient, (13) of [mccollum-bakovic-mai-meinhardt-2020]: for every `d`,
some target changes under `f`, and perturbing either far side leaves it with its input value. -/
def IsUnboundedCircumambient (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ (f u)[i]? = base[i]?

theorem IsUnboundedCircumambient.twoSidedUnboundedDependence {f : List α → List α}
    (hf : IsUnboundedCircumambient f) : TwoSidedUnboundedDependence f := fun d ↦
  have ⟨base, i, hi, hchange, hw⟩ := hf d
  ⟨base, i, hi, fun s ↦
    have ⟨u, hp, hrev⟩ := hw s
    ⟨u, hp, fun h ↦ hchange (h.trans hrev)⟩⟩

section FlankWitness

variable {x fill y a : α} {n k : ℕ}

/-! ### The flank-witness template

The recurring witness family: a target buried in a filler run, with independently editable
flanks. -/

/-- `flankWord x fill y n` is the word `x`, then `n` copies of `fill`, then `y`. -/
def flankWord (x fill y : α) (n : ℕ) : List α := x :: (List.replicate n fill ++ [y])

@[simp] theorem length_flankWord :
    (flankWord x fill y n).length = n + 2 := by
  simp [flankWord]

theorem getElem?_flankWord :
    (flankWord x fill y n)[k]? = if k = 0 then some x else if k = n + 1 then some y
      else if k < n + 2 then some fill else none := by
  simp only [flankWord, List.getElem?_cons, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

@[simp] theorem getElem?_flankWord_zero :
    (flankWord x fill y n)[0]? = some x := rfl

@[simp] theorem head?_flankWord : (flankWord x fill y n).head? = some x := rfl

@[simp] theorem getElem?_flankWord_last :
    (flankWord x fill y n)[n + 1]? = some y := by
  rw [getElem?_flankWord]; simp

theorem getElem?_flankWord_mid (h₁ : 0 < k) (h₂ : k ≤ n) :
    (flankWord x fill y n)[k]? = some fill := by
  rw [getElem?_flankWord]
  split_ifs <;> first | rfl | omega

theorem take_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).take (k + 1) = x :: List.replicate k fill := by
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate, Nat.min_eq_left hk]

theorem drop_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).drop (k + 1) = List.replicate (n - k) fill ++ [y] := by
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]

theorem mem_take_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).take (k + 1) ↔ x = a := by
  rw [take_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

theorem mem_drop_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).drop (k + 1) ↔ y = a := by
  rw [drop_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

theorem IsFarPerturbation.flankWord_left {i d : ℕ} (x' : α) (h : d < i) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x' fill y n) i d .left := by
  obtain ⟨k, hk⟩ : ∃ k, i - d = k + 1 := ⟨i - d - 1, by omega⟩
  exact ⟨by simp, by simp [hk, flankWord]⟩

theorem IsFarPerturbation.flankWord_right {i d : ℕ} (y' : α) (h : i + d ≤ n) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x fill y' n) i d .right :=
  ⟨by simp, by simp only [Edge.window_right, take_flankWord h]⟩

/-- A `d`-indexed family of flank words whose target's image flips under changing
either flank alone has two-sided unbounded dependence. -/
theorem TwoSidedUnboundedDependence.of_flanks {fill xOn yOn xOff yOff : α}
    {n t : ℕ → ℕ} (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hL : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]?
      ≠ (f (flankWord xOff fill yOn (n d)))[t d]?)
    (hR : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]?
      ≠ (f (flankWord xOn fill yOff (n d)))[t d]?) :
    TwoSidedUnboundedDependence f := fun d ↦ by
  refine ⟨flankWord xOn fill yOn (n d), t d, by have := hn d; simp; omega, fun s ↦ ?_⟩
  cases s
  · exact ⟨_, .flankWord_left xOff (ht d), hL d⟩
  · exact ⟨_, .flankWord_right yOff (hn d), hR d⟩

/-- A `d`-indexed family of flank words whose target sits `d`-far from both flanks,
changed in the base and reverted by flipping either flank alone, is unbounded circumambient. -/
theorem IsUnboundedCircumambient.of_flanks {f : List α → List α}
    {fill xOn yOn xOff yOff : α} {n t : ℕ → ℕ}
    (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hchange : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]? ≠ some fill)
    (hrevL : ∀ d, (f (flankWord xOff fill yOn (n d)))[t d]? = some fill)
    (hrevR : ∀ d, (f (flankWord xOn fill yOff (n d)))[t d]? = some fill) :
    IsUnboundedCircumambient f := fun d ↦ by
  have hmid : (flankWord xOn fill yOn (n d))[t d]? = some fill :=
    getElem?_flankWord_mid (by have := ht d; omega) (by have := ht d; have := hn d; omega)
  refine ⟨_, t d, by have := hn d; simp; omega, hmid ▸ hchange d, fun s ↦ ?_⟩
  cases s
  · exact ⟨_, .flankWord_left xOff (ht d), hmid ▸ hrevL d⟩
  · exact ⟨_, .flankWord_right yOff (hn d), hmid ▸ hrevR d⟩

end FlankWitness

/-! ### Machines bound dependence

The delay bound of a subsequential function is its dependence bound. -/

/-- A length-preserving left-subsequential function depends boundedly on the right. -/
theorem BoundedDependence.right_of_isLeftSubsequential
    (hlen : ∀ w, (f w).length = w.length) (hf : IsLeftSubsequential f) :
    BoundedDependence f .right :=
  have ⟨N, hN⟩ := hf.exists_getElem?_take_eq hlen
  ⟨N, fun i u v h ↦ (hN i u).symm.trans ((congrArg (fun w ↦ (f w)[i]?) h).trans (hN i v))⟩

/-- A length-preserving right-subsequential function depends boundedly on the left. -/
theorem BoundedDependence.left_of_isRightSubsequential
    (hlen : ∀ w, (f w).length = w.length) (hf : IsRightSubsequential f) :
    BoundedDependence f .left := by
  obtain ⟨N, hN⟩ := hf.exists_getElem?_drop_eq hlen
  refine ⟨N, fun i u v h ↦ ?_⟩
  rcases lt_or_ge i N with hiN | hiN
  · simpa [Nat.sub_eq_zero_of_le hiN.le] using congrArg (·[i]?) (congrArg f h)
  · exact (hN i u hiN).symm.trans ((congrArg (fun w ↦ (f w)[N]?) h).trans (hN i v hiN))

/-- A length-preserving function with two-sided unbounded dependence is subsequential in
neither direction. -/
theorem TwoSidedUnboundedDependence.not_isSubsequential (h : TwoSidedUnboundedDependence f)
    (hlen : ∀ w, (f w).length = w.length) : ∀ d, ¬ IsSubsequential d f
  | .left => fun hf ↦ h.not_boundedDependence .right (.right_of_isLeftSubsequential hlen hf)
  | .right => fun hf ↦ h.not_boundedDependence .left (.left_of_isRightSubsequential hlen hf)

end Subregular
