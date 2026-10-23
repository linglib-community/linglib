/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.WordOrder
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.Card
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Dependency length

The length of a dependency is the distance in words between head and dependent. This file defines
the total dependency length of a graph, transports a graph along a permutation of its positions,
and defines the distance from a head to the nearest word of a dependent's yield, dependency length
measured to the boundary of the dependent's phrase. On a projective tree that distance is one
more than the sizes of the yields of the sibling dependents between head and dependent: it is the
block measure `WordOrder.Arrangement.boundaryDist` with yields as blocks. Summed over the elements
after a head, the block measure weighs each element's length by the number of elements farther
out, so by the rearrangement inequality an order whose lengths grow outward is shortest: this is
Behaghel's law of growing constituents, and its mirror image orders long before short before a
final head.

## Main definitions

* `Graph.totalLength`: the sum of `Nat.dist` over the arcs.
* `Graph.map`: a graph transported along a permutation of its positions; `Graph.mirror` and
  `Graph.linearize` read it in reverse and in a given order.
* `Graph.yieldDist`: the distance from a position to the nearest word of a yield.
* `WordOrder.Arrangement.boundaryDist`: the distance in words between two constituents of given
  lengths in an arrangement.
* `Graph.siblingArrangement`: a head and its dependents in the order of their positions.

## Main results

* `Graph.totalLength_map`: transport along an isometry preserves total dependency length.
* `Graph.yieldDist_eq_one_add_sum`: on a projective tree, the yield distance from a head to a
  dependent is one more than the yield sizes of the dependents between them.
* `WordOrder.Arrangement.sum_boundaryDist_after_le`: Behaghel's law, no rearrangement of the
  elements after a head is shorter than the order whose lengths grow outward.
* `Graph.sum_yieldDist_eq_sum_boundaryDist`: on a projective tree a head's yield distances are
  the boundary distances of its sibling arrangement with phrase lengths.

## References

* [behaghel-1909]
* [futrell-levy-gibson-2020]
* [fedzechkina-chu-jaeger-2018]
-/

@[expose] public section

namespace WordOrder.Arrangement

open Finset

variable {α : Type*} {n : ℕ}

section Monovary

variable {a : Arrangement α n} (ℓ : α → ℕ)

theorem monovaryOn_mirror_iff {s : Set α} : MonovaryOn ℓ a.mirror s ↔ AntivaryOn ℓ a s := by
  simp only [MonovaryOn, AntivaryOn, mirror, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev]
  exact ⟨fun h i hi j hj hij ↦ h hj hi hij, fun h i hi j hj hij ↦ h hj hi hij⟩

private theorem antivaryOn_rank_iff_monovaryOn {s : Set α} :
    AntivaryOn ℓ (fun d ↦ n - 1 - a d) s ↔ MonovaryOn ℓ a s := by
  constructor <;> intro h i hi j hj hij <;> refine h hj hi ?_ <;>
    · have := (a j).isLt
      have := (a i).isLt
      simp only [Fin.lt_def] at hij ⊢
      omega

end Monovary

section Fintype

variable [Fintype α]

section after

variable {a : Arrangement α n} {x : α}

theorem card_after (d : α) : #(a.after d) = n - 1 - a d := by
  rw [← Fin.card_Ioi, ← card_map a.toEmbedding]
  congr 1; ext j
  simp only [mem_map, mem_after, Precedes, Equiv.coe_toEmbedding, mem_Ioi]
  exact ⟨fun ⟨c, hc, hj⟩ ↦ hj ▸ hc, fun h ↦ ⟨a.symm j, by simpa using h, by simp⟩⟩

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.after x))
include hσ

theorem apply_eq_self_of_notMem_after {c : α} (hc : c ∉ a.after x) : σ c = c := by
  by_contra h
  exact hc (hσ h)

theorem mem_after_apply_of_mem {c : α} (hc : c ∈ a.after x) : σ c ∈ a.after x := by
  by_cases h : σ c = c
  · rwa [h]
  · exact hσ fun h' ↦ h (σ.injective h')

theorem precedes_trans_iff_of_notMem_after {c d : α} (hc : c ∉ a.after x) :
    (Precedes (σ.trans a) c d ↔ a.Precedes c d) ∧ (Precedes (σ.trans a) d c ↔ a.Precedes d c) := by
  simp only [Precedes, Equiv.trans_apply, apply_eq_self_of_notMem_after hσ hc]
  by_cases hd : d ∈ a.after x
  · have h₁ := mem_after.1 (mem_after_apply_of_mem hσ hd)
    have h₂ := mem_after.1 hd
    simp only [mem_after, Precedes, Fin.lt_def, not_lt] at h₁ h₂ hc
    simp only [Fin.lt_def]
    constructor <;> constructor <;> intro <;> omega
  · rw [apply_eq_self_of_notMem_after hσ hd]; exact ⟨Iff.rfl, Iff.rfl⟩

theorem after_trans : after (σ.trans a) x = a.after x := by
  ext c
  simp only [mem_after]
  exact (precedes_trans_iff_of_notMem_after hσ notMem_after_self).1

end after

variable [DecidableEq α] (a : Arrangement α n) (ℓ : α → ℕ) (x y : α)

/-- The distance in words between the closest boundaries of `x` and `y` when each element `c` is
`ℓ c` words long, which is one more than the words of the elements between them and zero from an
element to itself. -/
def boundaryDist : ℕ :=
  if x = y then 0 else
    1 + ∑ c with a.Precedes x c ∧ a.Precedes c y ∨ a.Precedes y c ∧ a.Precedes c x, ℓ c

@[simp] theorem boundaryDist_self : a.boundaryDist ℓ x x = 0 := by simp [boundaryDist]

theorem boundaryDist_comm : a.boundaryDist ℓ x y = a.boundaryDist ℓ y x := by
  simp only [boundaryDist, eq_comm (a := x), or_comm]

@[simp] theorem boundaryDist_mirror : a.mirror.boundaryDist ℓ x y = a.boundaryDist ℓ x y := by
  simp only [boundaryDist, precedes_mirror, and_comm, or_comm]

section Behaghel

variable {a x}

theorem sum_boundaryDist_after :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c =
      #(a.after x) + ∑ d ∈ a.after x, ℓ d * (n - 1 - a d) := by
  have hx : ∀ c ∈ a.after x, a.boundaryDist ℓ x c =
      1 + ∑ c' with a.Precedes x c' ∧ a.Precedes c' c ∨ a.Precedes c c' ∧ a.Precedes c' x,
        ℓ c' := by
    intro c hc
    rw [boundaryDist, ite_eq_right]
    rintro rfl
    exact notMem_after_self hc
  rw [sum_congr rfl hx]
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, add_right_inj]
  calc ∑ c ∈ a.after x, ∑ d with a.Precedes x d ∧ a.Precedes d c ∨ a.Precedes c d ∧
          a.Precedes d x, ℓ d
      = ∑ c ∈ a.after x, ∑ d ∈ a.after x with a.Precedes d c, ℓ d := by
        refine sum_congr rfl fun c hc ↦ ?_
        rw [mem_after] at hc
        rw [after, filter_filter]
        refine sum_congr (filter_congr fun d _ ↦ ?_) fun _ _ ↦ rfl
        constructor
        · rintro (h | ⟨h₁, h₂⟩)
          · exact h
          · exact absurd (hc.trans h₁) h₂.asymm
        · exact Or.inl
    _ = ∑ d ∈ a.after x, ∑ c ∈ a.after x with a.Precedes d c, ℓ d := by
        simp only [sum_filter]
        rw [Finset.sum_comm]
    _ = ∑ d ∈ a.after x, ℓ d * (n - 1 - a d) := by
        refine sum_congr rfl fun d hd ↦ ?_
        rw [sum_const, smul_eq_mul, mul_comm, ← card_after]
        congr 2
        ext c
        simp only [mem_filter, mem_after]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨(mem_after.1 hd).trans h, h⟩⟩

section perm

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.after x))
include hσ

theorem boundaryDist_trans_of_notMem_after {c : α} (hc : c ∉ a.after x) :
    boundaryDist (σ.trans a) ℓ x c = a.boundaryDist ℓ x c := by
  have hx := notMem_after_self (a := a) (x := x)
  simp only [boundaryDist, (precedes_trans_iff_of_notMem_after hσ hx).1,
    (precedes_trans_iff_of_notMem_after hσ hx).2, (precedes_trans_iff_of_notMem_after hσ hc).1,
    (precedes_trans_iff_of_notMem_after hσ hc).2]

/-- Behaghel's law of growing constituents ([behaghel-1909]). When the lengths of the elements
after `x` grow outward (`ℓ` monovaries with rank, short before long), no rearrangement of them
shortens the distance from `x` to them. -/
theorem sum_boundaryDist_after_le (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c ≤
      ∑ c ∈ after (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c := by
  rw [sum_boundaryDist_after, sum_boundaryDist_after, after_trans hσ]
  refine Nat.add_le_add_left ?_ _
  simpa [Equiv.trans_apply] using
    ((antivaryOn_rank_iff_monovaryOn ℓ).2 h).sum_mul_le_sum_mul_comp_perm hσ

theorem sum_boundaryDist_after_lt_iff (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c ∈ a.after x, a.boundaryDist ℓ x c <
      ∑ c ∈ after (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c ↔
      ¬ MonovaryOn ℓ (σ.trans a) (after (σ.trans a) x) := by
  rw [sum_boundaryDist_after, sum_boundaryDist_after, after_trans hσ, add_lt_add_iff_left,
    ← antivaryOn_rank_iff_monovaryOn]
  simpa [Equiv.trans_apply, Function.comp_def] using
    ((antivaryOn_rank_iff_monovaryOn ℓ).2 h).sum_mul_lt_sum_mul_comp_perm_iff hσ

theorem sum_boundaryDist_le (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c, a.boundaryDist ℓ x c ≤ ∑ c, boundaryDist (σ.trans a) ℓ x c := by
  rw [← sum_filter_add_sum_filter_not univ (a.Precedes x ·),
    ← sum_filter_add_sum_filter_not univ (a.Precedes x ·)]
  refine Nat.add_le_add ?_ (le_of_eq ?_)
  · have := sum_boundaryDist_after_le (ℓ := ℓ) hσ h
    rwa [after_trans hσ] at this
  · refine sum_congr rfl fun c hc ↦ (boundaryDist_trans_of_notMem_after ℓ hσ ?_).symm
    simpa using (mem_filter.1 hc).2

theorem sum_boundaryDist_lt_iff (h : MonovaryOn ℓ a (a.after x)) :
    ∑ c, a.boundaryDist ℓ x c < ∑ c, boundaryDist (σ.trans a) ℓ x c ↔
      ¬ MonovaryOn ℓ (σ.trans a) (after (σ.trans a) x) := by
  have e : ∑ c with ¬ a.Precedes x c, boundaryDist (σ.trans a) ℓ x c =
      ∑ c with ¬ a.Precedes x c, a.boundaryDist ℓ x c :=
    sum_congr rfl fun c hc ↦
      boundaryDist_trans_of_notMem_after ℓ hσ (by simpa using (mem_filter.1 hc).2)
  rw [← sum_filter_add_sum_filter_not univ (a.Precedes x ·),
    ← sum_filter_add_sum_filter_not univ (a.Precedes x ·), e, add_lt_add_iff_right,
    ← sum_boundaryDist_after_lt_iff ℓ hσ h, after_trans hσ]
  exact Iff.rfl

end perm

section before

variable {σ : Equiv.Perm α} (hσ : {c | σ c ≠ c} ⊆ ↑(a.before x))
include hσ

theorem sum_boundaryDist_before_le (h : AntivaryOn ℓ a (a.before x)) :
    ∑ c ∈ a.before x, a.boundaryDist ℓ x c ≤
      ∑ c ∈ before (σ.trans a) x, boundaryDist (σ.trans a) ℓ x c := by
  have h' : {c | σ c ≠ c} ⊆ ↑(a.mirror.after x) := by rwa [← before_eq_after_mirror]
  have e : ∀ b : Arrangement α n, ∑ c ∈ b.before x, b.boundaryDist ℓ x c =
      ∑ c ∈ b.mirror.after x, b.mirror.boundaryDist ℓ x c := fun b ↦ by
    rw [before_eq_after_mirror]
    exact sum_congr rfl fun c _ ↦ (boundaryDist_mirror ..).symm
  rw [e, e]
  exact sum_boundaryDist_after_le (a := a.mirror) ℓ h'
    ((monovaryOn_mirror_iff ℓ).2 ((before_eq_after_mirror (a := a) (x := x)) ▸ h))

end before

end Behaghel

end Fintype

end WordOrder.Arrangement

namespace DependencyGrammar

open Relation

variable {n : ℕ}

/-- Total dependency length sums `Nat.dist` over all arcs, the quantity dependency-length
minimisation is about. -/
def Graph.totalLength (g : Graph n) : Nat :=
  ∑ v : Fin n, ∑ w ∈ g.children v, Nat.dist v w

theorem Graph.totalLength_words (g : Graph n) (words' : Fin n → Morphology.Word) :
    Graph.totalLength { g with words := words' } = g.totalLength := rfl

/-! ### Transport: same structure, different linearization -/

/-- `g.map σ` transports `g` along the position permutation `σ`. Arcs, tokens and root move
together, so the labeled structure is unchanged and only the linearization varies. -/
def Graph.map (g : Graph n) (σ : Equiv.Perm (Fin n)) : Graph n :=
  { words := g.words ∘ σ.symm
    label := fun v w ↦ g.label (σ.symm v) (σ.symm w)
    root := σ g.root }

@[simp] theorem Graph.map_adj (g : Graph n) (σ : Equiv.Perm (Fin n))
    (v w : Fin n) : (g.map σ).Adj v w ↔ g.Adj (σ.symm v) (σ.symm w) :=
  Iff.rfl

/-- The mirror image, transported along position reversal. -/
def Graph.mirror (g : Graph n) : Graph n := g.map Fin.revPerm

/-- Transport along an isometry of the positions preserves total dependency length. -/
theorem Graph.totalLength_map (g : Graph n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v w : Fin n, Nat.dist (σ v) (σ w) = Nat.dist v w) :
    (g.map σ).totalLength = g.totalLength := by
  unfold totalLength
  simp only [Graph.children, Finset.sum_filter]
  refine Fintype.sum_equiv σ.symm _ _ (fun v ↦ ?_)
  refine Fintype.sum_equiv σ.symm _ _ (fun w ↦ ?_)
  simp only [map_adj]
  by_cases h : g.Adj (σ.symm v) (σ.symm w) <;>
    simp [h, ← hσ (σ.symm v) (σ.symm w)]

theorem _root_.Fin.dist_rev_rev (v w : Fin n) :
    Nat.dist v.rev w.rev = Nat.dist v w := by
  have hv := v.isLt
  have hw := w.isLt
  simp only [Nat.dist, Fin.val_rev]
  omega

/-- The mirror image of a graph has the same total dependency length ([futrell-levy-gibson-2020],
examples (7)–(8)). -/
theorem Graph.totalLength_mirror (g : Graph n) :
    g.mirror.totalLength = g.totalLength :=
  g.totalLength_map _ Fin.dist_rev_rev

/-- The graph read in the order `order`, which lists every position once. The token at
position `p` is the token of `g` at `order[p]`, arcs and root following. -/
def Graph.linearize (g : Graph n) (order : List (Fin n)) (h : order.Perm (List.finRange n)) :
    Graph n :=
  g.map ((finCongr (h.length_eq.trans List.length_finRange).symm).trans
    ((h.nodup_iff.mpr (List.nodup_finRange n)).getEquivOfForallMemList order
      fun x ↦ h.mem_iff.mpr (List.mem_finRange x))).symm

theorem Graph.linearize_words (g : Graph n) (order : List (Fin n))
    (h : order.Perm (List.finRange n)) (p : Fin n) :
    (g.linearize order h).words p =
      g.words (order.get (Fin.cast (h.length_eq.trans List.length_finRange).symm p)) :=
  rfl

/-! ### Arc length and the dependent's phrase -/

theorem Graph.ncard_yield_le_dist (g : Graph n) {v w : Fin n} (hv : v ∉ g.yield w)
    (h : ∀ x ∈ g.yield w, x ∈ Set.uIcc v w) : (g.yield w).ncard ≤ Nat.dist v w := by
  have hsub : g.yield w ⊆ Set.uIcc v w \ {v} := Set.subset_sdiff_singleton h hv
  refine (Set.ncard_le_ncard hsub).trans (le_of_eq ?_)
  rw [Set.ncard_sdiff_singleton_of_mem Set.left_mem_uIcc, Set.ncard_uIcc, Fin.card_uIcc,
    Nat.add_sub_cancel]
  simp only [Nat.dist]
  omega

/-! ### Distance to a phrase -/

theorem Graph.toFinset_yield_nonempty (g : Graph n) (w : Fin n) : (g.yield w).toFinset.Nonempty :=
  ⟨w, by simp [ReflTransGen.refl]⟩

/-- The distance from `v` to the nearest word of the yield of `w`, dependency length measured to
the closest boundary of the dependent's phrase. -/
def Graph.yieldDist (g : Graph n) (v w : Fin n) : ℕ :=
  (g.yield w).toFinset.inf' (g.toFinset_yield_nonempty w) fun x ↦ Nat.dist v x

theorem Graph.yieldDist_le_dist (g : Graph n) (v w : Fin n) : g.yieldDist v w ≤ Nat.dist v w :=
  Finset.inf'_le _ (by simp [ReflTransGen.refl])

variable {g : Graph n} {v w : Fin n}

/-- An order-connected set through a point strictly between `a` and `b` and avoiding both lies
strictly between them. -/
private theorem _root_.Set.OrdConnected.between {S : Set (Fin n)} (hS : S.OrdConnected)
    {a b x y : Fin n}
    (hx : x ∈ S) (hy : y ∈ S) (hxab : a < x ∧ x < b ∨ b < x ∧ x < a) (ha : a ∉ S)
    (hb : b ∉ S) : a < y ∧ y < b ∨ b < y ∧ y < a := by
  have key : ∀ z, (x ≤ z ∧ z ≤ y ∨ y ≤ z ∧ z ≤ x) → z ∈ S := fun z hz ↦
    hS.uIcc_subset hx hy (Set.mem_uIcc.2 hz)
  by_contra hc
  rcases hxab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases le_or_gt y a with hya | hay
    · exact ha (key a (Or.inr ⟨hya, h1.le⟩))
    · exact hb (key b (Or.inl ⟨h2.le, not_lt.1 fun hyb ↦ hc (Or.inl ⟨hay, hyb⟩)⟩))
  · rcases le_or_gt y b with hyb | hby
    · exact hb (key b (Or.inr ⟨hyb, h1.le⟩))
    · exact ha (key a (Or.inl ⟨h2.le, not_lt.1 fun hya ↦ hc (Or.inr ⟨hby, hya⟩)⟩))

private theorem card_between {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a).card + 1 = Nat.dist a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · have e : (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a) = Finset.Ioo a b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, Fin.lt_def] at h ⊢
      omega
    rw [e, Fin.card_Ioo]
    simp only [Nat.dist, Fin.lt_def] at h ⊢
    omega
  · have e : (Finset.univ.filter fun x ↦ a < x ∧ x < b ∨ b < x ∧ x < a) = Finset.Ioo b a := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, Fin.lt_def] at h ⊢
      omega
    rw [e, Fin.card_Ioo]
    simp only [Nat.dist, Fin.lt_def] at h ⊢
    omega

/-- On a projective tree the distance from a head to the nearest word of a dependent's phrase is
one more than the phrase sizes of the dependents between them. -/
theorem Graph.yieldDist_eq_one_add_sum (hT : g.IsTree) (hP : g.IsProjective) (h : g.Adj v w) :
    g.yieldDist v w = 1 + ∑ u ∈ g.children v with (v < u ∧ u < w ∨ w < u ∧ u < v),
      (g.yield u).ncard := by
  classical
  obtain ⟨m, hmY, hm⟩ := Finset.exists_mem_eq_inf' (g.toFinset_yield_nonempty w)
    fun x ↦ Nat.dist v x
  have hmY : m ∈ g.yield w := by simpa using hmY
  have hvY := hT.not_dominates_of_adj h
  have hmin : ∀ y ∈ g.yield w, Nat.dist v m ≤ Nat.dist v y := fun y hy ↦
    hm ▸ Finset.inf'_le _ (by simpa using hy)
  have hgap : ∀ y ∈ g.yield w, ¬ (v < y ∧ y < m ∨ m < y ∧ y < v) := by
    intro y hy hb
    have := hmin y hy
    simp only [Nat.dist, Fin.lt_def] at this hb
    omega
  -- m lies between v and every point of the phrase
  have hside : ∀ y ∈ g.yield w, v < m ∧ m ≤ y ∨ y ≤ m ∧ m < v := by
    intro y hy
    have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
    have hy' : ¬ (m < v ∧ v < y ∨ y < v ∧ v < m) := fun hb ↦
      hvY ((hP w).uIcc_subset hmY hy (Set.mem_uIcc.2 (by
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inl ⟨h1.le, h2.le⟩;
          exact Or.inr ⟨h1.le, h2.le⟩])))
    have hg := hgap y hy
    have hyv : y ≠ v := fun e ↦ hvY (e ▸ hy)
    simp only [Fin.lt_def, Fin.le_def, ne_eq, Fin.ext_iff] at hg hy' hyv hvm ⊢
    omega
  have hiff : ∀ x, (v < x ∧ x < m ∨ m < x ∧ x < v) ↔
      ∃ u ∈ g.children v, (v < u ∧ u < w ∨ w < u ∧ u < v) ∧ x ∈ g.yield u := by
    intro x
    constructor
    · intro hx
      have hxv : x ∈ g.yield v := (hP v).uIcc_subset .refl (ReflTransGen.head h hmY)
        (Set.mem_uIcc.2 (by
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inl ⟨h1.le, h2.le⟩;
            exact Or.inr ⟨h1.le, h2.le⟩]))
      have hne : x ≠ v := by rintro rfl; simp at hx
      obtain ⟨u, hvu, hxu⟩ := g.exists_adj_mem_yield hxv hne
      have hxY : x ∉ g.yield w := fun hxY ↦ hgap x hxY hx
      have huw : u ≠ w := by rintro rfl; exact hxY hxu
      have hdis := hT.disjoint_yield_of_adj hvu h huw
      have hb := (hP u).between hxu (ReflTransGen.refl) hx (hT.not_dominates_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
      have hs := hside w ReflTransGen.refl
      refine ⟨u, by simpa using hvu, ?_, hxu⟩
      simp only [Fin.lt_def, Fin.le_def] at hb hs ⊢
      omega
    · rintro ⟨u, hu, hb, hxu⟩
      have hvu : g.Adj v u := by simpa using hu
      have huw : u ≠ w := by rintro rfl; simp at hb
      have hdis := hT.disjoint_yield_of_adj hvu h huw
      have huY : u ∉ g.yield w := Set.disjoint_left.1 hdis ReflTransGen.refl
      have hs := hside w ReflTransGen.refl
      -- u lies strictly between v and m
      have hum : v < u ∧ u < m ∨ m < u ∧ u < v := by
        have hmw : ¬ (m ≤ u ∧ u ≤ w ∨ w ≤ u ∧ u ≤ m) := fun hc ↦
          huY ((hP w).uIcc_subset hmY ReflTransGen.refl (Set.mem_uIcc.2 hc))
        simp only [Fin.lt_def, Fin.le_def] at hb hs hmw ⊢
        omega
      exact (hP u).between ReflTransGen.refl hxu hum (hT.not_dominates_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
  have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
  have hT' : (Finset.univ.filter fun x ↦ v < x ∧ x < m ∨ m < x ∧ x < v) =
      (g.children v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v).biUnion
        fun u ↦ Finset.univ.filter (· ∈ g.yield u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hiff]
    constructor
    · rintro ⟨u, hu, hb, hx⟩; exact ⟨u, ⟨hu, hb⟩, hx⟩
    · rintro ⟨u, ⟨hu, hb⟩, hx⟩; exact ⟨u, hu, hb, hx⟩
  have hdisj : ((g.children v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v) : Set (Fin n)
      ).PairwiseDisjoint fun u ↦ Finset.univ.filter (· ∈ g.yield u) := by
    intro u hu u' hu' hne
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Graph.mem_children] at hu hu'
    simpa [Function.onFun, Finset.disjoint_filter] using
      Set.disjoint_left.1 (hT.disjoint_yield_of_adj hu.1 hu'.1 hne)
  rw [Graph.yieldDist, hm, ← card_between hvm, hT', Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext; simp

/-! ### A head's dependents as an arrangement -/

section Siblings

open Finset WordOrder

variable (g : Graph n) (v : Fin n)

/-- A head together with its dependents. -/
def Graph.siblings : Finset (Fin n) := insert v (g.children v)

/-- The rank of a sibling counts the siblings before it. -/
def Graph.siblingRank (c : g.siblings v) : Fin #(g.siblings v) :=
  ⟨#{d ∈ g.siblings v | d < (c : Fin n)}, card_lt_card (filter_ssubset.2 ⟨c, c.2, lt_irrefl _⟩)⟩

theorem Graph.siblingRank_strictMono : StrictMono (g.siblingRank v) := fun c d hcd ↦ by
  have hcd' : (c : Fin n) < d := Subtype.coe_lt_coe.2 hcd
  simp only [Graph.siblingRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun _ _ he ↦ lt_trans he hcd')).2
    ⟨c, mem_filter.2 ⟨c.2, hcd'⟩, by simp⟩)

/-- A head and its dependents arranged by position. The inverse is classical, but `Precedes`
reads only the rank, which the kernel reduces. -/
noncomputable def Graph.siblingArrangement : Arrangement (g.siblings v) #(g.siblings v) :=
  Equiv.ofBijective (g.siblingRank v)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(g.siblingRank_strictMono v).injective, by simp⟩)

/-- The phrase length of a position is the number of words of its yield. -/
def Graph.phraseLength (c : Fin n) : ℕ := #(g.yield c).toFinset

theorem Graph.phraseLength_eq_ncard (c : Fin n) : g.phraseLength c = (g.yield c).ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

@[simp] theorem Graph.self_mem_siblings : v ∈ g.siblings v := mem_insert_self _ _

variable {g v}

theorem Graph.mem_siblings_of_adj {w : Fin n} (h : g.Adj v w) : w ∈ g.siblings v :=
  mem_insert_of_mem (by simpa using h)

@[simp] theorem Graph.siblingArrangement_precedes {c d : g.siblings v} :
    (g.siblingArrangement v).Precedes c d ↔ (c : Fin n) < d :=
  (g.siblingRank_strictMono v).lt_iff_lt.trans Subtype.coe_lt_coe.symm

theorem Graph.yieldDist_eq_boundaryDist (hT : g.IsTree) (hP : g.IsProjective) {w : Fin n}
    (h : g.Adj v w) :
    g.yieldDist v w = (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c)
      ⟨v, g.self_mem_siblings v⟩ ⟨w, Graph.mem_siblings_of_adj h⟩ := by
  have hvw : v ≠ w := fun e ↦ hT.not_dominates_of_adj h (e ▸ ReflTransGen.refl)
  rw [Graph.yieldDist_eq_one_add_sum hT hP h, Arrangement.boundaryDist, ite_eq_right (by simpa)]
  congr 1
  simp only [Graph.siblingArrangement_precedes, Graph.phraseLength_eq_ncard, sum_filter]
  refine Eq.trans ?_ (sum_coe_sort (g.siblings v)
    fun c ↦ if v < c ∧ c < w ∨ w < c ∧ c < v then (g.yield c).ncard else 0).symm
  rw [Graph.siblings, sum_insert (by simpa using hT.not_adj_self), ite_eq_right (by simp),
    zero_add]

/-- The sum of a head's yield distances is the head's measure in the sibling arrangement. -/
theorem Graph.sum_yieldDist_eq_sum_boundaryDist (hT : g.IsTree) (hP : g.IsProjective) :
    ∑ w ∈ g.children v, g.yieldDist v w =
      ∑ c, (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c)
        ⟨v, g.self_mem_siblings v⟩ c := by
  rw [← sum_erase univ (Arrangement.boundaryDist_self ..)]
  refine sum_bij' (fun w hw ↦ ⟨w, Graph.mem_siblings_of_adj (by simpa using hw)⟩)
    (fun c _ ↦ c.1) (fun w hw ↦ ?_) (fun c hc ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun w hw ↦ Graph.yieldDist_eq_boundaryDist hT hP (by simpa using hw)
  · simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq]
    rintro rfl
    exact hT.not_adj_self (by simpa using hw)
  · obtain ⟨c, hc'⟩ := c
    simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq] at hc
    simpa [Graph.siblings, hc] using hc'

end Siblings

end DependencyGrammar
