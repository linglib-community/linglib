/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Core.Data.Finset.Sort
public import Linglib.Syntax.WordOrder.BoundaryDistance
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.Card
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Dependency length

The length of a dependency is the distance in words between its head and its dependent. For a
digraph `G` on the positions of a sentence, the total dependency length `G.totalLength` is the sum
of `Nat.dist v w` over the arcs from `v` to `w`. A dependency is at least one word long, so the
total dependency length is at least the number of arcs, with equality exactly when every dependent
stands next to its head.

We also define the distance `G.reachSetDist v w` from a position `v` to the nearest position of
the yield of `w`. On a projective forest, the distance from a head to the yield of a dependent is
one more than the sizes of the yields of the dependents between them. This is the boundary
distance `WordOrder.Arrangement.boundaryDist` of the local arrangement, with the yields as blocks.

## Main definitions

* `Digraph.totalLength`: the sum of `Nat.dist` over the arcs.
* `Digraph.reachSetDist`: the distance from a position to the nearest word of a yield.
* `Digraph.localArrangement`: a head and its dependents in the order of their positions.

## Main results

* `Digraph.totalLength_comap_symm`: transport along an isometry preserves total dependency length.
  In particular the mirror image of a digraph has the same length (`Digraph.totalLength_mirror`).
* `Digraph.card_arcs_le_totalLength` and `Digraph.totalLength_eq_card_arcs_iff`: the total
  dependency length is at least the number of arcs, with equality exactly when every dependent
  stands next to its head.
* `Digraph.totalLength_le_totalLength_comap`: a digraph in which every dependent stands next to
  its head is no longer than any reordering of its positions.
* `Digraph.card_arcs_lt_totalLength`: the bound is not attained when a head has two dependents on
  one side.
* `Digraph.reachSetDist_eq_one_add_sum`: on a projective forest, the distance from a head to the
  yield of a dependent is one more than the sizes of the yields of the dependents between them.
* `Digraph.sum_reachSetDist_eq_sum_boundaryDist`: on a projective forest, the distances from a
  head to the yields of its dependents sum to its boundary distances in the local arrangement.

## References

* [behaghel-1909]
* [futrell-levy-gibson-2020]
* [gildea-temperley-2007]
* [fedzechkina-chu-jaeger-2018]
-/

@[expose] public section


open Relation

variable {n : ℕ}

section Transport

variable (G : Digraph (Fin n)) [DecidableRel G.Adj]

/-- The total dependency length of a digraph on positions is the sum of `Nat.dist v w` over its arcs
from `v` to `w`. -/
def Digraph.totalLength : ℕ :=
  ∑ v : Fin n, ∑ w ∈ G.outNeighborFinset v, Nat.dist v w

/-! ### Transport -/

omit [DecidableRel G.Adj] in
theorem Digraph.mirror_comap_symm (σ : Equiv.Perm (Fin n)) :
    (G.comap σ.symm).mirror = G.comap (WordOrder.Arrangement.mirror σ).symm :=
  rfl

theorem Digraph.totalLength_comap_symm_eq_sum (σ : Equiv.Perm (Fin n)) :
    (G.comap σ.symm).totalLength = ∑ u, ∑ w ∈ G.outNeighborFinset u, Nat.dist (σ u) (σ w) := by
  unfold Digraph.totalLength
  simp only [Digraph.outNeighborFinset, Finset.sum_filter]
  refine Fintype.sum_equiv σ.symm _ _ fun u ↦ Fintype.sum_equiv σ.symm _ _ fun w ↦ ?_
  simp [Digraph.comap_adj]

theorem Digraph.totalLength_comap_symm (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v w : Fin n, Nat.dist (σ v) (σ w) = Nat.dist v w) :
    (G.comap σ.symm).totalLength = G.totalLength := by
  rw [Digraph.totalLength_comap_symm_eq_sum]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun w _ ↦ hσ u w

theorem _root_.Fin.dist_rev_rev (v w : Fin n) :
    Nat.dist v.rev w.rev = Nat.dist v w := by
  have hv := v.isLt
  have hw := w.isLt
  simp only [Nat.dist, Fin.val_rev]
  omega

theorem Digraph.totalLength_mirror : G.mirror.totalLength = G.totalLength :=
  G.totalLength_comap_symm Fin.revPerm Fin.dist_rev_rev

@[simp] theorem Digraph.totalLength_comap_mirror_symm (σ : Equiv.Perm (Fin n)) :
    (G.comap (WordOrder.Arrangement.mirror σ).symm).totalLength =
      (G.comap σ.symm).totalLength := by
  rw [Digraph.totalLength_comap_symm_eq_sum, Digraph.totalLength_comap_symm_eq_sum]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun w _ ↦ Fin.dist_rev_rev _ _

end Transport

/-! ### The lower bound -/

section LowerBound

open Finset

@[simp] theorem Digraph.card_arcs_comap (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin n)) : #(G.comap σ).arcs = #G.arcs :=
  card_equiv (σ.prodCongr σ) fun ⟨v, w⟩ ↦ by simp

@[simp] theorem Digraph.card_arcs_mirror (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    #G.mirror.arcs = #G.arcs :=
  G.card_arcs_comap Fin.revPerm

variable {G : Digraph (Fin n)} [DecidableRel G.Adj]

private theorem Digraph.one_le_dist_of_mem_outNeighborFinset (h : ∀ v, ¬ G.Adj v v) (v : Fin n) :
    ∀ w ∈ G.outNeighborFinset v, 1 ≤ Nat.dist v w := fun w hw ↦
  Nat.dist_pos_of_ne (Fin.val_ne_of_ne fun e ↦ h v (by simpa [← e] using hw))

/-- The total dependency length of a digraph without loops is at least the number of its arcs. -/
theorem Digraph.card_arcs_le_totalLength (h : ∀ v, ¬ G.Adj v v) : #G.arcs ≤ G.totalLength := by
  rw [G.card_arcs]
  exact sum_le_sum fun v _ ↦ card_eq_sum_ones (G.outNeighborFinset v) ▸
    sum_le_sum (Digraph.one_le_dist_of_mem_outNeighborFinset h v)

/-- The total dependency length equals the number of arcs exactly when every dependent stands next
to its head. -/
theorem Digraph.totalLength_eq_card_arcs_iff (h : ∀ v, ¬ G.Adj v v) :
    G.totalLength = #G.arcs ↔ ∀ ⦃v w⦄, G.Adj v w → Nat.dist v w = 1 := by
  rw [G.card_arcs, eq_comm, Digraph.totalLength]
  simp only [card_eq_sum_ones]
  rw [sum_eq_sum_iff_of_le fun v _ ↦ sum_le_sum (Digraph.one_le_dist_of_mem_outNeighborFinset h v)]
  refine forall_congr' fun v ↦ ?_
  rw [sum_eq_sum_iff_of_le (Digraph.one_le_dist_of_mem_outNeighborFinset h v)]
  simp [eq_comm]

theorem Digraph.totalLength_le_totalLength_comap (h : ∀ v, ¬ G.Adj v v)
    (h₁ : ∀ ⦃v w⦄, G.Adj v w → Nat.dist v w = 1) (σ : Equiv.Perm (Fin n)) :
    G.totalLength ≤ (G.comap σ).totalLength := by
  rw [(Digraph.totalLength_eq_card_arcs_iff h).2 h₁, ← G.card_arcs_comap σ]
  exact Digraph.card_arcs_le_totalLength fun v hv ↦ h _ hv

theorem Digraph.card_arcs_lt_totalLength (h : ∀ v, ¬ G.Adj v v) {d : HeadDirection}
    {v w₁ w₂ : Fin n} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂) (hne : w₁ ≠ w₂)
    (o₁ : d.Orders v w₁) (o₂ : d.Orders v w₂) : #G.arcs < G.totalLength := by
  refine (Digraph.card_arcs_le_totalLength h).lt_of_ne fun e ↦ hne ?_
  have hd := (Digraph.totalLength_eq_card_arcs_iff h).1 e.symm
  have e₁ := hd h₁
  have e₂ := hd h₂
  cases d <;>
    simp only [HeadDirection.headInitial_orders, HeadDirection.headFinal_orders, Fin.lt_def,
      Nat.dist] at o₁ o₂ e₁ e₂ <;>
    exact Fin.ext (by omega)

end LowerBound

/-! ### Arc length and the dependent's phrase -/

theorem Digraph.ncard_reachSet_le_dist (G : Digraph (Fin n)) [DecidableRel G.Adj] {v w : Fin n}
    (hv : v ∉ G.reachSet w)
    (h : ∀ x ∈ G.reachSet w, x ∈ Set.uIcc v w) : (G.reachSet w).ncard ≤ Nat.dist v w := by
  have hsub : G.reachSet w ⊆ Set.uIcc v w \ {v} := Set.subset_sdiff_singleton h hv
  refine (Set.ncard_le_ncard hsub).trans (le_of_eq ?_)
  rw [Set.ncard_sdiff_singleton_of_mem Set.left_mem_uIcc, Set.ncard_uIcc, Fin.card_uIcc,
    Nat.add_sub_cancel]
  simp only [Nat.dist]
  omega

/-! ### Distance to a phrase -/

theorem Digraph.toFinset_reachSet_nonempty (G : Digraph (Fin n)) [DecidableRel G.Adj] (w : Fin n) :
    (G.reachSet w).toFinset.Nonempty :=
  ⟨w, by simp [ReflTransGen.refl]⟩

/-- The distance from `v` to the nearest position of the yield of `w`. -/
def Digraph.reachSetDist (G : Digraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n) : ℕ :=
  (G.reachSet w).toFinset.inf' (G.toFinset_reachSet_nonempty w) fun x ↦ Nat.dist v x

theorem Digraph.reachSetDist_le_dist (G : Digraph (Fin n)) [DecidableRel G.Adj] (v w : Fin n) :
    G.reachSetDist v w ≤ Nat.dist v w :=
  Finset.inf'_le _ (by simp [ReflTransGen.refl])

variable {G : Digraph (Fin n)} [DecidableRel G.Adj] {v w : Fin n}

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

/-- On a projective forest, the distance from a head to the yield of a dependent is one more than
the sizes of the yields of the dependents between them. -/
theorem Digraph.reachSetDist_eq_one_add_sum (hF : G.IsBranching) (hP : G.IsProjective)
    (h : G.Adj v w) :
    G.reachSetDist v w = 1 + ∑ u ∈ G.outNeighborFinset v with (v < u ∧ u < w ∨ w < u ∧ u < v),
      (G.reachSet u).ncard := by
  classical
  obtain ⟨m, hmY, hm⟩ := Finset.exists_mem_eq_inf' (G.toFinset_reachSet_nonempty w)
    fun x ↦ Nat.dist v x
  have hmY : m ∈ G.reachSet w := by simpa using hmY
  have hvY := hF.not_reachable_of_adj h
  have hmin : ∀ y ∈ G.reachSet w, Nat.dist v m ≤ Nat.dist v y := fun y hy ↦
    hm ▸ Finset.inf'_le _ (by simpa using hy)
  have hgap : ∀ y ∈ G.reachSet w, ¬ (v < y ∧ y < m ∨ m < y ∧ y < v) := by
    intro y hy hb
    have := hmin y hy
    simp only [Nat.dist, Fin.lt_def] at this hb
    omega
  -- m lies between v and every point of the phrase
  have hside : ∀ y ∈ G.reachSet w, v < m ∧ m ≤ y ∨ y ≤ m ∧ m < v := by
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
      ∃ u ∈ G.outNeighborFinset v, (v < u ∧ u < w ∨ w < u ∧ u < v) ∧ x ∈ G.reachSet u := by
    intro x
    constructor
    · intro hx
      have hxv : x ∈ G.reachSet v := (hP v).uIcc_subset .refl (ReflTransGen.head h hmY)
        (Set.mem_uIcc.2 (by
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inl ⟨h1.le, h2.le⟩;
            exact Or.inr ⟨h1.le, h2.le⟩]))
      have hne : x ≠ v := by rintro rfl; simp at hx
      obtain ⟨u, hvu, hxu⟩ := G.exists_adj_mem_reachSet hxv hne
      have hxY : x ∉ G.reachSet w := fun hxY ↦ hgap x hxY hx
      have huw : u ≠ w := by rintro rfl; exact hxY hxu
      have hdis := hF.disjoint_reachSet_of_adj hvu h huw
      have hb := (hP u).between hxu (ReflTransGen.refl) hx (hF.not_reachable_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
      have hs := hside w ReflTransGen.refl
      refine ⟨u, by simpa using hvu, ?_, hxu⟩
      simp only [Fin.lt_def, Fin.le_def] at hb hs ⊢
      omega
    · rintro ⟨u, hu, hb, hxu⟩
      have hvu : G.Adj v u := by simpa using hu
      have huw : u ≠ w := by rintro rfl; simp at hb
      have hdis := hF.disjoint_reachSet_of_adj hvu h huw
      have huY : u ∉ G.reachSet w := Set.disjoint_left.1 hdis ReflTransGen.refl
      have hs := hside w ReflTransGen.refl
      -- u lies strictly between v and m
      have hum : v < u ∧ u < m ∨ m < u ∧ u < v := by
        have hmw : ¬ (m ≤ u ∧ u ≤ w ∨ w ≤ u ∧ u ≤ m) := fun hc ↦
          huY ((hP w).uIcc_subset hmY ReflTransGen.refl (Set.mem_uIcc.2 hc))
        simp only [Fin.lt_def, Fin.le_def] at hb hs hmw ⊢
        omega
      exact (hP u).between ReflTransGen.refl hxu hum (hF.not_reachable_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
  have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
  have hfilter : (Finset.univ.filter fun x ↦ v < x ∧ x < m ∨ m < x ∧ x < v) =
      (G.outNeighborFinset v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v).biUnion
        fun u ↦ Finset.univ.filter (· ∈ G.reachSet u) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hiff]
    constructor
    · rintro ⟨u, hu, hb, hx⟩; exact ⟨u, ⟨hu, hb⟩, hx⟩
    · rintro ⟨u, ⟨hu, hb⟩, hx⟩; exact ⟨u, hu, hb, hx⟩
  have hdisj : ((G.outNeighborFinset v |>.filter fun u ↦ v < u ∧ u < w ∨ w < u ∧ u < v) :
      Set (Fin n)).PairwiseDisjoint fun u ↦ Finset.univ.filter (· ∈ G.reachSet u) := by
    intro u hu u' hu' hne
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Digraph.mem_outNeighborFinset] at hu hu'
    simpa [Function.onFun, Finset.disjoint_filter] using
      Set.disjoint_left.1 (hF.disjoint_reachSet_of_adj hu.1 hu'.1 hne)
  rw [Digraph.reachSetDist, hm, ← card_between hvm, hfilter, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext; simp

/-! ### Distance to a phrase as a boundary distance -/

section LocalSubtree

open Finset WordOrder

variable (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

/-- The arrangement of a local subtree in the order of its positions. -/
noncomputable def Digraph.localArrangement : Arrangement (G.localSubtree v) #(G.localSubtree v) :=
  (G.localSubtree v).rankOrderIso.toEquiv

variable {G v}

@[simp] theorem Digraph.localArrangement_precedes {c d : G.localSubtree v} :
    (G.localArrangement v).Precedes c d ↔ (c : Fin n) < d :=
  (G.localSubtree v).rankOrderIso.lt_iff_lt.trans Subtype.coe_lt_coe.symm

theorem Digraph.reachSetDist_eq_boundaryDist (hF : G.IsBranching) (hP : G.IsProjective) {w : Fin n}
    (h : G.Adj v w) :
    G.reachSetDist v w = (G.localArrangement v).boundaryDist (fun c ↦ #(G.reachSet c).toFinset)
      ⟨v, G.self_mem_localSubtree v⟩ ⟨w, Digraph.mem_localSubtree_of_adj h⟩ := by
  have hvw : v ≠ w := hF.ne_of_adj h
  rw [Digraph.reachSetDist_eq_one_add_sum hF hP h, Arrangement.boundaryDist,
    ite_eq_right (by simpa)]
  congr 1
  simp only [Digraph.localArrangement_precedes, ← Set.ncard_eq_toFinset_card', sum_filter]
  refine Eq.trans ?_ (sum_coe_sort (G.localSubtree v)
    fun c ↦ if v < c ∧ c < w ∨ w < c ∧ c < v then (G.reachSet c).ncard else 0).symm
  rw [Digraph.localSubtree, sum_insert (by simpa using hF.not_adj_self), ite_eq_right (by simp),
    zero_add]

theorem Digraph.sum_reachSetDist_eq_sum_boundaryDist (hF : G.IsBranching) (hP : G.IsProjective) :
    ∑ w ∈ G.outNeighborFinset v, G.reachSetDist v w =
      ∑ c, (G.localArrangement v).boundaryDist (fun c ↦ #(G.reachSet c).toFinset)
        ⟨v, G.self_mem_localSubtree v⟩ c := by
  rw [← sum_erase univ (Arrangement.boundaryDist_self ..)]
  refine sum_bij' (fun w hw ↦ ⟨w, Digraph.mem_localSubtree_of_adj (by simpa using hw)⟩)
    (fun c _ ↦ c.1) (fun w hw ↦ ?_) (fun c hc ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun w hw ↦ Digraph.reachSetDist_eq_boundaryDist hF hP (by simpa using hw)
  · simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq]
    rintro rfl
    exact hF.not_adj_self (by simpa using hw)
  · obtain ⟨c, hc'⟩ := c
    simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq] at hc
    simpa [Digraph.localSubtree, hc] using hc'

end LocalSubtree

