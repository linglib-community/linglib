/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.WordOrder.BoundaryDistance
public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.Card
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Order.Ring.Nat

/-!
# Dependency length

The length of a dependency is the distance in words between head and dependent. This file defines
the total dependency length of a graph and the distance from a head to the nearest word of a
dependent's yield, dependency length measured to the boundary of the dependent's phrase. On a
projective forest that distance is one more than the sizes of the yields of the sibling dependents
between head and dependent: it is the block measure `WordOrder.Arrangement.boundaryDist` with yields
as blocks. Summed over the elements after a head, the block measure weighs each element's length by
the number of elements farther out, so by the rearrangement inequality an order whose lengths grow
outward is shortest. This is the short-before-long order that dependency length minimization
predicts after a head, and its mirror image orders long before short before a final head.

## Main definitions

* `Graph.totalLength`: the sum of `Nat.dist` over the arcs.
* `Graph.yieldDist`: the distance from a position to the nearest word of a yield.
* `Graph.siblingOrderIso` and `Graph.siblingArrangement`: a head and its dependents in the order
  of their positions.

## Main results

* `Graph.totalLength_map`: transport along an isometry preserves total dependency length.
* `Graph.card_arcs_le_totalLength` and `Graph.totalLength_eq_card_arcs_iff`: total dependency
  length is at least the number of dependencies, with equality exactly when every dependent stands
  next to its head, so that such a graph is no longer than any reordering of it
  (`Graph.totalLength_le_totalLength_map`).
* `Graph.card_arcs_lt_totalLength`: the bound is not attained when a head has two dependents on
  one side.
* `Graph.yieldDist_eq_one_add_sum`: on a projective forest, the yield distance from a head to a
  dependent is one more than the yield sizes of the dependents between them.
* `Graph.sum_yieldDist_eq_sum_boundaryDist`: on a projective forest a head's yield distances are
  the boundary distances of its sibling arrangement with phrase lengths.

## References

* [behaghel-1909]
* [futrell-levy-gibson-2020]
* [gildea-temperley-2007]
* [fedzechkina-chu-jaeger-2018]
-/

@[expose] public section

namespace DependencyGrammar

open Relation

variable {L : Type*} {n : ℕ}

/-- Total dependency length sums `Nat.dist` over all arcs, the quantity dependency-length
minimisation is about. -/
def Graph.totalLength (g : Graph L n) : Nat :=
  ∑ v : Fin n, ∑ w ∈ g.children v, Nat.dist v w

/-! ### Transport -/

/-- Mirroring a linearization is linearizing along the mirrored arrangement. -/
theorem Graph.mirror_map (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    (g.map σ).mirror = g.map (WordOrder.Arrangement.mirror σ) :=
  rfl

/-- The total length of a transported graph sums the transported distances of the original arcs. -/
theorem Graph.totalLength_map_eq (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    (g.map σ).totalLength = ∑ u, ∑ w ∈ g.children u, Nat.dist (σ u) (σ w) := by
  unfold Graph.totalLength
  simp only [Graph.children, Finset.sum_filter]
  refine Fintype.sum_equiv σ.symm _ _ fun u ↦ Fintype.sum_equiv σ.symm _ _ fun w ↦ ?_
  simp [Graph.map_adj]

/-- Transport along an isometry of the positions preserves total dependency length. -/
theorem Graph.totalLength_map (g : Graph L n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v w : Fin n, Nat.dist (σ v) (σ w) = Nat.dist v w) :
    (g.map σ).totalLength = g.totalLength := by
  rw [Graph.totalLength_map_eq]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun w _ ↦ hσ u w

theorem _root_.Fin.dist_rev_rev (v w : Fin n) :
    Nat.dist v.rev w.rev = Nat.dist v w := by
  have hv := v.isLt
  have hw := w.isLt
  simp only [Nat.dist, Fin.val_rev]
  omega

/-- The mirror image of a graph has the same total dependency length ([futrell-levy-gibson-2020],
examples (7)–(8)). -/
theorem Graph.totalLength_mirror (g : Graph L n) :
    g.mirror.totalLength = g.totalLength :=
  g.totalLength_map _ Fin.dist_rev_rev

@[simp] theorem Graph.totalLength_map_mirror (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    (g.map (WordOrder.Arrangement.mirror σ)).totalLength = (g.map σ).totalLength := by
  rw [← Graph.mirror_map, Graph.totalLength_mirror]

/-! ### The lower bound -/

section LowerBound

open Finset

theorem Graph.card_arcs (g : Graph L n) : #g.arcs = ∑ v, #(g.children v) := by
  simp only [Graph.arcs, Graph.children, card_filter, Fintype.sum_prod_type]

@[simp] theorem Graph.card_arcs_map (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    #(g.map σ).arcs = #g.arcs :=
  card_equiv (σ.symm.prodCongr σ.symm) fun ⟨v, w⟩ ↦ by simp

variable {g : Graph L n}

private theorem Graph.one_le_dist_of_mem_children (h : ∀ v, ¬ g.Adj v v) (v : Fin n) :
    ∀ w ∈ g.children v, 1 ≤ Nat.dist v w := fun w hw ↦
  Nat.dist_pos_of_ne (Fin.val_ne_of_ne fun e ↦ h v (by simpa [← e] using hw))

/-- Each dependency is at least one word long, so the total dependency length of a graph without
loops is at least the number of its dependencies. -/
theorem Graph.card_arcs_le_totalLength (h : ∀ v, ¬ g.Adj v v) : #g.arcs ≤ g.totalLength := by
  rw [g.card_arcs]
  exact sum_le_sum fun v _ ↦ card_eq_sum_ones (g.children v) ▸
    sum_le_sum (Graph.one_le_dist_of_mem_children h v)

/-- Total dependency length equals the number of dependencies exactly when every dependent stands
next to its head. -/
theorem Graph.totalLength_eq_card_arcs_iff (h : ∀ v, ¬ g.Adj v v) :
    g.totalLength = #g.arcs ↔ ∀ ⦃v w⦄, g.Adj v w → Nat.dist v w = 1 := by
  rw [g.card_arcs, eq_comm, Graph.totalLength]
  simp only [card_eq_sum_ones]
  rw [sum_eq_sum_iff_of_le fun v _ ↦ sum_le_sum (Graph.one_le_dist_of_mem_children h v)]
  refine forall_congr' fun v ↦ ?_
  rw [sum_eq_sum_iff_of_le (Graph.one_le_dist_of_mem_children h v)]
  simp [eq_comm]

/-- A graph in which every dependent stands next to its head is no longer than any reordering of
its positions. -/
theorem Graph.totalLength_le_totalLength_map (h : ∀ v, ¬ g.Adj v v)
    (h₁ : ∀ ⦃v w⦄, g.Adj v w → Nat.dist v w = 1) (σ : Equiv.Perm (Fin n)) :
    g.totalLength ≤ (g.map σ).totalLength := by
  rw [(Graph.totalLength_eq_card_arcs_iff h).2 h₁, ← g.card_arcs_map σ]
  exact Graph.card_arcs_le_totalLength fun v hv ↦ h _ hv

/-- Two dependents on one side of their head cannot both stand next to it, so the total dependency
length exceeds the number of dependencies. -/
theorem Graph.card_arcs_lt_totalLength (h : ∀ v, ¬ g.Adj v v) {d : HeadDirection}
    {v w₁ w₂ : Fin n} (h₁ : g.Adj v w₁) (h₂ : g.Adj v w₂) (hne : w₁ ≠ w₂)
    (o₁ : d.Orders v w₁) (o₂ : d.Orders v w₂) : #g.arcs < g.totalLength := by
  refine (Graph.card_arcs_le_totalLength h).lt_of_ne fun e ↦ hne ?_
  have hd := (Graph.totalLength_eq_card_arcs_iff h).1 e.symm
  have e₁ := hd h₁
  have e₂ := hd h₂
  cases d <;>
    simp only [HeadDirection.headInitial_orders, HeadDirection.headFinal_orders, Fin.lt_def,
      Nat.dist] at o₁ o₂ e₁ e₂ <;>
    exact Fin.ext (by omega)

end LowerBound

/-! ### Arc length and the dependent's phrase -/

theorem Graph.ncard_yield_le_dist (g : Graph L n) {v w : Fin n} (hv : v ∉ g.yield w)
    (h : ∀ x ∈ g.yield w, x ∈ Set.uIcc v w) : (g.yield w).ncard ≤ Nat.dist v w := by
  have hsub : g.yield w ⊆ Set.uIcc v w \ {v} := Set.subset_sdiff_singleton h hv
  refine (Set.ncard_le_ncard hsub).trans (le_of_eq ?_)
  rw [Set.ncard_sdiff_singleton_of_mem Set.left_mem_uIcc, Set.ncard_uIcc, Fin.card_uIcc,
    Nat.add_sub_cancel]
  simp only [Nat.dist]
  omega

/-! ### Distance to a phrase -/

theorem Graph.toFinset_yield_nonempty (g : Graph L n) (w : Fin n) : (g.yield w).toFinset.Nonempty :=
  ⟨w, by simp [ReflTransGen.refl]⟩

/-- The distance from `v` to the nearest word of the yield of `w`, dependency length measured to
the closest boundary of the dependent's phrase. -/
def Graph.yieldDist (g : Graph L n) (v w : Fin n) : ℕ :=
  (g.yield w).toFinset.inf' (g.toFinset_yield_nonempty w) fun x ↦ Nat.dist v x

theorem Graph.yieldDist_le_dist (g : Graph L n) (v w : Fin n) : g.yieldDist v w ≤ Nat.dist v w :=
  Finset.inf'_le _ (by simp [ReflTransGen.refl])

variable {g : Graph L n} {v w : Fin n}

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

/-- On a projective forest the distance from a head to the nearest word of a dependent's phrase is
one more than the phrase sizes of the dependents between them. -/
theorem Graph.yieldDist_eq_one_add_sum (hF : g.IsForest) (hP : g.IsProjective) (h : g.Adj v w) :
    g.yieldDist v w = 1 + ∑ u ∈ g.children v with (v < u ∧ u < w ∨ w < u ∧ u < v),
      (g.yield u).ncard := by
  classical
  obtain ⟨m, hmY, hm⟩ := Finset.exists_mem_eq_inf' (g.toFinset_yield_nonempty w)
    fun x ↦ Nat.dist v x
  have hmY : m ∈ g.yield w := by simpa using hmY
  have hvY := hF.not_dominates_of_adj h
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
      have hdis := hF.disjoint_yield_of_adj hvu h huw
      have hb := (hP u).between hxu (ReflTransGen.refl) hx (hF.not_dominates_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
      have hs := hside w ReflTransGen.refl
      refine ⟨u, by simpa using hvu, ?_, hxu⟩
      simp only [Fin.lt_def, Fin.le_def] at hb hs ⊢
      omega
    · rintro ⟨u, hu, hb, hxu⟩
      have hvu : g.Adj v u := by simpa using hu
      have huw : u ≠ w := by rintro rfl; simp at hb
      have hdis := hF.disjoint_yield_of_adj hvu h huw
      have huY : u ∉ g.yield w := Set.disjoint_left.1 hdis ReflTransGen.refl
      have hs := hside w ReflTransGen.refl
      -- u lies strictly between v and m
      have hum : v < u ∧ u < m ∨ m < u ∧ u < v := by
        have hmw : ¬ (m ≤ u ∧ u ≤ w ∨ w ≤ u ∧ u ≤ m) := fun hc ↦
          huY ((hP w).uIcc_subset hmY ReflTransGen.refl (Set.mem_uIcc.2 hc))
        simp only [Fin.lt_def, Fin.le_def] at hb hs hmw ⊢
        omega
      exact (hP u).between ReflTransGen.refl hxu hum (hF.not_dominates_of_adj hvu)
        (Set.disjoint_right.1 hdis hmY)
  have hvm : v ≠ m := fun e ↦ hvY (e ▸ hmY)
  have hfilter : (Finset.univ.filter fun x ↦ v < x ∧ x < m ∨ m < x ∧ x < v) =
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
      Set.disjoint_left.1 (hF.disjoint_yield_of_adj hu.1 hu'.1 hne)
  rw [Graph.yieldDist, hm, ← card_between hvm, hfilter, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext; simp

/-! ### A head's dependents as an arrangement -/

section Siblings

open Finset WordOrder

variable (g : Graph L n) (v : Fin n)

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

/-- The rank is an order isomorphism from a head and its dependents to an initial segment of the
positions. The inverse is classical, but an order isomorphism is applied through
`Graph.siblingRank`, which the kernel reduces. -/
noncomputable def Graph.siblingOrderIso : g.siblings v ≃o Fin #(g.siblings v) where
  toEquiv := Equiv.ofBijective (g.siblingRank v)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(g.siblingRank_strictMono v).injective, by simp⟩)
  map_rel_iff' := (g.siblingRank_strictMono v).le_iff_le

@[simp] theorem Graph.coe_siblingOrderIso : ⇑(g.siblingOrderIso v) = g.siblingRank v := rfl

/-- The rank inverts mathlib's enumeration of a finite set in increasing order. -/
theorem Graph.symm_siblingOrderIso :
    (g.siblingOrderIso v).symm = (g.siblings v).orderIsoOfFin rfl :=
  Subsingleton.elim _ _

/-- A head and its dependents arranged by position. -/
noncomputable def Graph.siblingArrangement : Arrangement (g.siblings v) #(g.siblings v) :=
  (g.siblingOrderIso v).toEquiv

@[simp] theorem Graph.self_mem_siblings : v ∈ g.siblings v := mem_insert_self _ _

variable {g v}

theorem Graph.mem_siblings_iff {w : Fin n} : w ∈ g.siblings v ↔ w = v ∨ g.Adj v w := by
  simp [Graph.siblings]

theorem Graph.mem_siblings_of_adj {w : Fin n} (h : g.Adj v w) : w ∈ g.siblings v :=
  Graph.mem_siblings_iff.2 (.inr h)

@[simp] theorem Graph.siblingArrangement_precedes {c d : g.siblings v} :
    (g.siblingArrangement v).Precedes c d ↔ (c : Fin n) < d :=
  (g.siblingOrderIso v).lt_iff_lt.trans Subtype.coe_lt_coe.symm

theorem Graph.yieldDist_eq_boundaryDist (hF : g.IsForest) (hP : g.IsProjective) {w : Fin n}
    (h : g.Adj v w) :
    g.yieldDist v w = (g.siblingArrangement v).boundaryDist (fun c ↦ #(g.yield c).toFinset)
      ⟨v, g.self_mem_siblings v⟩ ⟨w, Graph.mem_siblings_of_adj h⟩ := by
  have hvw : v ≠ w := hF.ne_of_adj h
  rw [Graph.yieldDist_eq_one_add_sum hF hP h, Arrangement.boundaryDist, ite_eq_right (by simpa)]
  congr 1
  simp only [Graph.siblingArrangement_precedes, ← Set.ncard_eq_toFinset_card', sum_filter]
  refine Eq.trans ?_ (sum_coe_sort (g.siblings v)
    fun c ↦ if v < c ∧ c < w ∨ w < c ∧ c < v then (g.yield c).ncard else 0).symm
  rw [Graph.siblings, sum_insert (by simpa using hF.not_adj_self), ite_eq_right (by simp),
    zero_add]

/-- The sum of a head's yield distances is the head's measure in the sibling arrangement. -/
theorem Graph.sum_yieldDist_eq_sum_boundaryDist (hF : g.IsForest) (hP : g.IsProjective) :
    ∑ w ∈ g.children v, g.yieldDist v w =
      ∑ c, (g.siblingArrangement v).boundaryDist (fun c ↦ #(g.yield c).toFinset)
        ⟨v, g.self_mem_siblings v⟩ c := by
  rw [← sum_erase univ (Arrangement.boundaryDist_self ..)]
  refine sum_bij' (fun w hw ↦ ⟨w, Graph.mem_siblings_of_adj (by simpa using hw)⟩)
    (fun c _ ↦ c.1) (fun w hw ↦ ?_) (fun c hc ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun w hw ↦ Graph.yieldDist_eq_boundaryDist hF hP (by simpa using hw)
  · simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq]
    rintro rfl
    exact hF.not_adj_self (by simpa using hw)
  · obtain ⟨c, hc'⟩ := c
    simp only [mem_erase, mem_univ, and_true, ne_eq, Subtype.mk.injEq] at hc
    simpa [Graph.siblings, hc] using hc'

end Siblings

end DependencyGrammar
