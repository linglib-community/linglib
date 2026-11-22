/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Core.Order.Monotone.Monovary
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Tactic.Ring

/-!
# Reordering the dependents of a head

For a digraph `G` on positions, a position `v` and a permutation `σ` of the local subtree of `v`,
we define `G.reorderDependents v σ`, the digraph in which the yields of the dependents of `v` are
moved, each as a block, into the order that `σ` gives them. Every position outside the yield of
`v` keeps its place.

On a projective forest, the blocks stand in the order of the dependents
(`Digraph.monotoneOn_blockHead`). We prove three facts about the total dependency length of a
reordering of a projective forest.

* A reordering that keeps each dependent on its side of the head changes the length by the change
  in the boundary distances of the head (`Digraph.totalLength_reorderDependents_add`). This is the
  first step of the proof in [gildea-temperley-2007] that their linearization has least
  dependency length.
* Exchanging two neighbouring dependents after the head changes the length by the difference of
  the sizes of their yields (`Digraph.totalLength_reorderDependents_swap_add`).
* When the yields after a head grow outward, a reordering of them is strictly longer exactly when
  they do not grow outward in it (`Digraph.totalLength_lt_reorderDependents_iff`).

## Implementation notes

A position's new place is its rank under a key: the new rank of its block, then its old position.
The reordering therefore reduces in the kernel. Mathlib's `Tuple.sort` would not, because it sorts
with `List.mergeSort`.

## References

* [gildea-temperley-2007]
* [futrell-levy-gibson-2020]
-/

@[expose] public section


open Finset WordOrder Relation

variable {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)

/-! ### Blocks -/

/-- `G.blockHead v x` is the member of the local subtree of `v` whose block holds `x`: the first
dependent of `v` whose phrase contains `x`, and `v` itself when there is none. -/
def Digraph.blockHead (x : Fin n) : G.localSubtree v :=
  match h : (List.finRange n).find? (fun c ↦ decide (G.Adj v c ∧ x ∈ G.reachSet c)) with
  | some c => ⟨c, Digraph.mem_localSubtree_of_adj
      (of_decide_eq_true
        (List.find?_some (p := fun c ↦ decide (G.Adj v c ∧ x ∈ G.reachSet c)) h)).1⟩
  | none => ⟨v, G.self_mem_localSubtree v⟩

variable (σ : Equiv.Perm (G.localSubtree v))

/-- The reordered positions are ranked by this key. A position outside the yield of `v` keeps its
place, and a position inside sorts by the new rank of its block, then by its old position. -/
def Digraph.reorderKey (x : Fin n) : Fin n ×ₗ (ℕ ×ₗ Fin n) :=
  toLex (if x ∈ G.reachSet v then v else x,
    toLex ((G.localRank v (σ (G.blockHead v x)) : ℕ), x))

/-- The new position of `x` counts the positions whose key is smaller. -/
def Digraph.reorderRank (x : Fin n) : Fin n :=
  ⟨#(univ.filter fun y ↦ G.reorderKey v σ y < G.reorderKey v σ x),
    by simpa using card_lt_card ((filter_ssubset (s := univ)
      (p := fun y ↦ G.reorderKey v σ y < G.reorderKey v σ x)).2 ⟨x, mem_univ x, lt_irrefl _⟩)⟩

variable {G v σ}

private theorem Digraph.reorderKey_injective : Function.Injective (G.reorderKey v σ) :=
  fun x y h ↦ by
  simpa [Digraph.reorderKey] using congrArg (fun k ↦ (ofLex (ofLex k).2).2) h

private theorem Digraph.reorderRank_lt_of_lt {x y : Fin n}
    (h : G.reorderKey v σ x < G.reorderKey v σ y) : G.reorderRank v σ x < G.reorderRank v σ y := by
  simp only [Digraph.reorderRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun z _ (hz : G.reorderKey v σ z < _) ↦ hz.trans h)).2
    ⟨x, by simp [h], by simp⟩)

private theorem Digraph.reorderRank_injective : Function.Injective (G.reorderRank v σ) := by
  intro x y h
  rcases lt_trichotomy (G.reorderKey v σ x) (G.reorderKey v σ y) with hk | hk | hk
  · exact absurd h (Digraph.reorderRank_lt_of_lt hk).ne
  · exact Digraph.reorderKey_injective hk
  · exact absurd h (Digraph.reorderRank_lt_of_lt hk).ne'

theorem Digraph.reorderRank_bijective : Function.Bijective (G.reorderRank v σ) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨Digraph.reorderRank_injective, rfl⟩

variable (G v σ)

/-- The permutation of the positions that moves the blocks of the dependents of `v` into the order
`σ` gives them. -/
def Digraph.reorderPerm : Equiv.Perm (Fin n) :=
  ⟨G.reorderRank v σ, Fintype.bijInv Digraph.reorderRank_bijective,
    Fintype.leftInverse_bijInv _, Fintype.rightInverse_bijInv _⟩

/-- The digraph with the dependents of `v` reordered by `σ`, each yield moving as a block. -/
def Digraph.reorderDependents : Digraph (Fin n) := G.comap (G.reorderPerm v σ).symm

instance : DecidableRel (G.reorderDependents v σ).Adj :=
  inferInstanceAs (DecidableRel (G.comap _).Adj)

private theorem Digraph.reorderPerm_apply (x : Fin n) :
    G.reorderPerm v σ x = G.reorderRank v σ x :=
  rfl

/-! ### Block lemmas (forests) -/

section Blocks

variable {G v}

private theorem find?_spec {x c : Fin n}
    (h : (List.finRange n).find? (fun c ↦ decide (G.Adj v c ∧ x ∈ G.reachSet c)) = some c) :
    G.Adj v c ∧ x ∈ G.reachSet c :=
  of_decide_eq_true (List.find?_some (p := fun c ↦ decide (G.Adj v c ∧ x ∈ G.reachSet c)) h)

theorem Digraph.blockHead_of_notMem_reachSet {x : Fin n} (hx : x ∉ G.reachSet v) :
    (G.blockHead v x : Fin n) = v := by
  unfold Digraph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd (ReflTransGen.head hc.1 hc.2) hx
  · rfl

theorem Digraph.blockHead_self (hF : G.IsBranching) : (G.blockHead v v : Fin n) = v := by
  unfold Digraph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd hc.2 (hF.not_reachable_of_adj hc.1)
  · rfl

theorem Digraph.blockHead_eq_of_mem_reachSet (hF : G.IsBranching) {x c : Fin n} (hc : G.Adj v c)
    (hx : x ∈ G.reachSet c) : (G.blockHead v x : Fin n) = c := by
  unfold Digraph.blockHead
  split
  · rename_i c' h
    have hc' := find?_spec h
    by_contra hne
    exact Set.disjoint_left.1 (hF.disjoint_reachSet_of_adj hc'.1 hc hne) hc'.2 hx
  · rename_i h
    have := List.find?_eq_none.1 h c (List.mem_finRange c)
    simp [hc, hx] at this

theorem Digraph.adj_blockHead_of_ne (hF : G.IsBranching) {x : Fin n} (hx : x ∈ G.reachSet v)
    (hne : x ≠ v) : G.Adj v (G.blockHead v x) ∧ x ∈ G.reachSet (G.blockHead v x) := by
  obtain ⟨c, hc, hxc⟩ := G.exists_adj_mem_reachSet hx hne
  rw [Digraph.blockHead_eq_of_mem_reachSet hF hc hxc]
  exact ⟨hc, hxc⟩

theorem Digraph.blockHead_eq_self_iff (hF : G.IsBranching) {x : Fin n} (hx : x ∈ G.reachSet v) :
    (G.blockHead v x : Fin n) = v ↔ x = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Digraph.blockHead_self hF⟩
  by_contra hne
  exact hF.ne_of_adj (Digraph.adj_blockHead_of_ne hF hx hne).1 h.symm

end Blocks

/-! ### Projectivity: blocks are intervals in the order of their heads -/

section Projective

variable {G v} (hF : G.IsBranching) (hP : G.IsProjective)
include hF hP

omit [DecidableRel G.Adj] in
theorem Digraph.lt_of_mem_reachSet_of_lt {d x : Fin n} (hd : G.Adj v d) (hvd : v < d)
    (hx : x ∈ G.reachSet d) : v < x := by
  by_contra h
  exact hF.not_reachable_of_adj hd ((hP d).uIcc_subset hx ReflTransGen.refl
    (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h, hvd.le⟩)))

omit [DecidableRel G.Adj] in
theorem Digraph.lt_of_mem_reachSet_of_gt {d x : Fin n} (hd : G.Adj v d) (hdv : d < v)
    (hx : x ∈ G.reachSet d) : x < v := by
  by_contra h
  exact hF.not_reachable_of_adj hd ((hP d).uIcc_subset ReflTransGen.refl hx
    (Set.mem_uIcc.2 (Or.inl ⟨hdv.le, not_lt.1 h⟩)))

omit [DecidableRel G.Adj] in
theorem Digraph.lt_of_mem_reachSet_of_mem_reachSet {c d y x : Fin n} (hc : G.Adj v c)
    (hd : G.Adj v d)
    (hcd : c < d) (hy : y ∈ G.reachSet c) (hx : x ∈ G.reachSet d) : y < x := by
  have hdis := hF.disjoint_reachSet_of_adj hc hd hcd.ne
  by_contra h
  rcases le_or_gt x c with hxc | hcx
  · exact Set.disjoint_left.1 hdis ReflTransGen.refl
      ((hP d).uIcc_subset hx ReflTransGen.refl (Set.mem_uIcc.2 (Or.inl ⟨hxc, hcd.le⟩)))
  · exact Set.disjoint_left.1 hdis
      ((hP c).uIcc_subset ReflTransGen.refl hy (Set.mem_uIcc.2 (Or.inl ⟨hcx.le, not_lt.1 h⟩))) hx

theorem Digraph.lt_of_blockHead_lt {x y : Fin n} (hx : x ∈ G.reachSet v) (hy : y ∈ G.reachSet v)
    (hlt : G.blockHead v y < G.blockHead v x) : y < x := by
  have hlt : (G.blockHead v y : Fin n) < G.blockHead v x := hlt
  by_cases hyv : y = v
  · have hxv : x ≠ v := by
      rintro rfl
      rw [hyv, Digraph.blockHead_self hF] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨hd, hxd⟩ := Digraph.adj_blockHead_of_ne hF hx hxv
    rw [hyv, Digraph.blockHead_self hF] at hlt
    rw [hyv]
    exact Digraph.lt_of_mem_reachSet_of_lt hF hP hd hlt hxd
  by_cases hxv : x = v
  · obtain ⟨hc, hyc⟩ := Digraph.adj_blockHead_of_ne hF hy hyv
    rw [hxv, Digraph.blockHead_self hF] at hlt
    rw [hxv]
    exact Digraph.lt_of_mem_reachSet_of_gt hF hP hc hlt hyc
  obtain ⟨hc, hyc⟩ := Digraph.adj_blockHead_of_ne hF hy hyv
  obtain ⟨hd, hxd⟩ := Digraph.adj_blockHead_of_ne hF hx hxv
  exact Digraph.lt_of_mem_reachSet_of_mem_reachSet hF hP hc hd hlt hyc hxd

theorem Digraph.monotoneOn_blockHead : MonotoneOn (G.blockHead v) (G.reachSet v) :=
  fun _ hy _ hx hyx ↦ not_lt.1 fun hlt ↦ hyx.not_gt (Digraph.lt_of_blockHead_lt hF hP hy hx hlt)

theorem Digraph.lt_iff_blockHead_lt {x y : Fin n} (hx : x ∈ G.reachSet v) (hy : y ∈ G.reachSet v)
    (hne : G.blockHead v y ≠ G.blockHead v x) :
    y < x ↔ G.blockHead v y < G.blockHead v x :=
  ⟨fun h ↦ (Digraph.monotoneOn_blockHead hF hP hy hx h.le).lt_of_ne hne,
    Digraph.lt_of_blockHead_lt hF hP hx hy⟩

end Projective

/-! ### The rank, decomposed -/

section Rank

variable {G v}

private theorem Digraph.reorderKey_lt_iff_of_mem {x y : Fin n} (hx : x ∈ G.reachSet v) :
    G.reorderKey v σ y < G.reorderKey v σ x ↔
      (y ∉ G.reachSet v ∧ y < v) ∨
        (y ∈ G.reachSet v ∧
          G.localRank v (σ (G.blockHead v y)) < G.localRank v (σ (G.blockHead v x))) ∨
        (y ∈ G.reachSet v ∧ G.blockHead v y = G.blockHead v x ∧ y < x) := by
  have hinj : Function.Injective fun c ↦ G.localRank v (σ c) :=
    (G.localRank_strictMono v).injective.comp σ.injective
  simp only [Digraph.reorderKey, Prod.Lex.toLex_lt_toLex, ite_eq_left hx, Fin.val_fin_lt]
  by_cases hy : y ∈ G.reachSet v
  · simp only [hy, ite_true, lt_self_iff_false, true_and, false_or, not_true_eq_false, false_and,
      Fin.val_eq_val]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hinj h, h'⟩
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by rw [h], h'⟩
  · have hyv : y ≠ v := fun h ↦ hy (h ▸ ReflTransGen.refl)
    simp [hy, hyv]

private theorem Digraph.reorderKey_lt_iff_of_notMem {x y : Fin n} (hx : x ∉ G.reachSet v) :
    G.reorderKey v σ y < G.reorderKey v σ x ↔
      (y ∉ G.reachSet v ∧ y < x) ∨ (y ∈ G.reachSet v ∧ v < x) := by
  have hxv : x ≠ v := fun h ↦ hx (h ▸ ReflTransGen.refl)
  simp only [Digraph.reorderKey, Prod.Lex.toLex_lt_toLex, ite_eq_right hx]
  by_cases hy : y ∈ G.reachSet v
  · simp [hy, hxv.symm]
  · by_cases hyx : y = x
    · subst hyx
      have hy' : ¬ G.Reachable v y := hy
      simp [hy']
    · simp [hy, hyx]

/-! #### The rank of a position in the yield, decomposed -/

/-- Positions outside the yield of `v` and before it. -/
private def baseCount (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℕ :=
    #{y | y ∉ G.reachSet v ∧ y < v}

/-- The words of the blocks placed before `c` by `σ`. -/
private def blocksBefore (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (σ : Equiv.Perm (G.localSubtree v)) (c : G.localSubtree v) :
    ℕ :=
  #{y | y ∈ G.reachSet v ∧ G.localRank v (σ (G.blockHead v y)) < G.localRank v (σ c)}

/-- The words of the block of `x` before `x`. -/
private def blockOffset (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n) : ℕ :=
  #{y | y ∈ G.reachSet v ∧ G.blockHead v y = G.blockHead v x ∧ y < x}

/-- The words of the block of `c`. -/
private def blockSize (G : Digraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (c : G.localSubtree v) : ℕ :=
  #{y | y ∈ G.reachSet v ∧ G.blockHead v y = c}

private theorem Digraph.reorderRank_of_mem {x : Fin n} (hx : x ∈ G.reachSet v) :
    (G.reorderRank v σ x : ℕ) =
      baseCount G v + blocksBefore G v σ (G.blockHead v x) + blockOffset G v x := by
  simp only [Digraph.reorderRank, baseCount, blocksBefore, blockOffset]
  rw [filter_congr fun y _ ↦ Digraph.reorderKey_lt_iff_of_mem σ hx, filter_or, filter_or,
    card_union_of_disjoint, card_union_of_disjoint, add_assoc]
  · exact disjoint_filter.2 fun y _ h₁ h₂ ↦ by rw [h₂.2.1] at h₁; exact lt_irrefl _ h₁.2
  · refine disjoint_union_right.2 ⟨disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1,
      disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1⟩

private theorem Digraph.reorderRank_of_notMem {x : Fin n} (hx : x ∉ G.reachSet v) :
    (G.reorderRank v σ x : ℕ) =
      #{y | y ∉ G.reachSet v ∧ y < x} + #{y | y ∈ G.reachSet v ∧ v < x} := by
  simp only [Digraph.reorderRank]
  rw [filter_congr fun y _ ↦ Digraph.reorderKey_lt_iff_of_notMem σ hx, filter_or,
    card_union_of_disjoint]
  exact disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1

private theorem Digraph.reorderRank_of_notMem_eq {x : Fin n} (hx : x ∉ G.reachSet v)
    (τ : Equiv.Perm (G.localSubtree v)) : G.reorderRank v σ x = G.reorderRank v τ x :=
  Fin.ext (by rw [Digraph.reorderRank_of_notMem σ hx, Digraph.reorderRank_of_notMem τ hx])

end Rank

/-! ### The identity permutation keeps every position -/

section One

variable {G v} (hF : G.IsBranching) (hP : G.IsProjective)
include hP

omit [DecidableRel G.Adj] in
theorem Digraph.lt_iff_lt_of_notMem_reachSet {x y : Fin n} (hx : x ∈ G.reachSet v)
    (hy : y ∉ G.reachSet v) :
    y < x ↔ y < v := by
  constructor <;> intro h <;> by_contra h'
  · exact hy ((hP v).uIcc_subset ReflTransGen.refl hx (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))
  · exact hy ((hP v).uIcc_subset hx ReflTransGen.refl (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))

include hF

private theorem Digraph.reorderRank_one (x : Fin n) : G.reorderRank v 1 x = x := by
  ext
  rw [← Fin.card_Iio x]
  simp only [Digraph.reorderRank]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_Iio]
  by_cases hx : x ∈ G.reachSet v
  · rw [Digraph.reorderKey_lt_iff_of_mem 1 hx]
    simp only [Equiv.Perm.coe_one, id, (G.localRank_strictMono v).lt_iff_lt]
    by_cases hy : y ∈ G.reachSet v
    · simp only [hy, not_true_eq_false, false_and, true_and, false_or]
      by_cases hne : G.blockHead v y = G.blockHead v x
      · simp [hne]
      · simp [hne, Digraph.lt_iff_blockHead_lt hF hP hx hy hne]
    · simp [hy, Digraph.lt_iff_lt_of_notMem_reachSet hP hx hy]
  · rw [Digraph.reorderKey_lt_iff_of_notMem 1 hx]
    by_cases hy : y ∈ G.reachSet v
    · have hxv : x ≠ v := fun h ↦ hx (h ▸ ReflTransGen.refl)
      have hxy : x ≠ y := fun h ↦ hx (h ▸ hy)
      have := Digraph.lt_iff_lt_of_notMem_reachSet hP hy hx
      simp only [hy, not_true_eq_false, false_and, false_or, true_and]
      constructor <;> intro h <;> by_contra h'
      · exact absurd (this.1 (lt_of_le_of_ne (not_lt.1 h') hxy)) (lt_asymm h)
      · exact absurd (this.2 (lt_of_le_of_ne (not_lt.1 h') hxv)) (lt_asymm h)
    · simp [hy]

private theorem Digraph.reorderRank_of_notMem_reachSet {x : Fin n} (hx : x ∉ G.reachSet v) :
    G.reorderRank v σ x = x := by
  rw [Digraph.reorderRank_of_notMem_eq σ hx 1, Digraph.reorderRank_one hF hP]

variable {σ} in
theorem Digraph.reorderPerm_apply_of_notMem_reachSet {x : Fin n} (hx : x ∉ G.reachSet v) :
    G.reorderPerm v σ x = x :=
  Digraph.reorderRank_of_notMem_reachSet σ hF hP hx

theorem Digraph.reorderPerm_one : G.reorderPerm v 1 = 1 :=
  Equiv.ext (Digraph.reorderRank_one hF hP)

theorem Digraph.reorderDependents_one : G.reorderDependents v 1 = G := by
  unfold Digraph.reorderDependents
  rw [Digraph.reorderPerm_one hF hP]
  rfl

end One

/-! ### Transport of total dependency length -/

section Transport

open WordOrder.Arrangement

variable {G v} (hF : G.IsBranching) (hP : G.IsProjective)

/-- The head as a member of its local subtree. -/
local notation "v'" => Subtype.mk v (Digraph.self_mem_localSubtree G v)

/-- The new rank of a member of the local subtree. -/
local notation "nr" c => G.localRank v (σ c)

include hF

private theorem blockSize_self : blockSize G v v' = 1 := by
  rw [blockSize, card_eq_one]
  refine ⟨v, ?_⟩
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hy, h⟩
    exact (Digraph.blockHead_eq_self_iff hF hy).1 (congrArg Subtype.val h)
  · rintro rfl
    exact ⟨ReflTransGen.refl, Subtype.ext (Digraph.blockHead_self hF)⟩

private theorem blockOffset_self : blockOffset G v v = 0 := by
  rw [blockOffset, card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨hy, h, hlt⟩
  have h' := congrArg Subtype.val h
  rw [Digraph.blockHead_self hF, Digraph.blockHead_eq_self_iff hF hy] at h'
  exact lt_irrefl _ (h' ▸ hlt)

private theorem blockSize_eq_card_reachSet {c : G.localSubtree v} (hc : (c : Fin n) ≠ v) :
    blockSize G v c = #(G.reachSet c).toFinset := by
  have hadj : G.Adj v c := (Digraph.mem_localSubtree_iff.1 c.2).resolve_left hc
  rw [blockSize]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset]
  constructor
  · rintro ⟨hy, h⟩
    have hyv : y ≠ v := fun e ↦ hc (by rw [← h, e, Digraph.blockHead_self hF])
    exact h ▸ (Digraph.adj_blockHead_of_ne hF hy hyv).2
  · intro h
    exact ⟨ReflTransGen.head hadj h, Subtype.ext (Digraph.blockHead_eq_of_mem_reachSet hF hadj h)⟩

private theorem blockOffset_lt_blockSize {c : G.localSubtree v} (hc : (c : Fin n) ≠ v) :
    blockOffset G v c < blockSize G v c := by
  have hadj : G.Adj v c := (Digraph.mem_localSubtree_iff.1 c.2).resolve_left hc
  have hcc : (G.blockHead v c) = c := Subtype.ext
    (Digraph.blockHead_eq_of_mem_reachSet hF hadj .refl)
  rw [blockOffset, blockSize, hcc]
  refine card_lt_card ((ssubset_iff_of_subset (monotone_filter_right _ fun y _ h ↦ ⟨h.1, h.2.1⟩)).2
    ⟨c, ?_, ?_⟩)
  · simp [hcc, ReflTransGen.single hadj]
  · simp

omit hF in
private theorem blocksBefore_eq_sum (c : G.localSubtree v) :
    blocksBefore G v σ c =
      ∑ d with Precedes (σ.trans (G.localArrangement v)) d c, blockSize G v d := by
  rw [blocksBefore, card_eq_sum_card_fiberwise (f := G.blockHead v)
    (t := {d | Precedes (σ.trans (G.localArrangement v)) d c})
    fun y hy ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hy).2.2⟩]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [blockSize, filter_filter]
  exact congrArg card (filter_congr fun y _ ↦
    ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ (mem_filter.1 hd).2⟩, h.2⟩⟩)

omit hF in
private theorem nr_injective : Function.Injective fun c ↦ (nr c) :=
  (G.localRank_strictMono v).injective.comp σ.injective

/-- Between the head and `c`, the boundary distance counts the words of the blocks. -/
private theorem boundaryDist_eq_blockSize (c : G.localSubtree v) :
    boundaryDist (σ.trans (G.localArrangement v)) (fun c ↦ #(G.reachSet c).toFinset) v' c =
      boundaryDist (σ.trans (G.localArrangement v)) (blockSize G v) v' c :=
  boundaryDist_congr _ fun _ hd _ ↦ (blockSize_eq_card_reachSet hF fun e ↦ hd (Subtype.ext e)).symm

private theorem blocksBefore_eq_of_lt {c : G.localSubtree v} (hvc : (nr v') < (nr c)) :
    blocksBefore G v σ c = blocksBefore G v σ v' +
      boundaryDist (σ.trans (G.localArrangement v)) (fun c ↦ #(G.reachSet c).toFinset) v' c := by
  have h : Precedes (σ.trans (G.localArrangement v)) v' c := hvc
  rw [boundaryDist_eq_blockSize σ hF, blocksBefore_eq_sum, blocksBefore_eq_sum,
    sum_precedes_of_precedes _ h, boundaryDist_of_precedes _ h, blockSize_self hF, add_assoc]

private theorem blocksBefore_eq_of_gt {c : G.localSubtree v} (hcv : (nr c) < (nr v')) :
    blocksBefore G v σ v' + 1 = blocksBefore G v σ c + blockSize G v c +
      boundaryDist (σ.trans (G.localArrangement v)) (fun c ↦ #(G.reachSet c).toFinset) v' c := by
  have h : Precedes (σ.trans (G.localArrangement v)) c v' := hcv
  rw [boundaryDist_eq_blockSize σ hF, boundaryDist_comm, blocksBefore_eq_sum, blocksBefore_eq_sum,
    sum_precedes_of_precedes _ h, boundaryDist_of_precedes _ h]
  ring

/-! #### Per-arc identities -/

section SameSide

variable (hσ : after (σ.trans (G.localArrangement v)) ⟨v, G.self_mem_localSubtree v⟩ =
  (G.localArrangement v).after ⟨v, G.self_mem_localSubtree v⟩)
include hσ

omit hF in
/-- `σ` keeps every dependent on its side of the head. -/
private theorem nr_lt_iff (c : G.localSubtree v) :
    (nr v') < (nr c) ↔ G.localRank v v' < G.localRank v c := by
  have := Finset.ext_iff.1 hσ c
  simp only [mem_after, Precedes, Equiv.trans_apply] at this
  exact this

omit hF in
private theorem blocksBefore_self_eq : blocksBefore G v σ v' = blocksBefore G v 1 v' := by
  simp only [blocksBefore, Equiv.Perm.coe_one, id]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, and_congr_right_iff]
  intro _
  have h := nr_lt_iff σ hσ (G.blockHead v y)
  have h1 : (nr (G.blockHead v y)) = (nr v') ↔
      G.localRank v (G.blockHead v y) = G.localRank v v' := by
    rw [(nr_injective σ).eq_iff, (G.localRank_strictMono v).injective.eq_iff]
  simp only [Fin.lt_def, Fin.ext_iff] at h h1 ⊢
  omega

include hP

private theorem Digraph.reorderRank_head : G.reorderRank v σ v = v := by
  have h1 := Digraph.reorderRank_of_mem σ (ReflTransGen.refl (r := G.Adj) (a := v))
  have h2 := Digraph.reorderRank_of_mem 1 (ReflTransGen.refl (r := G.Adj) (a := v))
  have hb : G.blockHead v v = v' := Subtype.ext (Digraph.blockHead_self hF)
  rw [Digraph.reorderRank_one hF hP] at h2
  rw [hb] at h1 h2
  rw [blocksBefore_self_eq (σ := σ) hσ] at h1
  exact Fin.ext (h1.trans h2.symm)

private theorem Digraph.dist_reorderRank_of_ne {u w : Fin n} (hu : u ≠ v)
    (huw : G.Adj u w) :
    Nat.dist (G.reorderRank v σ u) (G.reorderRank v σ w) = Nat.dist u w := by
  by_cases huY : u ∈ G.reachSet v
  · have hwY : w ∈ G.reachSet v := ReflTransGen.tail huY huw
    obtain ⟨hc, huc⟩ := Digraph.adj_blockHead_of_ne hF huY hu
    have hbw : G.blockHead v w = G.blockHead v u :=
      Subtype.ext (Digraph.blockHead_eq_of_mem_reachSet hF hc (ReflTransGen.tail huc huw))
    have h1 := Digraph.reorderRank_of_mem σ huY
    have h2 := Digraph.reorderRank_of_mem 1 huY
    have h3 := Digraph.reorderRank_of_mem σ hwY
    have h4 := Digraph.reorderRank_of_mem 1 hwY
    rw [Digraph.reorderRank_one hF hP] at h2 h4
    rw [hbw] at h3 h4
    simp only [Nat.dist]
    omega
  · rw [Digraph.reorderRank_of_notMem_reachSet (σ := σ) hF hP huY]
    by_cases hwY : w ∈ G.reachSet v
    · have hwv : w = v := by
        rcases ReflTransGen.cases_tail hwY with h | ⟨u', hu', hu'w⟩
        · exact h
        · exact absurd (hF.leftUnique_adj huw hu'w ▸ hu') huY
      subst hwv
      rw [Digraph.reorderRank_head (σ := σ) hF hP hσ]
    · rw [Digraph.reorderRank_of_notMem_reachSet (σ := σ) hF hP hwY]

private theorem Digraph.dist_reorderRank_add_boundaryDist (c : G.localSubtree v) :
    Nat.dist (G.reorderRank v σ v) (G.reorderRank v σ c) +
        (G.localArrangement v).boundaryDist (fun c ↦ #(G.reachSet c).toFinset) v' c =
      Nat.dist v c +
        boundaryDist (σ.trans (G.localArrangement v)) (fun c ↦ #(G.reachSet c).toFinset) v'
          c := by
  by_cases hcv : c = v'
  · subst hcv; simp
  have hcv' : (c : Fin n) ≠ v := fun h ↦ hcv (Subtype.ext h)
  have hadj : G.Adj v c := (Digraph.mem_localSubtree_iff.1 c.2).resolve_left hcv'
  have hcY : (c : Fin n) ∈ G.reachSet v := ReflTransGen.single hadj
  have hbc : G.blockHead v c = c := Subtype.ext (Digraph.blockHead_eq_of_mem_reachSet hF hadj .refl)
  rw [Digraph.reorderRank_head (σ := σ) hF hP hσ]
  have h1 := Digraph.reorderRank_of_mem σ hcY
  have h2 := Digraph.reorderRank_of_mem 1 hcY
  rw [Digraph.reorderRank_one hF hP] at h2
  rw [hbc] at h1 h2
  have hv1 := Digraph.reorderRank_of_mem 1 (ReflTransGen.refl (r := G.Adj) (a := v))
  have hb : G.blockHead v v = v' := Subtype.ext (Digraph.blockHead_self hF)
  rw [Digraph.reorderRank_one hF hP, hb, blockOffset_self hF] at hv1
  have hb := blocksBefore_self_eq (σ := σ) hσ
  have hoff := blockOffset_lt_blockSize hF hcv'
  have hone : boundaryDist ((1 : Equiv.Perm (G.localSubtree v)).trans (G.localArrangement v))
      (fun c ↦ #(G.reachSet c).toFinset) v' c = (G.localArrangement v).boundaryDist
      (fun c ↦ #(G.reachSet c).toFinset) v' c := rfl
  have hne : (nr c) ≠ (nr v') := fun h ↦ hcv (nr_injective σ h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have e1 := blocksBefore_eq_of_gt (σ := σ) hF hlt
    have hlt1 : G.localRank v c < G.localRank v v' := by
      have := nr_lt_iff σ hσ c
      rcases lt_trichotomy (G.localRank v v') (G.localRank v c) with h | h | h
      · exact absurd (this.2 h) (lt_asymm hlt)
      · exact absurd ((G.localRank_strictMono v).injective h) (Ne.symm hcv)
      · exact h
    have e2 := blocksBefore_eq_of_gt (σ := 1) hF hlt1
    rw [hone] at e2
    simp only [Nat.dist]
    omega
  · have e1 := blocksBefore_eq_of_lt (σ := σ) hF hgt
    have e2 := blocksBefore_eq_of_lt (σ := 1) hF ((nr_lt_iff σ hσ c).1 hgt)
    rw [hone] at e2
    simp only [Nat.dist]
    omega

/-! #### The transport theorem -/

variable {σ}

/-- A reordering that keeps each dependent of `v` on its side of the head changes the total
dependency length by the change in the boundary distances of the head in the local arrangement. -/
theorem Digraph.totalLength_reorderDependents_add :
    (G.reorderDependents v σ).totalLength +
        ∑ c, (G.localArrangement v).boundaryDist (fun c ↦ #(G.reachSet c).toFinset) v' c =
      G.totalLength +
        ∑ c, boundaryDist (σ.trans (G.localArrangement v))
          (fun c ↦ #(G.reachSet c).toFinset) v' c := by
  have hrest : ∑ u ∈ univ.erase v, ∑ w ∈ G.outNeighborFinset u,
      Nat.dist (G.reorderRank v σ u) (G.reorderRank v σ w) =
      ∑ u ∈ univ.erase v, ∑ w ∈ G.outNeighborFinset u, Nat.dist u w :=
    sum_congr rfl fun u hu ↦ sum_congr rfl fun w hw ↦
      Digraph.dist_reorderRank_of_ne σ hF hP hσ (ne_of_mem_erase hu)
        (Digraph.mem_outNeighborFinset.1 hw)
  have hhead : ∀ τ : Equiv.Perm (G.localSubtree v), ∑ w ∈ G.outNeighborFinset v,
      Nat.dist (G.reorderRank v τ v) (G.reorderRank v τ w) =
      ∑ c : G.localSubtree v, Nat.dist (G.reorderRank v τ v) (G.reorderRank v τ c) := fun τ ↦ by
    rw [sum_coe_sort (G.localSubtree v)
        fun w ↦ Nat.dist (G.reorderRank v τ v) (G.reorderRank v τ w), Digraph.localSubtree,
      sum_insert (by simpa using hF.not_adj_self), Nat.dist_self, zero_add]
  have hg : G.totalLength = ∑ u, ∑ w ∈ G.outNeighborFinset u,
      Nat.dist (G.reorderRank v 1 u) (G.reorderRank v 1 w) := by
    simp only [Digraph.reorderRank_one hF hP]; rfl
  rw [show (G.reorderDependents v σ).totalLength = (G.comap (G.reorderPerm v σ).symm).totalLength
    from rfl, Digraph.totalLength_comap_symm_eq_sum, hg]
  simp only [Digraph.reorderPerm_apply]
  rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v), hhead, hhead,
    Digraph.reorderRank_one hF hP]
  simp only [Digraph.reorderRank_one hF hP] at hrest ⊢
  rw [hrest]
  have := Fintype.sum_congr _ _ fun c ↦ Digraph.dist_reorderRank_add_boundaryDist σ hF hP hσ c
  simp only [sum_add_distrib] at this
  omega

end SameSide

variable {σ}

include hP

/-! #### Exchanging neighbouring dependents -/

/-- Exchanging two neighbouring dependents after their head changes the total dependency length by
the difference of the sizes of their yields. -/
theorem Digraph.totalLength_reorderDependents_swap_add {c d : G.localSubtree v} (hc : v < c)
    (hcd : (G.localRank v c : ℕ) + 1 = G.localRank v d) :
    (G.reorderDependents v (Equiv.swap c d)).totalLength + #(G.reachSet c).toFinset =
      G.totalLength + #(G.reachSet d).toFinset := by
  have hc' : c ∈ (G.localArrangement v).after v' :=
    mem_after.2 (Digraph.localArrangement_precedes.2 hc)
  have hcd' : (G.localArrangement v).Precedes c d :=
    Fin.lt_def.2 (show (G.localRank v c : ℕ) < G.localRank v d by omega)
  have h₁ := Digraph.totalLength_reorderDependents_add hF hP
    (after_trans (swap_apply_ne_subset_after hc' hcd'))
  have h₂ := sum_boundaryDist_swap_add (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset) hc' hcd
  omega

/-! #### Growing constituents after the head -/

theorem Digraph.totalLength_le_reorderDependents
    (hσ : σ.support ⊆ (G.localArrangement v).after v')
    (h : MonovaryOn (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset) (G.localArrangement v)
      ↑((G.localArrangement v).after v')) :
    G.totalLength ≤ (G.reorderDependents v σ).totalLength := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((G.localArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Digraph.totalLength_reorderDependents_add hF hP (after_trans hσ')
  have := sum_boundaryDist_le (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset) hσ' h
  omega

/-- When the yields after `v` grow outward, a reordering of them is strictly longer exactly when
they do not grow outward in it. -/
theorem Digraph.totalLength_lt_reorderDependents_iff
    (hσ : σ.support ⊆ (G.localArrangement v).after v')
    (h : MonovaryOn (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset) (G.localArrangement v)
      ↑((G.localArrangement v).after v')) :
    G.totalLength < (G.reorderDependents v σ).totalLength ↔
      ¬ MonovaryOn (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset)
        (σ.trans (G.localArrangement v))
        ↑(after (σ.trans (G.localArrangement v)) v') := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((G.localArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Digraph.totalLength_reorderDependents_add hF hP (after_trans hσ')
  rw [← sum_boundaryDist_lt_iff (fun c : G.localSubtree v ↦ #(G.reachSet c).toFinset) hσ' h]
  omega

end Transport

