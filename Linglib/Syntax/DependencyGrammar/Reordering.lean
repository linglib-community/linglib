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
# Reordering a head's dependents

`Graph.reorderDependents g v σ` moves the phrases of the dependents of `v` as whole blocks into the
order a permutation `σ` of `v` and its dependents gives them; every other position keeps its
place. The position permutation ranks positions by a key (the block's new rank, then the old
position inside the yield of `v`), so it is defined on every graph and computable. On a projective
tree only the head's own dependencies change length under the move, by the change in their
boundary distances, so Behaghel's law of growing constituents
(`WordOrder.Arrangement.sum_boundaryDist_lt_iff`) becomes a statement about total dependency
length: when the phrases after a head grow outward, every reordering that does not is strictly
longer.

## Main definitions

* `Graph.reorderDependents`: the graph with a head's dependent phrases reordered as blocks.

## Main results

* `Graph.totalLength_reorderDependents_add`: on a projective tree, reordering changes total
  dependency length exactly as it changes the head's boundary distances.
* `Graph.totalLength_lt_reorderDependents_iff`: Behaghel's law for graphs.

## References

* [behaghel-1909]
* [futrell-levy-gibson-2020]
-/

@[expose] public section

namespace DependencyGrammar

open Finset WordOrder Relation

variable {L : Type*} {n : ℕ} (g : Graph L n) (v : Fin n)

/-! ### Blocks -/

/-- `g.blockHead v x` is the sibling of `v` whose block holds `x`, the dependent of `v` whose phrase
contains `x`, and `v` itself for `v` and for positions outside its yield. -/
def Graph.blockHead (x : Fin n) : g.siblings v :=
  match h : (List.finRange n).find? (fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) with
  | some c => ⟨c, mem_insert_of_mem (mem_children.2
      (of_decide_eq_true (List.find?_some (p := fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) h)).1)⟩
  | none => ⟨v, g.self_mem_siblings v⟩

variable (σ : Equiv.Perm (g.siblings v))

/-- The reordered positions are ranked by this key. A position outside the yield of `v` keeps its
place, and a position inside sorts by the new rank of its block, then by its old position. -/
def Graph.reorderKey (x : Fin n) : Fin n ×ₗ (ℕ ×ₗ Fin n) :=
  toLex (if x ∈ g.yield v then v else x,
    toLex ((g.siblingRank v (σ (g.blockHead v x)) : ℕ), x))

/-- The new position of `x` counts the positions whose key is smaller. -/
def Graph.reorderRank (x : Fin n) : Fin n :=
  ⟨#(univ.filter fun y ↦ g.reorderKey v σ y < g.reorderKey v σ x),
    by simpa using card_lt_card ((filter_ssubset (s := univ)
      (p := fun y ↦ g.reorderKey v σ y < g.reorderKey v σ x)).2 ⟨x, mem_univ x, lt_irrefl _⟩)⟩

variable {g v σ}

theorem Graph.reorderKey_injective : Function.Injective (g.reorderKey v σ) := fun x y h ↦ by
  simpa [Graph.reorderKey] using congrArg (fun k ↦ (ofLex (ofLex k).2).2) h

theorem Graph.reorderRank_lt_of_lt {x y : Fin n}
    (h : g.reorderKey v σ x < g.reorderKey v σ y) : g.reorderRank v σ x < g.reorderRank v σ y := by
  simp only [Graph.reorderRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun z _ (hz : g.reorderKey v σ z < _) ↦ hz.trans h)).2
    ⟨x, by simp [h], by simp⟩)

theorem Graph.reorderRank_injective : Function.Injective (g.reorderRank v σ) := fun x y h ↦ by
  rcases lt_trichotomy (g.reorderKey v σ x) (g.reorderKey v σ y) with hk | hk | hk
  · exact absurd h (Graph.reorderRank_lt_of_lt hk).ne
  · exact Graph.reorderKey_injective hk
  · exact absurd h (Graph.reorderRank_lt_of_lt hk).ne'

theorem Graph.reorderRank_bijective : Function.Bijective (g.reorderRank v σ) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨Graph.reorderRank_injective, rfl⟩

variable (g v σ)

/-- The position permutation that moves the blocks of `v`'s dependents into the order `σ`
gives them; its inverse is computable. -/
def Graph.reorderPerm : Equiv.Perm (Fin n) :=
  ⟨g.reorderRank v σ, Fintype.bijInv Graph.reorderRank_bijective,
    Fintype.leftInverse_bijInv _, Fintype.rightInverse_bijInv _⟩

/-- The graph with the dependents of `v` reordered by `σ`, each phrase moving as a block. -/
def Graph.reorderDependents : Graph L n := g.map (g.reorderPerm v σ)

@[simp] theorem Graph.reorderPerm_apply (x : Fin n) : g.reorderPerm v σ x = g.reorderRank v σ x :=
  rfl

/-! ### Block lemmas (trees) -/

section Blocks

variable {g v}

private theorem find?_spec {x c : Fin n}
    (h : (List.finRange n).find? (fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) = some c) :
    g.Adj v c ∧ x ∈ g.yield c :=
  of_decide_eq_true (List.find?_some (p := fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) h)

theorem Graph.blockHead_spec (x : Fin n) : (g.blockHead v x : Fin n) = v ∨
    g.Adj v (g.blockHead v x) ∧ x ∈ g.yield (g.blockHead v x) := by
  unfold Graph.blockHead
  split
  · rename_i c h
    exact Or.inr (find?_spec h)
  · exact Or.inl rfl

theorem Graph.blockHead_of_notMem_yield {x : Fin n} (hx : x ∉ g.yield v) :
    (g.blockHead v x : Fin n) = v := by
  unfold Graph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd (ReflTransGen.head hc.1 hc.2) hx
  · rfl

theorem Graph.blockHead_self (hT : g.IsTree) : (g.blockHead v v : Fin n) = v := by
  unfold Graph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd hc.2 (hT.not_dominates_of_adj hc.1)
  · rfl

theorem Graph.blockHead_eq_of_mem_yield (hT : g.IsTree) {x c : Fin n} (hc : g.Adj v c)
    (hx : x ∈ g.yield c) : (g.blockHead v x : Fin n) = c := by
  unfold Graph.blockHead
  split
  · rename_i c' h
    have hc' := find?_spec h
    by_contra hne
    exact Set.disjoint_left.1 (hT.disjoint_yield_of_adj hc'.1 hc hne) hc'.2 hx
  · rename_i h
    have := List.find?_eq_none.1 h c (List.mem_finRange c)
    simp [hc, hx] at this

theorem Graph.adj_blockHead_of_ne (hT : g.IsTree) {x : Fin n} (hx : x ∈ g.yield v) (hne : x ≠ v) :
    g.Adj v (g.blockHead v x) ∧ x ∈ g.yield (g.blockHead v x) := by
  obtain ⟨c, hc, hxc⟩ := g.exists_adj_mem_yield hx hne
  rw [Graph.blockHead_eq_of_mem_yield hT hc hxc]
  exact ⟨hc, hxc⟩

theorem Graph.blockHead_eq_self_iff (hT : g.IsTree) {x : Fin n} (hx : x ∈ g.yield v) :
    (g.blockHead v x : Fin n) = v ↔ x = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Graph.blockHead_self hT⟩
  by_contra hne
  exact hT.ne_of_adj (Graph.adj_blockHead_of_ne hT hx hne).1 h.symm

theorem Graph.mem_yield_blockHead {x : Fin n} (hx : x ∈ g.yield v) :
    x ∈ g.yield (g.blockHead v x) := by
  rcases Graph.blockHead_spec (g := g) (v := v) x with h | h
  · rw [h]; exact hx
  · exact h.2

end Blocks

/-! ### Projectivity: blocks are intervals in the order of their heads -/

section Projective

variable {g v} (hT : g.IsTree) (hP : g.IsProjective)
include hT hP

theorem Graph.lt_of_adj_of_mem_yield {d x : Fin n} (hd : g.Adj v d) (hvd : v < d)
    (hx : x ∈ g.yield d) : v < x := by
  by_contra h
  exact hT.not_dominates_of_adj hd ((hP d).uIcc_subset hx ReflTransGen.refl
    (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h, hvd.le⟩)))

theorem Graph.lt_of_adj_of_mem_yield' {d x : Fin n} (hd : g.Adj v d) (hdv : d < v)
    (hx : x ∈ g.yield d) : x < v := by
  by_contra h
  exact hT.not_dominates_of_adj hd ((hP d).uIcc_subset ReflTransGen.refl hx
    (Set.mem_uIcc.2 (Or.inl ⟨hdv.le, not_lt.1 h⟩)))

theorem Graph.lt_of_mem_yield_of_mem_yield {c d y x : Fin n} (hc : g.Adj v c) (hd : g.Adj v d)
    (hcd : c < d) (hy : y ∈ g.yield c) (hx : x ∈ g.yield d) : y < x := by
  have hdis := hT.disjoint_yield_of_adj hc hd hcd.ne
  by_contra h
  rcases le_or_gt x c with hxc | hcx
  · exact Set.disjoint_left.1 hdis ReflTransGen.refl
      ((hP d).uIcc_subset hx ReflTransGen.refl (Set.mem_uIcc.2 (Or.inl ⟨hxc, hcd.le⟩)))
  · exact Set.disjoint_left.1 hdis
      ((hP c).uIcc_subset ReflTransGen.refl hy (Set.mem_uIcc.2 (Or.inl ⟨hcx.le, not_lt.1 h⟩))) hx

theorem Graph.lt_iff_blockHead_lt {x y : Fin n} (hx : x ∈ g.yield v) (hy : y ∈ g.yield v)
    (hne : g.blockHead v y ≠ g.blockHead v x) :
    y < x ↔ (g.blockHead v y : Fin n) < g.blockHead v x := by
  have hne' : (g.blockHead v y : Fin n) ≠ g.blockHead v x := fun h ↦ hne (Subtype.ext h)
  -- it suffices to show the forward direction for both orientations
  suffices key : ∀ {x y : Fin n}, x ∈ g.yield v → y ∈ g.yield v →
      (g.blockHead v y : Fin n) < g.blockHead v x → y < x by
    refine ⟨fun h ↦ ?_, key hx hy⟩
    rcases lt_or_gt_of_ne hne' with h' | h'
    · exact h'
    · exact absurd (key hy hx h') (lt_asymm h)
  intro x y hx hy hlt
  by_cases hyv : y = v
  · have hxv : x ≠ v := by
      rintro rfl
      rw [hyv, Graph.blockHead_self hT] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨hd, hxd⟩ := Graph.adj_blockHead_of_ne hT hx hxv
    rw [hyv, Graph.blockHead_self hT] at hlt
    rw [hyv]
    exact Graph.lt_of_adj_of_mem_yield hT hP hd hlt hxd
  by_cases hxv : x = v
  · obtain ⟨hc, hyc⟩ := Graph.adj_blockHead_of_ne hT hy hyv
    rw [hxv, Graph.blockHead_self hT] at hlt
    rw [hxv]
    exact Graph.lt_of_adj_of_mem_yield' hT hP hc hlt hyc
  obtain ⟨hc, hyc⟩ := Graph.adj_blockHead_of_ne hT hy hyv
  obtain ⟨hd, hxd⟩ := Graph.adj_blockHead_of_ne hT hx hxv
  exact Graph.lt_of_mem_yield_of_mem_yield hT hP hc hd hlt hyc hxd

end Projective

/-! ### The rank, decomposed -/

section Rank

variable {g v}

theorem Graph.reorderKey_lt_iff_of_mem {x y : Fin n} (hx : x ∈ g.yield v) :
    g.reorderKey v σ y < g.reorderKey v σ x ↔
      (y ∉ g.yield v ∧ y < v) ∨
        (y ∈ g.yield v ∧
          g.siblingRank v (σ (g.blockHead v y)) < g.siblingRank v (σ (g.blockHead v x))) ∨
        (y ∈ g.yield v ∧ g.blockHead v y = g.blockHead v x ∧ y < x) := by
  have hinj : Function.Injective fun c ↦ g.siblingRank v (σ c) :=
    (g.siblingRank_strictMono v).injective.comp σ.injective
  simp only [Graph.reorderKey, Prod.Lex.toLex_lt_toLex, ite_eq_left hx, Fin.val_fin_lt]
  by_cases hy : y ∈ g.yield v
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

theorem Graph.reorderKey_lt_iff_of_notMem {x y : Fin n} (hx : x ∉ g.yield v) :
    g.reorderKey v σ y < g.reorderKey v σ x ↔
      (y ∉ g.yield v ∧ y < x) ∨ (y ∈ g.yield v ∧ v < x) := by
  have hxv : x ≠ v := fun h ↦ hx (h ▸ ReflTransGen.refl)
  simp only [Graph.reorderKey, Prod.Lex.toLex_lt_toLex, ite_eq_right hx]
  by_cases hy : y ∈ g.yield v
  · simp [hy, hxv.symm]
  · by_cases hyx : y = x
    · subst hyx
      have hy' : ¬ Dominates g v y := hy
      simp [hy']
    · simp [hy, hyx]


/-! #### The rank of a position in the yield, decomposed -/

/-- Positions outside the yield of `v` and before it. -/
private def base (g : Graph L n) (v : Fin n) : ℕ := #{y | y ∉ g.yield v ∧ y < v}

/-- The words of the blocks placed before `c` by `σ`. -/
private def before (g : Graph L n) (v : Fin n) (σ : Equiv.Perm (g.siblings v)) (c : g.siblings v) :
    ℕ :=
  #{y | y ∈ g.yield v ∧ g.siblingRank v (σ (g.blockHead v y)) < g.siblingRank v (σ c)}

/-- The words of the block of `x` before `x`. -/
private def off (g : Graph L n) (v : Fin n) (x : Fin n) : ℕ :=
  #{y | y ∈ g.yield v ∧ g.blockHead v y = g.blockHead v x ∧ y < x}

/-- The words of the block of `c`. -/
private def size (g : Graph L n) (v : Fin n) (c : g.siblings v) : ℕ :=
  #{y | y ∈ g.yield v ∧ g.blockHead v y = c}

private theorem Graph.reorderRank_of_mem {x : Fin n} (hx : x ∈ g.yield v) :
    (g.reorderRank v σ x : ℕ) = base g v + before g v σ (g.blockHead v x) + off g v x := by
  simp only [Graph.reorderRank, base, before, off]
  rw [filter_congr fun y _ ↦ Graph.reorderKey_lt_iff_of_mem σ hx, filter_or, filter_or,
    card_union_of_disjoint, card_union_of_disjoint, add_assoc]
  · exact disjoint_filter.2 fun y _ h₁ h₂ ↦ by rw [h₂.2.1] at h₁; exact lt_irrefl _ h₁.2
  · refine disjoint_union_right.2 ⟨disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1,
      disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1⟩

theorem Graph.reorderRank_of_notMem {x : Fin n} (hx : x ∉ g.yield v) :
    (g.reorderRank v σ x : ℕ) = #{y | y ∉ g.yield v ∧ y < x} + #{y | y ∈ g.yield v ∧ v < x} := by
  simp only [Graph.reorderRank]
  rw [filter_congr fun y _ ↦ Graph.reorderKey_lt_iff_of_notMem σ hx, filter_or,
    card_union_of_disjoint]
  exact disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1

theorem Graph.reorderRank_of_notMem_eq {x : Fin n} (hx : x ∉ g.yield v)
    (τ : Equiv.Perm (g.siblings v)) : g.reorderRank v σ x = g.reorderRank v τ x :=
  Fin.ext (by rw [Graph.reorderRank_of_notMem σ hx, Graph.reorderRank_of_notMem τ hx])

end Rank

/-! ### The identity permutation keeps every position -/

section One

variable {g v} (hT : g.IsTree) (hP : g.IsProjective)
include hP

theorem Graph.lt_iff_lt_of_notMem_yield {x y : Fin n} (hx : x ∈ g.yield v) (hy : y ∉ g.yield v) :
    y < x ↔ y < v := by
  constructor <;> intro h <;> by_contra h'
  · exact hy ((hP v).uIcc_subset ReflTransGen.refl hx (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))
  · exact hy ((hP v).uIcc_subset hx ReflTransGen.refl (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))

include hT

theorem Graph.reorderRank_one (x : Fin n) : g.reorderRank v 1 x = x := by
  ext
  rw [← Fin.card_Iio x]
  simp only [Graph.reorderRank]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_Iio]
  by_cases hx : x ∈ g.yield v
  · rw [Graph.reorderKey_lt_iff_of_mem 1 hx]
    simp only [Equiv.Perm.coe_one, id, (g.siblingRank_strictMono v).lt_iff_lt]
    by_cases hy : y ∈ g.yield v
    · simp only [hy, not_true_eq_false, false_and, true_and, false_or]
      by_cases hne : g.blockHead v y = g.blockHead v x
      · simp [hne]
      · simp [hne, Graph.lt_iff_blockHead_lt hT hP hx hy hne, Subtype.coe_lt_coe]
    · simp [hy, Graph.lt_iff_lt_of_notMem_yield hP hx hy]
  · rw [Graph.reorderKey_lt_iff_of_notMem 1 hx]
    by_cases hy : y ∈ g.yield v
    · have hxv : x ≠ v := fun h ↦ hx (h ▸ ReflTransGen.refl)
      have hxy : x ≠ y := fun h ↦ hx (h ▸ hy)
      have := Graph.lt_iff_lt_of_notMem_yield hP hy hx
      simp only [hy, not_true_eq_false, false_and, false_or, true_and]
      constructor <;> intro h <;> by_contra h'
      · exact absurd (this.1 (lt_of_le_of_ne (not_lt.1 h') hxy)) (lt_asymm h)
      · exact absurd (this.2 (lt_of_le_of_ne (not_lt.1 h') hxv)) (lt_asymm h)
    · simp [hy]

theorem Graph.reorderRank_of_notMem_yield {x : Fin n} (hx : x ∉ g.yield v) :
    g.reorderRank v σ x = x := by
  rw [Graph.reorderRank_of_notMem_eq σ hx 1, Graph.reorderRank_one hT hP]

end One

/-! ### Transport of total dependency length -/

section Transport

open WordOrder.Arrangement

variable {g v} (hT : g.IsTree) (hP : g.IsProjective)

/-- The head as a sibling. -/
local notation "v'" => Subtype.mk v (Graph.self_mem_siblings g v)

/-- The new rank of a sibling. -/
local notation "nr" c => g.siblingRank v (σ c)

include hT

private theorem size_self : size g v v' = 1 := by
  rw [size, card_eq_one]
  refine ⟨v, ?_⟩
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hy, h⟩
    exact (Graph.blockHead_eq_self_iff hT hy).1 (congrArg Subtype.val h)
  · rintro rfl
    exact ⟨ReflTransGen.refl, Subtype.ext (Graph.blockHead_self hT)⟩

private theorem off_self : off g v v = 0 := by
  rw [off, card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨hy, h, hlt⟩
  have h' := congrArg Subtype.val h
  rw [Graph.blockHead_self hT, Graph.blockHead_eq_self_iff hT hy] at h'
  exact lt_irrefl _ (h' ▸ hlt)

private theorem size_eq_phraseLength {c : g.siblings v} (hc : (c : Fin n) ≠ v) :
    size g v c = g.phraseLength c := by
  have hadj : g.Adj v c := by
    rcases mem_insert.1 c.2 with h | h
    · exact absurd h hc
    · exact Graph.mem_children.1 h
  rw [size, Graph.phraseLength]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset]
  constructor
  · rintro ⟨hy, h⟩
    have hyv : y ≠ v := fun e ↦ hc (by rw [← h, e, Graph.blockHead_self hT])
    exact h ▸ (Graph.adj_blockHead_of_ne hT hy hyv).2
  · intro h
    exact ⟨ReflTransGen.head hadj h, Subtype.ext (Graph.blockHead_eq_of_mem_yield hT hadj h)⟩

private theorem off_lt_size {c : g.siblings v} (hc : (c : Fin n) ≠ v) :
    off g v c < size g v c := by
  have hadj : g.Adj v c := by
    rcases mem_insert.1 c.2 with h | h
    · exact absurd h hc
    · exact Graph.mem_children.1 h
  have hcc : (g.blockHead v c) = c := Subtype.ext (Graph.blockHead_eq_of_mem_yield hT hadj .refl)
  rw [off, size, hcc]
  refine card_lt_card ((ssubset_iff_of_subset (monotone_filter_right _ fun y _ h ↦ ⟨h.1, h.2.1⟩)).2
    ⟨c, ?_, ?_⟩)
  · simp [hcc, ReflTransGen.single hadj]
  · simp

omit hT in
private theorem before_eq_sum (c : g.siblings v) :
    before g v σ c = ∑ d with (nr d) < (nr c), size g v d := by
  rw [before, card_eq_sum_card_fiberwise (f := g.blockHead v) (t := {d | (nr d) < (nr c)})
    (fun y hy ↦ by simpa using (mem_filter.1 hy).2.2)]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [size]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and] at hd ⊢
  constructor
  · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, h⟩
  · rintro ⟨hy, h⟩; exact ⟨⟨hy, h ▸ hd⟩, h⟩

omit hT in
private theorem nr_injective : Function.Injective fun c ↦ (nr c) :=
  (g.siblingRank_strictMono v).injective.comp σ.injective

private theorem before_eq_of_lt {c : g.siblings v} (hvc : (nr v') < (nr c)) :
    before g v σ c = before g v σ v' +
      boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have hcv : c ≠ v' := fun h ↦ lt_irrefl _ (h ▸ hvc)
  rw [boundaryDist, ite_eq_right hcv.symm, before_eq_sum, before_eq_sum, sum_filter, sum_filter,
    sum_filter]
  rw [← size_self hT, show ∑ x, (if (nr x) < (nr c) then size g v x else 0) =
      ∑ x, ((if (nr x) < (nr v') then size g v x else 0) + (if x = v' then size g v x else 0) +
        (if Precedes (σ.trans (g.siblingArrangement v)) v' x ∧
          Precedes (σ.trans (g.siblingArrangement v)) x c ∨
          Precedes (σ.trans (g.siblingArrangement v)) c x ∧
          Precedes (σ.trans (g.siblingArrangement v)) x v' then g.phraseLength x else 0)) from ?_]
  · simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    ring
  refine sum_congr rfl fun d _ ↦ ?_
  by_cases hd : d = v'
  · subst hd
    simp [hvc, Precedes]
  · have hne : (nr d) ≠ (nr v') := fun h ↦ hd (nr_injective σ h)
    have hdv : (d : Fin n) ≠ v := fun h ↦ hd (Subtype.ext h)
    simp only [Precedes, Equiv.trans_apply, ite_eq_right hd, add_zero]
    change (if (nr d) < (nr c) then size g v d else 0) =
      (if (nr d) < (nr v') then size g v d else 0) +
        if (nr v') < (nr d) ∧ (nr d) < (nr c) ∨ (nr c) < (nr d) ∧ (nr d) < (nr v') then
          g.phraseLength d else 0
    rw [← size_eq_phraseLength hT hdv]
    have h1 := lt_or_gt_of_ne hne
    split_ifs <;> first | rfl | omega

private theorem before_eq_of_gt {c : g.siblings v} (hcv : (nr c) < (nr v')) :
    before g v σ v' + 1 = before g v σ c + size g v c +
      boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have hcv' : c ≠ v' := fun h ↦ lt_irrefl _ (h ▸ hcv)
  rw [boundaryDist, ite_eq_right hcv'.symm, before_eq_sum, before_eq_sum, sum_filter, sum_filter,
    sum_filter]
  rw [show ∑ x, (if (nr x) < (nr v') then size g v x else 0) =
      ∑ x, ((if (nr x) < (nr c) then size g v x else 0) + (if x = c then size g v x else 0) +
        (if Precedes (σ.trans (g.siblingArrangement v)) v' x ∧
          Precedes (σ.trans (g.siblingArrangement v)) x c ∨
          Precedes (σ.trans (g.siblingArrangement v)) c x ∧
          Precedes (σ.trans (g.siblingArrangement v)) x v' then g.phraseLength x else 0)) from ?_]
  · simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    ring
  refine sum_congr rfl fun d _ ↦ ?_
  by_cases hd : d = c
  · subst hd
    simp [hcv, Precedes]
  · have hne : (nr d) ≠ (nr c) := fun h ↦ hd (nr_injective σ h)
    simp only [Precedes, Equiv.trans_apply, ite_eq_right hd, add_zero]
    by_cases hdv : d = v'
    · subst hdv
      simp [lt_asymm hcv]
    have hdv' : (d : Fin n) ≠ v := fun h ↦ hdv (Subtype.ext h)
    change (if (nr d) < (nr v') then size g v d else 0) =
      (if (nr d) < (nr c) then size g v d else 0) +
        if (nr v') < (nr d) ∧ (nr d) < (nr c) ∨ (nr c) < (nr d) ∧ (nr d) < (nr v') then
          g.phraseLength d else 0
    rw [← size_eq_phraseLength hT hdv']
    have h1 := lt_or_gt_of_ne hne
    have hne' : (nr d) ≠ (nr v') := fun h ↦ hdv (nr_injective σ h)
    have h2 := lt_or_gt_of_ne hne'
    split_ifs <;> first | rfl | omega

/-! #### Per-arc identities -/

/-- `σ` keeps every dependent on its side of the head. -/
private def SameSide : Prop := ∀ c, (nr v') < (nr c) ↔ g.siblingRank v v' < g.siblingRank v c

omit hT in
private theorem before_self_eq (hs : SameSide (σ := σ)) : before g v σ v' = before g v 1 v' := by
  simp only [before, Equiv.Perm.coe_one, id]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, and_congr_right_iff]
  intro _
  have h := hs (g.blockHead v y)
  have h1 : (nr (g.blockHead v y)) = (nr v') ↔
      g.siblingRank v (g.blockHead v y) = g.siblingRank v v' := by
    rw [(nr_injective σ).eq_iff, (g.siblingRank_strictMono v).injective.eq_iff]
  simp only [Fin.lt_def, Fin.ext_iff] at h h1 ⊢
  omega

include hP

private theorem Graph.reorderRank_head (hs : SameSide (σ := σ)) : g.reorderRank v σ v = v := by
  have h1 := Graph.reorderRank_of_mem σ (ReflTransGen.refl (r := g.Adj) (a := v))
  have h2 := Graph.reorderRank_of_mem 1 (ReflTransGen.refl (r := g.Adj) (a := v))
  have hb : g.blockHead v v = v' := Subtype.ext (Graph.blockHead_self hT)
  rw [Graph.reorderRank_one hT hP] at h2
  rw [hb] at h1 h2
  rw [before_self_eq (σ := σ) hs] at h1
  exact Fin.ext (h1.trans h2.symm)

private theorem Graph.dist_reorderRank_of_ne (hs : SameSide (σ := σ)) {u w : Fin n} (hu : u ≠ v)
    (huw : g.Adj u w) :
    Nat.dist (g.reorderRank v σ u) (g.reorderRank v σ w) = Nat.dist u w := by
  by_cases huY : u ∈ g.yield v
  · have hwY : w ∈ g.yield v := ReflTransGen.tail huY huw
    obtain ⟨hc, huc⟩ := Graph.adj_blockHead_of_ne hT huY hu
    have hbw : g.blockHead v w = g.blockHead v u :=
      Subtype.ext (Graph.blockHead_eq_of_mem_yield hT hc (ReflTransGen.tail huc huw))
    have h1 := Graph.reorderRank_of_mem σ huY
    have h2 := Graph.reorderRank_of_mem 1 huY
    have h3 := Graph.reorderRank_of_mem σ hwY
    have h4 := Graph.reorderRank_of_mem 1 hwY
    rw [Graph.reorderRank_one hT hP] at h2 h4
    rw [hbw] at h3 h4
    simp only [Nat.dist]
    omega
  · rw [Graph.reorderRank_of_notMem_yield (σ := σ) hT hP huY]
    by_cases hwY : w ∈ g.yield v
    · have hwv : w = v := by
        rcases ReflTransGen.cases_tail hwY with h | ⟨u', hu', hu'w⟩
        · exact h
        · exact absurd (hT.leftUnique_adj huw hu'w ▸ hu') huY
      subst hwv
      rw [Graph.reorderRank_head (σ := σ) hT hP hs]
    · rw [Graph.reorderRank_of_notMem_yield (σ := σ) hT hP hwY]

private theorem Graph.dist_reorderRank_add_boundaryDist (hs : SameSide (σ := σ))
    (c : g.siblings v) :
    Nat.dist (g.reorderRank v σ v) (g.reorderRank v σ c) +
        (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c) v' c =
      Nat.dist v c +
        boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  by_cases hcv : c = v'
  · subst hcv; simp
  have hcv' : (c : Fin n) ≠ v := fun h ↦ hcv (Subtype.ext h)
  have hadj : g.Adj v c := by
    rcases mem_insert.1 c.2 with h | h
    · exact absurd h hcv'
    · exact Graph.mem_children.1 h
  have hcY : (c : Fin n) ∈ g.yield v := ReflTransGen.single hadj
  have hbc : g.blockHead v c = c := Subtype.ext (Graph.blockHead_eq_of_mem_yield hT hadj .refl)
  rw [Graph.reorderRank_head (σ := σ) hT hP hs]
  have h1 := Graph.reorderRank_of_mem σ hcY
  have h2 := Graph.reorderRank_of_mem 1 hcY
  rw [Graph.reorderRank_one hT hP] at h2
  rw [hbc] at h1 h2
  have hv1 := Graph.reorderRank_of_mem 1 (ReflTransGen.refl (r := g.Adj) (a := v))
  have hb : g.blockHead v v = v' := Subtype.ext (Graph.blockHead_self hT)
  rw [Graph.reorderRank_one hT hP, hb, off_self hT] at hv1
  have hb := before_self_eq (σ := σ) hs
  have hoff := off_lt_size hT hcv'
  have hone : boundaryDist ((1 : Equiv.Perm (g.siblings v)).trans (g.siblingArrangement v))
      (fun c ↦ g.phraseLength c) v' c = (g.siblingArrangement v).boundaryDist
      (fun c ↦ g.phraseLength c) v' c := rfl
  have hne : (nr c) ≠ (nr v') := fun h ↦ hcv (nr_injective σ h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have e1 := before_eq_of_gt (σ := σ) hT hlt
    have hlt1 : g.siblingRank v c < g.siblingRank v v' := by
      have := hs c
      rcases lt_trichotomy (g.siblingRank v v') (g.siblingRank v c) with h | h | h
      · exact absurd (this.2 h) (lt_asymm hlt)
      · exact absurd ((g.siblingRank_strictMono v).injective h) (Ne.symm hcv)
      · exact h
    have e2 := before_eq_of_gt (σ := 1) hT hlt1
    rw [hone] at e2
    simp only [Nat.dist]
    omega
  · have e1 := before_eq_of_lt (σ := σ) hT hgt
    have e2 := before_eq_of_lt (σ := 1) hT ((hs c).1 hgt)
    rw [hone] at e2
    simp only [Nat.dist]
    omega

/-! #### The transport theorem -/

private theorem Graph.totalLength_reorderDependents_add_of_sameSide (hs : SameSide (σ := σ)) :
    (g.reorderDependents v σ).totalLength +
        ∑ c, (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c) v' c =
      g.totalLength +
        ∑ c, boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have hrest : ∑ u ∈ univ.erase v, ∑ w ∈ g.children u,
      Nat.dist (g.reorderRank v σ u) (g.reorderRank v σ w) =
      ∑ u ∈ univ.erase v, ∑ w ∈ g.children u, Nat.dist u w :=
    sum_congr rfl fun u hu ↦ sum_congr rfl fun w hw ↦
      Graph.dist_reorderRank_of_ne (σ := σ) hT hP hs (ne_of_mem_erase hu) (Graph.mem_children.1 hw)
  have hhead : ∀ τ : Equiv.Perm (g.siblings v), ∑ w ∈ g.children v,
      Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ w) =
      ∑ c : g.siblings v, Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ c) := fun τ ↦ by
    rw [sum_coe_sort (g.siblings v) fun w ↦ Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ w),
      Graph.siblings, sum_insert (by simpa using hT.not_adj_self), Nat.dist_self, zero_add]
  have hg : g.totalLength = ∑ u, ∑ w ∈ g.children u,
      Nat.dist (g.reorderRank v 1 u) (g.reorderRank v 1 w) := by
    simp only [Graph.reorderRank_one hT hP]; rfl
  rw [Graph.reorderDependents, Graph.totalLength_map_eq, hg]
  simp only [Graph.reorderPerm_apply]
  rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v), hhead, hhead,
    Graph.reorderRank_one hT hP]
  simp only [Graph.reorderRank_one hT hP] at hrest ⊢
  rw [hrest]
  have := Fintype.sum_congr _ _ fun c ↦ Graph.dist_reorderRank_add_boundaryDist (σ := σ) hT hP hs c
  simp only [sum_add_distrib] at this
  omega


/-! #### Behaghel's law for graphs -/

variable {σ}

omit hT hP in
private theorem sameSide_of_support_subset_after
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v') : SameSide σ := fun c ↦ by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((g.siblingArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Finset.ext_iff.1 (after_trans hσ') c
  simp only [mem_after, Precedes, Equiv.trans_apply] at this
  exact this

/-- Reordering the dependents after `v` changes total dependency length exactly as it changes the
head's boundary distances in the sibling arrangement. -/
theorem Graph.totalLength_reorderDependents_add
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v') :
    (g.reorderDependents v σ).totalLength +
        ∑ c, (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c) v' c =
      g.totalLength +
        ∑ c, boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c :=
  Graph.totalLength_reorderDependents_add_of_sameSide σ hT hP (sameSide_of_support_subset_after hσ)

theorem Graph.totalLength_le_reorderDependents
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v')
    (h : MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (g.siblingArrangement v)
      ↑((g.siblingArrangement v).after v')) :
    g.totalLength ≤ (g.reorderDependents v σ).totalLength := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((g.siblingArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Graph.totalLength_reorderDependents_add hT hP hσ
  have := sum_boundaryDist_le (fun c : g.siblings v ↦ g.phraseLength c) hσ' h
  omega

/-- The reordering is strictly longer exactly when it is not itself short before long. -/
theorem Graph.totalLength_lt_reorderDependents_iff
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v')
    (h : MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (g.siblingArrangement v)
      ↑((g.siblingArrangement v).after v')) :
    g.totalLength < (g.reorderDependents v σ).totalLength ↔
      ¬ MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (σ.trans (g.siblingArrangement v))
        ↑(after (σ.trans (g.siblingArrangement v)) v') := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((g.siblingArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Graph.totalLength_reorderDependents_add hT hP hσ
  rw [← sum_boundaryDist_lt_iff (fun c : g.siblings v ↦ g.phraseLength c) hσ' h]
  omega

end Transport


end DependencyGrammar
