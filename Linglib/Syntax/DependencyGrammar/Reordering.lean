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

This file defines `Graph.reorderDependents g v σ`, which moves the phrases of the dependents of `v`
as whole blocks into the order that a permutation `σ` of `v` and its dependents gives them; every
position outside the yield of `v` keeps its place. On a projective forest, a reordering that keeps
each dependent on its side of the head changes only the head's own dependencies, [by the change in
their boundary distances](##DependencyGrammar.Graph.totalLength_reorderDependents_add). This is
the observation with which Gildea and Temperley begin their proof that their linearization
algorithm minimizes dependency length. When the phrases after a head grow outward, [every
reordering of them that does not is strictly
longer](##DependencyGrammar.Graph.totalLength_lt_reorderDependents_iff).

## Implementation notes

A position's new place is its rank under a key: the new rank of its block, then its old position.
The reordering therefore reduces in the kernel. Mathlib's `Tuple.sort` would not, because it sorts
with `List.mergeSort`.

## References

* [gildea-temperley-2007]
* [futrell-levy-gibson-2020]
-/

@[expose] public section

namespace DependencyGrammar

open Finset WordOrder Relation

variable {L : Type*} {n : ℕ} (g : Graph L n) (v : Fin n)

/-! ### Blocks -/

/-- `g.blockHead v x` is the sibling of `v` whose block holds `x`: the first dependent of `v`
whose phrase contains `x`, and `v` itself when there is none. -/
def Graph.blockHead (x : Fin n) : g.siblings v :=
  match h : (List.finRange n).find? (fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) with
  | some c => ⟨c, Graph.mem_siblings_of_adj
      (of_decide_eq_true (List.find?_some (p := fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) h)).1⟩
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

private theorem Graph.reorderKey_injective : Function.Injective (g.reorderKey v σ) := fun x y h ↦ by
  simpa [Graph.reorderKey] using congrArg (fun k ↦ (ofLex (ofLex k).2).2) h

private theorem Graph.reorderRank_lt_of_lt {x y : Fin n}
    (h : g.reorderKey v σ x < g.reorderKey v σ y) : g.reorderRank v σ x < g.reorderRank v σ y := by
  simp only [Graph.reorderRank, Fin.mk_lt_mk]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right _ fun z _ (hz : g.reorderKey v σ z < _) ↦ hz.trans h)).2
    ⟨x, by simp [h], by simp⟩)

private theorem Graph.reorderRank_injective : Function.Injective (g.reorderRank v σ) := by
  intro x y h
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

private theorem Graph.reorderPerm_apply (x : Fin n) :
    g.reorderPerm v σ x = g.reorderRank v σ x :=
  rfl

/-! ### Block lemmas (forests) -/

section Blocks

variable {g v}

private theorem find?_spec {x c : Fin n}
    (h : (List.finRange n).find? (fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) = some c) :
    g.Adj v c ∧ x ∈ g.yield c :=
  of_decide_eq_true (List.find?_some (p := fun c ↦ decide (g.Adj v c ∧ x ∈ g.yield c)) h)

theorem Graph.blockHead_of_notMem_yield {x : Fin n} (hx : x ∉ g.yield v) :
    (g.blockHead v x : Fin n) = v := by
  unfold Graph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd (ReflTransGen.head hc.1 hc.2) hx
  · rfl

theorem Graph.blockHead_self (hF : g.IsForest) : (g.blockHead v v : Fin n) = v := by
  unfold Graph.blockHead
  split
  · rename_i c h
    have hc := find?_spec h
    exact absurd hc.2 (hF.not_dominates_of_adj hc.1)
  · rfl

theorem Graph.blockHead_eq_of_mem_yield (hF : g.IsForest) {x c : Fin n} (hc : g.Adj v c)
    (hx : x ∈ g.yield c) : (g.blockHead v x : Fin n) = c := by
  unfold Graph.blockHead
  split
  · rename_i c' h
    have hc' := find?_spec h
    by_contra hne
    exact Set.disjoint_left.1 (hF.disjoint_yield_of_adj hc'.1 hc hne) hc'.2 hx
  · rename_i h
    have := List.find?_eq_none.1 h c (List.mem_finRange c)
    simp [hc, hx] at this

theorem Graph.adj_blockHead_of_ne (hF : g.IsForest) {x : Fin n} (hx : x ∈ g.yield v)
    (hne : x ≠ v) : g.Adj v (g.blockHead v x) ∧ x ∈ g.yield (g.blockHead v x) := by
  obtain ⟨c, hc, hxc⟩ := g.exists_adj_mem_yield hx hne
  rw [Graph.blockHead_eq_of_mem_yield hF hc hxc]
  exact ⟨hc, hxc⟩

theorem Graph.blockHead_eq_self_iff (hF : g.IsForest) {x : Fin n} (hx : x ∈ g.yield v) :
    (g.blockHead v x : Fin n) = v ↔ x = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Graph.blockHead_self hF⟩
  by_contra hne
  exact hF.ne_of_adj (Graph.adj_blockHead_of_ne hF hx hne).1 h.symm

end Blocks

/-! ### Projectivity: blocks are intervals in the order of their heads -/

section Projective

variable {g v} (hF : g.IsForest) (hP : g.IsProjective)
include hF hP

theorem Graph.lt_of_adj_of_mem_yield {d x : Fin n} (hd : g.Adj v d) (hvd : v < d)
    (hx : x ∈ g.yield d) : v < x := by
  by_contra h
  exact hF.not_dominates_of_adj hd ((hP d).uIcc_subset hx ReflTransGen.refl
    (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h, hvd.le⟩)))

theorem Graph.lt_of_adj_of_mem_yield' {d x : Fin n} (hd : g.Adj v d) (hdv : d < v)
    (hx : x ∈ g.yield d) : x < v := by
  by_contra h
  exact hF.not_dominates_of_adj hd ((hP d).uIcc_subset ReflTransGen.refl hx
    (Set.mem_uIcc.2 (Or.inl ⟨hdv.le, not_lt.1 h⟩)))

theorem Graph.lt_of_mem_yield_of_mem_yield {c d y x : Fin n} (hc : g.Adj v c) (hd : g.Adj v d)
    (hcd : c < d) (hy : y ∈ g.yield c) (hx : x ∈ g.yield d) : y < x := by
  have hdis := hF.disjoint_yield_of_adj hc hd hcd.ne
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
      rw [hyv, Graph.blockHead_self hF] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨hd, hxd⟩ := Graph.adj_blockHead_of_ne hF hx hxv
    rw [hyv, Graph.blockHead_self hF] at hlt
    rw [hyv]
    exact Graph.lt_of_adj_of_mem_yield hF hP hd hlt hxd
  by_cases hxv : x = v
  · obtain ⟨hc, hyc⟩ := Graph.adj_blockHead_of_ne hF hy hyv
    rw [hxv, Graph.blockHead_self hF] at hlt
    rw [hxv]
    exact Graph.lt_of_adj_of_mem_yield' hF hP hc hlt hyc
  obtain ⟨hc, hyc⟩ := Graph.adj_blockHead_of_ne hF hy hyv
  obtain ⟨hd, hxd⟩ := Graph.adj_blockHead_of_ne hF hx hxv
  exact Graph.lt_of_mem_yield_of_mem_yield hF hP hc hd hlt hyc hxd

end Projective

/-! ### The rank, decomposed -/

section Rank

variable {g v}

private theorem Graph.reorderKey_lt_iff_of_mem {x y : Fin n} (hx : x ∈ g.yield v) :
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

private theorem Graph.reorderKey_lt_iff_of_notMem {x y : Fin n} (hx : x ∉ g.yield v) :
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

private theorem Graph.reorderRank_of_notMem {x : Fin n} (hx : x ∉ g.yield v) :
    (g.reorderRank v σ x : ℕ) = #{y | y ∉ g.yield v ∧ y < x} + #{y | y ∈ g.yield v ∧ v < x} := by
  simp only [Graph.reorderRank]
  rw [filter_congr fun y _ ↦ Graph.reorderKey_lt_iff_of_notMem σ hx, filter_or,
    card_union_of_disjoint]
  exact disjoint_filter.2 fun y _ h₁ h₂ ↦ h₁.1 h₂.1

private theorem Graph.reorderRank_of_notMem_eq {x : Fin n} (hx : x ∉ g.yield v)
    (τ : Equiv.Perm (g.siblings v)) : g.reorderRank v σ x = g.reorderRank v τ x :=
  Fin.ext (by rw [Graph.reorderRank_of_notMem σ hx, Graph.reorderRank_of_notMem τ hx])

end Rank

/-! ### The identity permutation keeps every position -/

section One

variable {g v} (hF : g.IsForest) (hP : g.IsProjective)
include hP

theorem Graph.lt_iff_lt_of_notMem_yield {x y : Fin n} (hx : x ∈ g.yield v) (hy : y ∉ g.yield v) :
    y < x ↔ y < v := by
  constructor <;> intro h <;> by_contra h'
  · exact hy ((hP v).uIcc_subset ReflTransGen.refl hx (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))
  · exact hy ((hP v).uIcc_subset hx ReflTransGen.refl (Set.mem_uIcc.2 (Or.inl ⟨not_lt.1 h', h.le⟩)))

include hF

private theorem Graph.reorderRank_one (x : Fin n) : g.reorderRank v 1 x = x := by
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
      · simp [hne, Graph.lt_iff_blockHead_lt hF hP hx hy hne, Subtype.coe_lt_coe]
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

private theorem Graph.reorderRank_of_notMem_yield {x : Fin n} (hx : x ∉ g.yield v) :
    g.reorderRank v σ x = x := by
  rw [Graph.reorderRank_of_notMem_eq σ hx 1, Graph.reorderRank_one hF hP]

variable {σ} in
/-- Positions outside the yield of `v` keep their place. -/
theorem Graph.reorderPerm_apply_of_notMem_yield {x : Fin n} (hx : x ∉ g.yield v) :
    g.reorderPerm v σ x = x :=
  Graph.reorderRank_of_notMem_yield σ hF hP hx

theorem Graph.reorderPerm_one : g.reorderPerm v 1 = 1 :=
  Equiv.ext (Graph.reorderRank_one hF hP)

/-- Reordering by the identity leaves the graph as it was. -/
theorem Graph.reorderDependents_one : g.reorderDependents v 1 = g := by
  rw [Graph.reorderDependents, Graph.reorderPerm_one hF hP]
  rfl

end One

/-! ### Transport of total dependency length -/

section Transport

open WordOrder.Arrangement

variable {g v} (hF : g.IsForest) (hP : g.IsProjective)

/-- The head as a sibling. -/
local notation "v'" => Subtype.mk v (Graph.self_mem_siblings g v)

/-- The new rank of a sibling. -/
local notation "nr" c => g.siblingRank v (σ c)

include hF

private theorem size_self : size g v v' = 1 := by
  rw [size, card_eq_one]
  refine ⟨v, ?_⟩
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hy, h⟩
    exact (Graph.blockHead_eq_self_iff hF hy).1 (congrArg Subtype.val h)
  · rintro rfl
    exact ⟨ReflTransGen.refl, Subtype.ext (Graph.blockHead_self hF)⟩

private theorem off_self : off g v v = 0 := by
  rw [off, card_eq_zero, filter_eq_empty_iff]
  rintro y - ⟨hy, h, hlt⟩
  have h' := congrArg Subtype.val h
  rw [Graph.blockHead_self hF, Graph.blockHead_eq_self_iff hF hy] at h'
  exact lt_irrefl _ (h' ▸ hlt)

private theorem size_eq_phraseLength {c : g.siblings v} (hc : (c : Fin n) ≠ v) :
    size g v c = g.phraseLength c := by
  have hadj : g.Adj v c := (Graph.mem_siblings_iff.1 c.2).resolve_left hc
  rw [size, Graph.phraseLength]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset]
  constructor
  · rintro ⟨hy, h⟩
    have hyv : y ≠ v := fun e ↦ hc (by rw [← h, e, Graph.blockHead_self hF])
    exact h ▸ (Graph.adj_blockHead_of_ne hF hy hyv).2
  · intro h
    exact ⟨ReflTransGen.head hadj h, Subtype.ext (Graph.blockHead_eq_of_mem_yield hF hadj h)⟩

private theorem off_lt_size {c : g.siblings v} (hc : (c : Fin n) ≠ v) :
    off g v c < size g v c := by
  have hadj : g.Adj v c := (Graph.mem_siblings_iff.1 c.2).resolve_left hc
  have hcc : (g.blockHead v c) = c := Subtype.ext (Graph.blockHead_eq_of_mem_yield hF hadj .refl)
  rw [off, size, hcc]
  refine card_lt_card ((ssubset_iff_of_subset (monotone_filter_right _ fun y _ h ↦ ⟨h.1, h.2.1⟩)).2
    ⟨c, ?_, ?_⟩)
  · simp [hcc, ReflTransGen.single hadj]
  · simp

omit hF in
private theorem before_eq_sum (c : g.siblings v) :
    before g v σ c = ∑ d with Precedes (σ.trans (g.siblingArrangement v)) d c, size g v d := by
  rw [before, card_eq_sum_card_fiberwise (f := g.blockHead v)
    (t := {d | Precedes (σ.trans (g.siblingArrangement v)) d c})
    fun y hy ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hy).2.2⟩]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [size, filter_filter]
  exact congrArg card (filter_congr fun y _ ↦
    ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ (mem_filter.1 hd).2⟩, h.2⟩⟩)

omit hF in
private theorem nr_injective : Function.Injective fun c ↦ (nr c) :=
  (g.siblingRank_strictMono v).injective.comp σ.injective

/-- Between the head and `c`, the boundary distance counts the words of the blocks. -/
private theorem boundaryDist_eq_size (c : g.siblings v) :
    boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c =
      boundaryDist (σ.trans (g.siblingArrangement v)) (size g v) v' c :=
  boundaryDist_congr _ fun _ hd _ ↦ (size_eq_phraseLength hF fun e ↦ hd (Subtype.ext e)).symm

private theorem before_eq_of_lt {c : g.siblings v} (hvc : (nr v') < (nr c)) :
    before g v σ c = before g v σ v' +
      boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have h : Precedes (σ.trans (g.siblingArrangement v)) v' c := hvc
  rw [boundaryDist_eq_size σ hF, before_eq_sum, before_eq_sum, sum_precedes_of_precedes _ h,
    boundaryDist_of_precedes _ h, size_self hF, add_assoc]

private theorem before_eq_of_gt {c : g.siblings v} (hcv : (nr c) < (nr v')) :
    before g v σ v' + 1 = before g v σ c + size g v c +
      boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have h : Precedes (σ.trans (g.siblingArrangement v)) c v' := hcv
  rw [boundaryDist_eq_size σ hF, boundaryDist_comm, before_eq_sum, before_eq_sum,
    sum_precedes_of_precedes _ h, boundaryDist_of_precedes _ h]
  ring

/-! #### Per-arc identities -/

section SameSide

variable (hσ : after (σ.trans (g.siblingArrangement v)) ⟨v, g.self_mem_siblings v⟩ =
  (g.siblingArrangement v).after ⟨v, g.self_mem_siblings v⟩)
include hσ

omit hF in
/-- `σ` keeps every dependent on its side of the head. -/
private theorem nr_lt_iff (c : g.siblings v) :
    (nr v') < (nr c) ↔ g.siblingRank v v' < g.siblingRank v c := by
  have := Finset.ext_iff.1 hσ c
  simp only [mem_after, Precedes, Equiv.trans_apply] at this
  exact this

omit hF in
private theorem before_self_eq : before g v σ v' = before g v 1 v' := by
  simp only [before, Equiv.Perm.coe_one, id]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, and_congr_right_iff]
  intro _
  have h := nr_lt_iff σ hσ (g.blockHead v y)
  have h1 : (nr (g.blockHead v y)) = (nr v') ↔
      g.siblingRank v (g.blockHead v y) = g.siblingRank v v' := by
    rw [(nr_injective σ).eq_iff, (g.siblingRank_strictMono v).injective.eq_iff]
  simp only [Fin.lt_def, Fin.ext_iff] at h h1 ⊢
  omega

include hP

private theorem Graph.reorderRank_head : g.reorderRank v σ v = v := by
  have h1 := Graph.reorderRank_of_mem σ (ReflTransGen.refl (r := g.Adj) (a := v))
  have h2 := Graph.reorderRank_of_mem 1 (ReflTransGen.refl (r := g.Adj) (a := v))
  have hb : g.blockHead v v = v' := Subtype.ext (Graph.blockHead_self hF)
  rw [Graph.reorderRank_one hF hP] at h2
  rw [hb] at h1 h2
  rw [before_self_eq (σ := σ) hσ] at h1
  exact Fin.ext (h1.trans h2.symm)

private theorem Graph.dist_reorderRank_of_ne {u w : Fin n} (hu : u ≠ v)
    (huw : g.Adj u w) :
    Nat.dist (g.reorderRank v σ u) (g.reorderRank v σ w) = Nat.dist u w := by
  by_cases huY : u ∈ g.yield v
  · have hwY : w ∈ g.yield v := ReflTransGen.tail huY huw
    obtain ⟨hc, huc⟩ := Graph.adj_blockHead_of_ne hF huY hu
    have hbw : g.blockHead v w = g.blockHead v u :=
      Subtype.ext (Graph.blockHead_eq_of_mem_yield hF hc (ReflTransGen.tail huc huw))
    have h1 := Graph.reorderRank_of_mem σ huY
    have h2 := Graph.reorderRank_of_mem 1 huY
    have h3 := Graph.reorderRank_of_mem σ hwY
    have h4 := Graph.reorderRank_of_mem 1 hwY
    rw [Graph.reorderRank_one hF hP] at h2 h4
    rw [hbw] at h3 h4
    simp only [Nat.dist]
    omega
  · rw [Graph.reorderRank_of_notMem_yield (σ := σ) hF hP huY]
    by_cases hwY : w ∈ g.yield v
    · have hwv : w = v := by
        rcases ReflTransGen.cases_tail hwY with h | ⟨u', hu', hu'w⟩
        · exact h
        · exact absurd (hF.leftUnique_adj huw hu'w ▸ hu') huY
      subst hwv
      rw [Graph.reorderRank_head (σ := σ) hF hP hσ]
    · rw [Graph.reorderRank_of_notMem_yield (σ := σ) hF hP hwY]

private theorem Graph.dist_reorderRank_add_boundaryDist (c : g.siblings v) :
    Nat.dist (g.reorderRank v σ v) (g.reorderRank v σ c) +
        (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c) v' c =
      Nat.dist v c +
        boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  by_cases hcv : c = v'
  · subst hcv; simp
  have hcv' : (c : Fin n) ≠ v := fun h ↦ hcv (Subtype.ext h)
  have hadj : g.Adj v c := (Graph.mem_siblings_iff.1 c.2).resolve_left hcv'
  have hcY : (c : Fin n) ∈ g.yield v := ReflTransGen.single hadj
  have hbc : g.blockHead v c = c := Subtype.ext (Graph.blockHead_eq_of_mem_yield hF hadj .refl)
  rw [Graph.reorderRank_head (σ := σ) hF hP hσ]
  have h1 := Graph.reorderRank_of_mem σ hcY
  have h2 := Graph.reorderRank_of_mem 1 hcY
  rw [Graph.reorderRank_one hF hP] at h2
  rw [hbc] at h1 h2
  have hv1 := Graph.reorderRank_of_mem 1 (ReflTransGen.refl (r := g.Adj) (a := v))
  have hb : g.blockHead v v = v' := Subtype.ext (Graph.blockHead_self hF)
  rw [Graph.reorderRank_one hF hP, hb, off_self hF] at hv1
  have hb := before_self_eq (σ := σ) hσ
  have hoff := off_lt_size hF hcv'
  have hone : boundaryDist ((1 : Equiv.Perm (g.siblings v)).trans (g.siblingArrangement v))
      (fun c ↦ g.phraseLength c) v' c = (g.siblingArrangement v).boundaryDist
      (fun c ↦ g.phraseLength c) v' c := rfl
  have hne : (nr c) ≠ (nr v') := fun h ↦ hcv (nr_injective σ h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have e1 := before_eq_of_gt (σ := σ) hF hlt
    have hlt1 : g.siblingRank v c < g.siblingRank v v' := by
      have := nr_lt_iff σ hσ c
      rcases lt_trichotomy (g.siblingRank v v') (g.siblingRank v c) with h | h | h
      · exact absurd (this.2 h) (lt_asymm hlt)
      · exact absurd ((g.siblingRank_strictMono v).injective h) (Ne.symm hcv)
      · exact h
    have e2 := before_eq_of_gt (σ := 1) hF hlt1
    rw [hone] at e2
    simp only [Nat.dist]
    omega
  · have e1 := before_eq_of_lt (σ := σ) hF hgt
    have e2 := before_eq_of_lt (σ := 1) hF ((nr_lt_iff σ hσ c).1 hgt)
    rw [hone] at e2
    simp only [Nat.dist]
    omega

/-! #### The transport theorem -/

variable {σ}

/-- A reordering that keeps each dependent of `v` on its side of the head changes total dependency
length exactly as it changes the head's boundary distances in the sibling arrangement. A link
inside a moved phrase keeps its length and so does a link across the whole yield of `v`, so only
the head's own links change. This is the observation behind the first step of
[gildea-temperley-2007]'s proof that their linearization is optimal (p. 186). -/
theorem Graph.totalLength_reorderDependents_add :
    (g.reorderDependents v σ).totalLength +
        ∑ c, (g.siblingArrangement v).boundaryDist (fun c ↦ g.phraseLength c) v' c =
      g.totalLength +
        ∑ c, boundaryDist (σ.trans (g.siblingArrangement v)) (fun c ↦ g.phraseLength c) v' c := by
  have hrest : ∑ u ∈ univ.erase v, ∑ w ∈ g.children u,
      Nat.dist (g.reorderRank v σ u) (g.reorderRank v σ w) =
      ∑ u ∈ univ.erase v, ∑ w ∈ g.children u, Nat.dist u w :=
    sum_congr rfl fun u hu ↦ sum_congr rfl fun w hw ↦
      Graph.dist_reorderRank_of_ne σ hF hP hσ (ne_of_mem_erase hu) (Graph.mem_children.1 hw)
  have hhead : ∀ τ : Equiv.Perm (g.siblings v), ∑ w ∈ g.children v,
      Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ w) =
      ∑ c : g.siblings v, Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ c) := fun τ ↦ by
    rw [sum_coe_sort (g.siblings v) fun w ↦ Nat.dist (g.reorderRank v τ v) (g.reorderRank v τ w),
      Graph.siblings, sum_insert (by simpa using hF.not_adj_self), Nat.dist_self, zero_add]
  have hg : g.totalLength = ∑ u, ∑ w ∈ g.children u,
      Nat.dist (g.reorderRank v 1 u) (g.reorderRank v 1 w) := by
    simp only [Graph.reorderRank_one hF hP]; rfl
  rw [Graph.reorderDependents, Graph.totalLength_map_eq, hg]
  simp only [Graph.reorderPerm_apply]
  rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v), hhead, hhead,
    Graph.reorderRank_one hF hP]
  simp only [Graph.reorderRank_one hF hP] at hrest ⊢
  rw [hrest]
  have := Fintype.sum_congr _ _ fun c ↦ Graph.dist_reorderRank_add_boundaryDist σ hF hP hσ c
  simp only [sum_add_distrib] at this
  omega

end SameSide

/-! #### Growing constituents after the head -/

variable {σ}

include hP

theorem Graph.totalLength_le_reorderDependents
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v')
    (h : MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (g.siblingArrangement v)
      ↑((g.siblingArrangement v).after v')) :
    g.totalLength ≤ (g.reorderDependents v σ).totalLength := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((g.siblingArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Graph.totalLength_reorderDependents_add hF hP (after_trans hσ')
  have := sum_boundaryDist_le (fun c : g.siblings v ↦ g.phraseLength c) hσ' h
  omega

/-- When the phrases after `v` grow outward, a reordering of them is strictly longer exactly when
they do not grow outward in it: dependency length minimization predicts short-before-long order
after a head ([futrell-levy-gibson-2020]). This is the first step of [gildea-temperley-2007]'s
optimality proof (p. 186), on the side after the head. -/
theorem Graph.totalLength_lt_reorderDependents_iff
    (hσ : σ.support ⊆ (g.siblingArrangement v).after v')
    (h : MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (g.siblingArrangement v)
      ↑((g.siblingArrangement v).after v')) :
    g.totalLength < (g.reorderDependents v σ).totalLength ↔
      ¬ MonovaryOn (fun c : g.siblings v ↦ g.phraseLength c) (σ.trans (g.siblingArrangement v))
        ↑(after (σ.trans (g.siblingArrangement v)) v') := by
  have hσ' : {c | σ c ≠ c} ⊆ ↑((g.siblingArrangement v).after v') :=
    Equiv.Perm.coe_support_eq_set_support σ ▸ coe_subset.2 hσ
  have := Graph.totalLength_reorderDependents_add hF hP (after_trans hσ')
  rw [← sum_boundaryDist_lt_iff (fun c : g.siblings v ↦ g.phraseLength c) hσ' h]
  omega

end Transport

end DependencyGrammar
