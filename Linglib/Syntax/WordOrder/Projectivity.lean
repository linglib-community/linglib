/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.Digraph.Arborescence
public import Linglib.Syntax.WordOrder.Digraph
public import Mathlib.Order.Fin.Basic
public import Linglib.Core.Combinatorics.SimpleGraph.Crossings
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.Order

/-!
# Projectivity and its relaxations

In this file `G` is a digraph on linearly ordered vertices, the dependency structure of a
sentence with its words in order. The *yield* of a vertex `v` is the set `G.reachSet v` of
vertices reachable from `v`: the words of the phrase that `v` heads.

`G` is *projective* if every yield is an interval, so that every phrase is an unbroken stretch of
the sentence. Three weaker constraints are in use.

* `G` is *planar* if no two arcs cross. An arc between `a` and `b` crosses an arc between `c` and
  `d` when their ends alternate, `a < c < b < d`.
* `G` is *well-nested* if two yields interleave only when one of their two vertices dominates the
  other. Two yields interleave when two vertices of one alternate with two vertices of the other.
* The *gap degree* of `G` is the greatest number of gaps in a yield. A gap of a yield is a maximal
  run of vertices outside it that lie between two of its vertices.

A digraph is projective exactly when its gap degree is zero. On a forest, every projective
digraph is planar and every planar digraph is well-nested.

## Main definitions

* `Digraph.IsProjective`: every yield is order-connected. `Digraph.IsArcProjective` is the same
  condition stated arc by arc.
* `Digraph.gapDegree`: the greatest number of gaps in a yield.
* `Digraph.IsPlanar`: no two arcs cross. `Digraph.crossings` counts the pairs that do.
* `Digraph.Interleave`, `Digraph.IsWellNested`: interleaving yields, and the constraint on them.

## Main statements

* `Digraph.isProjective_iff_gapDegree_eq_zero`, `Digraph.isPlanar_iff_crossings_eq_zero`: each
  constraint is the least value of a count.
* `Digraph.IsProjective.isPlanar`, `Digraph.IsPlanar.isWellNested`: on a forest, projective
  digraphs are planar and planar digraphs are well-nested.
* `Digraph.IsPlanar.root_mem_Ioo`: in a planar tree, the root lies inside every gap.
* `Digraph.IsPlanar.isProjective_of_isBot`: a planar tree whose root is the first word is
  projective.
* `Digraph.isProjective_comap_orderIso`, `Digraph.isProjective_comap_ofDual`: projectivity is
  invariant under order isomorphisms and under reversal of the order, and so is planarity. The
  mirror image of a sentence is therefore projective or planar exactly when the sentence is
  (`Digraph.isProjective_mirror`, `Digraph.isPlanar_mirror`).

## References

* [kuhlmann-nivre-2006]
* [kuhlmann-2013]
-/

@[expose] public section

namespace Digraph

open Relation

variable {V W : Type*} [LinearOrder V] [LinearOrder W] (G : Digraph V) {r : V}

/-! ### Projectivity -/

/-- A digraph on a linear order is projective when the vertices reachable from each vertex are
order-connected. -/
def IsProjective : Prop := ∀ v, (G.reachSet v).OrdConnected

/-- A digraph on a linear order is arc-projective when every vertex between the ends of an arc is
reachable from the tail of the arc. -/
def IsArcProjective : Prop := ∀ ⦃h d⦄, G.Adj h d → ∀ w ∈ Set.uIcc h d, G.Reachable h w

theorem isProjective_iff :
    G.IsProjective ↔ ∀ v x, G.Reachable v x → ∀ y, G.Reachable v y →
      ∀ z, x ≤ z → z ≤ y → G.Reachable v z := by
  simp [IsProjective, Set.ordConnected_def, Set.subset_def]

variable {G} in
theorem IsArcProjective.reachable_of_mem_uIcc (hA : G.IsArcProjective) {v x : V}
    (hx : G.Reachable v x) {w : V} (hw : w ∈ Set.uIcc v x) : G.Reachable v w := by
  induction hx with
  | refl => exact (Set.uIcc_self.subset hw : w ∈ ({v} : Set V)) ▸ .refl
  | tail hvc hcx ih =>
    rcases Set.uIcc_subset_uIcc_union_uIcc hw with h₁ | h₂
    · exact ih h₁
    · exact hvc.trans (hA hcx w h₂)

theorem isProjective_iff_isArcProjective : G.IsProjective ↔ G.IsArcProjective := by
  constructor
  · intro hP h d hd w hw
    exact (hP h).uIcc_subset (mem_reachSet.2 .refl) (mem_reachSet.2 (.single hd)) hw
  · intro hA v
    refine ⟨fun x hx y hy z hz ↦ ?_⟩
    rcases Set.uIcc_subset_uIcc_union_uIcc (b := v) (Set.Icc_subset_uIcc hz) with h₁ | h₂
    · exact hA.reachable_of_mem_uIcc hx (Set.uIcc_comm x v ▸ h₁)
    · exact hA.reachable_of_mem_uIcc hy h₂

instance [Fintype V] [DecidableRel G.Adj] : Decidable G.IsProjective :=
  decidable_of_iff _ G.isProjective_iff.symm

instance [Fintype V] [DecidableRel G.Adj] : Decidable G.IsArcProjective :=
  decidable_of_iff _ G.isProjective_iff_isArcProjective

variable {G} in
theorem IsProjective.reachable_of_mem_uIcc (hP : G.IsProjective) {p t x : V} (h : G.Adj p t)
    (hx : x ∈ Set.uIcc p t) : G.Reachable p x :=
  (hP p).uIcc_subset .refl (.single h) hx

/-! ### Gap degree -/

section GapDegree

variable [Fintype V] [DecidableRel G.Adj]

private instance (a b : V) : Decidable (a ⋖ b) :=
  decidable_of_iff (a < b ∧ ∀ c, a < c → ¬ c < b) ⟨fun h ↦ ⟨h.1, fun _ hc hcb ↦ h.2 _ hc hcb⟩,
    fun h ↦ ⟨h.1, fun _ hc hcb ↦ h.2 hc hcb⟩⟩

/-- The gap degree of a vertex is the number of vertices of its reach set that are covered by a
vertex outside it while a later vertex lies inside. -/
def gapDegreeAt (v : V) : ℕ :=
  (Finset.univ.filter fun x : V ↦ x ∈ G.reachSet v ∧
    ∃ z, x ⋖ z ∧ z ∉ G.reachSet v ∧ ∃ y, z < y ∧ y ∈ G.reachSet v).card

/-- The gap degree of a digraph is the greatest gap degree of its vertices. -/
def gapDegree : ℕ := Finset.univ.sup G.gapDegreeAt

variable {G}

theorem gapDegreeAt_eq_zero_iff {v : V} : G.gapDegreeAt v = 0 ↔ (G.reachSet v).OrdConnected := by
  rw [gapDegreeAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Set.ordConnected_iff]
  refine ⟨fun h x hx y hy _ z hz ↦ ?_, fun h x _ ⟨hx, z, hxz, hzS, y, hzy, hy⟩ ↦
    hzS (h x hx y hy (hxz.lt.le.trans hzy.le) ⟨hxz.lt.le, hzy.le⟩)⟩
  by_contra hzS
  classical
  have hxz : x < z := lt_of_le_of_ne hz.1 fun e ↦ hzS (e ▸ hx)
  -- the least vertex `m` after `x` outside the reach set, and the greatest vertex `p` before `m`
  let T : Finset V := {w | x < w ∧ w ∉ G.reachSet v}
  have memT {w : V} (h₁ : x < w) (h₂ : w ∉ G.reachSet v) : w ∈ T :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h₁, h₂⟩
  have hT : T.Nonempty := ⟨z, memT hxz hzS⟩
  obtain ⟨hxm, hmS⟩ := (Finset.mem_filter.1 (T.min'_mem hT)).2
  let P : Finset V := {w | w < T.min' hT}
  have memP {w : V} (h : w < T.min' hT) : w ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
  have hP : P.Nonempty := ⟨x, memP hxm⟩
  have hpm : P.max' hP < T.min' hT := (Finset.mem_filter.1 (P.max'_mem hP)).2
  have hpS : P.max' hP ∈ G.reachSet v := by
    by_contra hpS
    rcases (P.le_max' x (memP hxm)).eq_or_lt with e | hlt
    · exact hpS (e ▸ hx)
    · exact (T.min'_le _ (memT hlt hpS)).not_gt hpm
  have hmy : T.min' hT < y :=
    lt_of_le_of_ne ((T.min'_le z (memT hxz hzS)).trans hz.2) fun e ↦ hmS (e ▸ hy)
  exact h (Finset.mem_univ _) ⟨hpS, _,
    ⟨hpm, fun c hpc hcm ↦ (P.le_max' c (memP hcm)).not_gt hpc⟩, hmS, y, hmy, hy⟩

/-- Projectivity is gap degree zero. -/
theorem isProjective_iff_gapDegree_eq_zero : G.IsProjective ↔ G.gapDegree = 0 := by
  rw [gapDegree, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff]
  simp [IsProjective, gapDegreeAt_eq_zero_iff]

end GapDegree

/-! ### Planarity -/

/-- A digraph on a linear order is planar when no two of its arcs have alternating ends, so that
the arcs can be drawn above the vertices without crossing. -/
def IsPlanar : Prop :=
  ∀ ⦃a b c d : V⦄, SymmGen G.Adj a b → SymmGen G.Adj c d → ¬ Alternate a b c d

instance [Fintype V] [DecidableRel G.Adj] : Decidable G.IsPlanar :=
  inferInstanceAs (Decidable (∀ a b c d, SymmGen G.Adj a b → SymmGen G.Adj c d →
    ¬ Alternate a b c d))

/-- The number of crossing pairs of arcs. -/
abbrev crossings [Fintype V] [DecidableRel G.Adj] : ℕ := G.toSimpleGraphInclusive.crossings

variable {G}

theorem isPlanar_iff_crossings_eq_zero [Fintype V] [DecidableRel G.Adj] :
    G.IsPlanar ↔ G.crossings = 0 := by
  rw [crossings, SimpleGraph.crossings, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h ⟨a, b, c, d⟩ - ⟨h1, h2, h3⟩
    exact h h1.2 h2.2 h3
  · exact fun h a b c d h1 h2 h3 ↦ h (Finset.mem_univ (a, b, c, d))
      ⟨⟨(h3.1.trans h3.2.1).ne, h1⟩, ⟨(h3.2.1.trans h3.2.2).ne, h2⟩, h3⟩

theorem crossings_comap [Fintype V] [DecidableRel G.Adj] {f : V → V} (hf : Function.Injective f) :
    (G.comap f).crossings = (G.toSimpleGraphInclusive.comap f).crossings := by
  unfold crossings SimpleGraph.crossings
  refine congrArg Finset.card (Finset.filter_congr fun x _ ↦ ?_)
  simp [toSimpleGraphInclusive, hf.ne_iff]

theorem IsPlanar.mem_uIcc_of_symmGen (hPl : G.IsPlanar) {lo hi p q : V}
    (hL : SymmGen G.Adj lo hi) (hL' : SymmGen G.Adj p q) (hlp : lo < p) (hph : p < hi) :
    q ∈ Set.uIcc lo hi := by
  by_contra hq
  rw [Set.uIcc_of_le (hlp.trans hph).le, Set.mem_Icc, not_and_or, not_le, not_le] at hq
  rcases hq with h | h
  · exact hPl hL'.symm hL ⟨h, hlp, hph⟩
  · exact hPl hL hL' ⟨hlp, hph, h⟩

theorem IsPlanar.mem_uIcc_of_mem_uIcc (hPl : G.IsPlanar) {p q p' q' : V}
    (hL : SymmGen G.Adj p q) (hL' : SymmGen G.Adj p' q') (hin : p' ∈ Set.uIcc p q)
    (hne1 : p' ≠ p) (hne2 : p' ≠ q) : q' ∈ Set.uIcc p q := by
  rcases le_total p q with h | h
  · rw [Set.uIcc_of_le h] at hin
    exact hPl.mem_uIcc_of_symmGen hL hL' (lt_of_le_of_ne hin.1 hne1.symm)
      (lt_of_le_of_ne hin.2 hne2)
  · rw [Set.uIcc_comm] at hin ⊢
    rw [Set.uIcc_of_le h] at hin
    exact hPl.mem_uIcc_of_symmGen hL.symm hL' (lt_of_le_of_ne hin.1 hne2.symm)
      (lt_of_le_of_ne hin.2 hne1)

/-! ### Well-nestedness -/

variable (G)

/-- The reach sets of `v` and `w` interleave when each holds two vertices and the two pairs
alternate. -/
def Interleave (v w : V) : Prop :=
  ∃ a ∈ G.reachSet v, ∃ b ∈ G.reachSet v, ∃ c ∈ G.reachSet w, ∃ d ∈ G.reachSet w, Alternate a b c d

/-- A digraph is well-nested when, of two vertices whose reach sets interleave, one reaches the
other. -/
def IsWellNested : Prop := ∀ v w : V, G.Interleave v w → G.Reachable v w ∨ G.Reachable w v

instance [Fintype V] [DecidableRel G.Adj] (v w : V) : Decidable (G.Interleave v w) :=
  inferInstanceAs (Decidable (∃ a ∈ G.reachSet v, ∃ b ∈ G.reachSet v, ∃ c ∈ G.reachSet w,
    ∃ d ∈ G.reachSet w, Alternate a b c d))

instance [Fintype V] [DecidableRel G.Adj] : Decidable G.IsWellNested :=
  inferInstanceAs (Decidable (∀ v w, G.Interleave v w → G.Reachable v w ∨ G.Reachable w v))

variable {G}

/-! ### The hierarchy on branchings -/

/-- Every projective branching is planar. -/
theorem IsProjective.isPlanar (hB : G.IsBranching) (hP : G.IsProjective) : G.IsPlanar := by
  rintro a b c d hL1 hL2 ⟨hac, hcb, hbd⟩
  -- The tail of an arc reaches the tail of any arc one of whose ends it spans.
  have step : ∀ {p t q u x : V}, G.Adj p t → G.Adj q u →
      x ∈ Set.uIcc p t → (x = q ∨ x = u) → p ≠ x → G.Reachable p q := by
    rintro p t q u x h1 h2 hx (rfl | rfl) hne
    exacts [hP.reachable_of_mem_uIcc h1 hx,
            hB.reachable_of_reachable_of_adj (hP.reachable_of_mem_uIcc h1 hx) hne h2]
  have hab : c ∈ Set.uIcc a b := Set.mem_uIcc.2 (.inl ⟨hac.le, hcb.le⟩)
  have hba : c ∈ Set.uIcc b a := Set.mem_uIcc.2 (.inr ⟨hac.le, hcb.le⟩)
  have hcd : b ∈ Set.uIcc c d := Set.mem_uIcc.2 (.inl ⟨hcb.le, hbd.le⟩)
  have hdc : b ∈ Set.uIcc d c := Set.mem_uIcc.2 (.inr ⟨hcb.le, hbd.le⟩)
  rcases hL1 with h1 | h1 <;> rcases hL2 with h2 | h2
  · exact hac.ne (hB.reachable_antisymm
      (step h1 h2 hab (.inl rfl) hac.ne) (step h2 h1 hcd (.inr rfl) hcb.ne))
  · exact ((hac.trans hcb).trans hbd).ne (hB.reachable_antisymm
      (step h1 h2 hab (.inr rfl) hac.ne) (step h2 h1 hdc (.inr rfl) hbd.ne'))
  · exact hcb.ne' (hB.reachable_antisymm
      (step h1 h2 hba (.inl rfl) hcb.ne') (step h2 h1 hcd (.inl rfl) hcb.ne))
  · exact hbd.ne (hB.reachable_antisymm
      (step h1 h2 hba (.inr rfl) hcb.ne') (step h2 h1 hdc (.inl rfl) hbd.ne'))

private theorem IsPlanar.false_of_mem_of_notMem (hPl : G.IsPlanar) {v p q x y : V}
    (hL : SymmGen G.Adj p q) (hp : ¬ G.Reachable v p) (hq : ¬ G.Reachable v q)
    (hx : G.Reachable v x) (hy : G.Reachable v y) (hin : x ∈ Set.uIcc p q)
    (hout : y ∉ Set.uIcc p q) : False := by
  obtain ⟨_, _, hL', hvp', _, hin', hout'⟩ := exists_symmGen_adj_of_mem_of_notMem hx hy hin hout
  exact hout' (hPl.mem_uIcc_of_mem_uIcc hL hL' hin' (fun h ↦ hp (h ▸ hvp'))
    (fun h ↦ hq (h ▸ hvp')))

/-- Every planar branching is well-nested. -/
theorem IsPlanar.isWellNested (hB : G.IsBranching) (hPl : G.IsPlanar) : G.IsWellNested := by
  rintro v w ⟨a, hva, b, hvb, c, hwc, d, hwd, hac, hcb, hbd⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hvw, hwv⟩ := hcon
  have hdis : ∀ {x}, G.Reachable v x → G.Reachable w x → False :=
    fun h1 h2 ↦ Set.disjoint_left.mp (hB.disjoint_reachSet hvw hwv) h1 h2
  -- An arc under `w` leaves the span of `a` and `b`.
  have hcS : c ∈ Set.Icc a b := ⟨hac.le, hcb.le⟩
  have hdS : d ∉ Set.Icc a b := fun h ↦ hbd.not_ge h.2
  obtain ⟨p, q, hLpq, hwp, hwq, hpS, hqS⟩ := exists_symmGen_adj_of_mem_of_notMem hwc hwd hcS hdS
  have hap : a < p := lt_of_le_of_ne hpS.1 (fun h ↦ hdis hva (h ▸ hwp))
  have hpb : p < b := lt_of_le_of_ne hpS.2 (fun h ↦ hdis hvb (h ▸ hwp))
  have hvp : ¬ G.Reachable v p := fun h ↦ hdis h hwp
  have hvq : ¬ G.Reachable v q := fun h ↦ hdis h hwq
  -- `q` falls on one side or the other, putting exactly one of `a`, `b` inside the arc's span.
  rcases lt_or_ge q a with hq | hq
  · exact hPl.false_of_mem_of_notMem hLpq hvp hvq hva hvb
      (Set.mem_uIcc.2 (.inr ⟨hq.le, hap.le⟩))
      (by rw [Set.mem_uIcc]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> order)
  · have hbq : b < q := lt_of_not_ge fun h ↦ hqS ⟨hq, h⟩
    exact hPl.false_of_mem_of_notMem hLpq hvp hvq hvb hva
      (Set.mem_uIcc.2 (.inl ⟨hpb.le, hbq.le⟩))
      (by rw [Set.mem_uIcc]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> order)

theorem IsPlanar.root_mem_Ioo (hA : G.IsArborescence r) (hPl : G.IsPlanar) {v i j k : V}
    (hi : G.Reachable v i) (hj : G.Reachable v j) (hik : i < k) (hkj : k < j)
    (hk : ¬ G.Reachable v k) : r ∈ Set.Ioo i j := by
  by_contra hcon
  -- `v` is not the root, so the root is not reachable from `v`.
  have hvr : ¬ G.Reachable v r := fun h ↦
    hk ((hA.reachable_antisymm h (hA.reachable v)).symm ▸ hA.reachable k)
  have hri : r ≠ i := fun h ↦ hvr (h ▸ hi)
  have hrj : r ≠ j := fun h ↦ hvr (h ▸ hj)
  have hkS : k ∈ Set.Icc i j := ⟨hik.le, hkj.le⟩
  have hrS : r ∉ Set.Icc i j := fun h ↦
    hcon ⟨lt_of_le_of_ne h.1 hri.symm, lt_of_le_of_ne h.2 hrj⟩
  -- The root's path to `k` enters the span of `i` and `j` by an arc that misses the reach set
  -- of `v`.
  obtain ⟨p, q, hpq, hpS', hqS', -, hqk⟩ :=
    (hA.reachable k).exists_boundary (S := (Set.Icc i j)ᶜ) hrS (not_not_intro hkS)
  have hpS : p ∉ Set.Icc i j := hpS'
  have hqS : q ∈ Set.Icc i j := not_not.mp hqS'
  have hqv : ¬ G.Reachable v q := fun h ↦ hk (h.trans hqk)
  have hpv : ¬ G.Reachable v p := fun h ↦ hk (h.trans ((ReflTransGen.single hpq).trans hqk))
  have hiq : i < q := lt_of_le_of_ne hqS.1 (fun h ↦ hqv (h ▸ hi))
  have hqj : q < j := lt_of_le_of_ne hqS.2 (fun h ↦ hqv (h ▸ hj))
  rcases lt_or_ge p i with hp | hp
  · exact hPl.false_of_mem_of_notMem (.inl hpq) hpv hqv hi hj
      (Set.mem_uIcc.2 (.inl ⟨hp.le, hiq.le⟩))
      (by rw [Set.mem_uIcc]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> order)
  · have hjp : j < p := lt_of_not_ge fun h ↦ hpS ⟨hp, h⟩
    exact hPl.false_of_mem_of_notMem (.inl hpq) hpv hqv hj hi
      (Set.mem_uIcc.2 (.inr ⟨hqj.le, hjp.le⟩))
      (by rw [Set.mem_uIcc]; rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> order)

/-- A planar arborescence whose root is the least vertex is projective. -/
theorem IsPlanar.isProjective_of_isBot (hA : G.IsArborescence r) (hPl : G.IsPlanar)
    (hr : IsBot r) : G.IsProjective := by
  rw [G.isProjective_iff]
  intro v x hx y hy z hxz hzy
  by_contra hz
  have hxz' : x < z := lt_of_le_of_ne hxz (fun h ↦ hz (h ▸ hx))
  have hzy' : z < y := lt_of_le_of_ne hzy (fun h ↦ hz (h ▸ hy))
  exact absurd (hPl.root_mem_Ioo hA hx hy hxz' hzy' hz).1 (not_lt.mpr (hr x))

theorem IsProjective.isWellNested (hB : G.IsBranching) (hP : G.IsProjective) : G.IsWellNested :=
  (hP.isPlanar hB).isWellNested hB

/-! ### Invariance -/

theorem IsProjective.comap (hP : G.IsProjective) (e : W ≃o V) : (G.comap e).IsProjective :=
  fun a ↦ (reachSet_comap e.toEquiv a ▸ (hP (e a)).preimage_mono e.monotone :)

theorem isProjective_comap_orderIso (e : W ≃o V) : (G.comap e).IsProjective ↔ G.IsProjective :=
  ⟨fun h ↦ by
    have e' : (G.comap e).comap e.symm = G := Digraph.ext (by ext; simp)
    exact e' ▸ h.comap e.symm, fun h ↦ h.comap e⟩

theorem isProjective_comap_ofDual :
    (G.comap OrderDual.ofDual : Digraph Vᵒᵈ).IsProjective ↔ G.IsProjective :=
  ⟨fun h v ↦ Set.ordConnected_dual.1
      (reachSet_comap OrderDual.ofDual (OrderDual.toDual v) ▸ h (OrderDual.toDual v) :),
    fun h a ↦ (reachSet_comap OrderDual.ofDual a ▸ (h _).dual :)⟩

theorem IsPlanar.comap (hPl : G.IsPlanar) (e : W ≃o V) : (G.comap e).IsPlanar :=
  fun _ _ _ _ h1 h2 h ↦ hPl h1 h2 ⟨e.lt_iff_lt.2 h.1, e.lt_iff_lt.2 h.2.1, e.lt_iff_lt.2 h.2.2⟩

theorem isPlanar_comap_orderIso (e : W ≃o V) : (G.comap e).IsPlanar ↔ G.IsPlanar :=
  ⟨fun h ↦ by
    have e' : (G.comap e).comap e.symm = G := Digraph.ext (by ext; simp)
    exact e' ▸ h.comap e.symm, fun h ↦ h.comap e⟩

theorem isPlanar_comap_ofDual :
    (G.comap OrderDual.ofDual : Digraph Vᵒᵈ).IsPlanar ↔ G.IsPlanar :=
  ⟨fun h a b c d h1 h2 alt ↦ h (a := .toDual d) (b := .toDual c) (c := .toDual b)
      (d := .toDual a) h2.symm h1.symm ⟨alt.2.2, alt.2.1, alt.1⟩,
    fun h _ _ _ _ h1 h2 alt ↦ h h2.symm h1.symm ⟨alt.2.2, alt.2.1, alt.1⟩⟩

/-! ### The mirror image -/

section Mirror

variable {n : ℕ} {G : Digraph (Fin n)}

@[simp] theorem isProjective_mirror : G.mirror.IsProjective ↔ G.IsProjective :=
  (isProjective_comap_ofDual (G := G.mirror)).symm.trans
    (isProjective_comap_orderIso (G := G) Fin.revOrderIso)

@[simp] theorem isPlanar_mirror : G.mirror.IsPlanar ↔ G.IsPlanar :=
  (isPlanar_comap_ofDual (G := G.mirror)).symm.trans
    (isPlanar_comap_orderIso (G := G) Fin.revOrderIso)

end Mirror

end Digraph
