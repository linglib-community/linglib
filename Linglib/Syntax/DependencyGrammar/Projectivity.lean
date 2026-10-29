/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Dominance
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Sort

/-!
# Projectivity and its relaxations

A dependency graph is projective when the positions each position dominates form a contiguous
stretch of the sentence. Natural language is not always projective, so the literature weakens the
constraint in several directions: planarity bans crossing arcs, well-nestedness bans interleaved
subtrees, and gap degree counts the discontinuities a single position may show.

This file defines those constraints and proves the inclusions among them that hold on forests.
The witnesses separating the constraints are the source papers' own figures, and live in their
study files.

## Main definitions

* `Graph.IsProjective`: every yield is an interval. `Graph.IsArcProjective` is its arc form,
  every arc spanning only positions its head dominates.
* `Graph.IsPlanar`: no two links cross.
* `Graph.Interleave` and `Graph.IsWellNested`: subtrees that interleave, and the ban on
  interleaving subtrees neither of whose roots dominates the other.
* `Graph.gapDegree`: the greatest number of discontinuities in the projection of a position.
* `Graph.crossings`: the number of crossing pairs of links.

## Main statements

* `Graph.isProjective_iff_gapDegree_eq_zero` and `Graph.isPlanar_iff_crossings_eq_zero`: each
  binary constraint is the least value of a count.
* `Graph.IsProjective.isPlanar` and `Graph.IsPlanar.isWellNested`: on forests, projective graphs
  are planar and planar graphs are well-nested.
* `Graph.IsPlanar.root_mem_gap` and `Graph.IsPlanar.isProjective_of_isBot`: every gap of a planar
  tree contains the root, so a planar tree rooted at a sentence boundary is projective.

## References

* [kuhlmann-nivre-2006]
* [kuhlmann-2013]
* [melcuk-1988]
* [de-marneffe-nivre-2019]
-/

@[expose] public section

namespace DependencyGrammar

variable {L : Type*} {n : ℕ} (g : Graph L n)

/-! ### The binary constraints: projectivity, planarity, well-nestedness -/

/-- A dependency graph is projective if the positions dominated by any one position are
order-convex ([kuhlmann-nivre-2006], Definition 3). -/
def Graph.IsProjective : Prop := ∀ v, (g.yield v).OrdConnected

/-- Positions `a b c d` alternate if `a < c < b < d`, so that the pairs
`{a, b}` and `{c, d}` strictly interleave. -/
abbrev Alternate (a b c d : Fin n) : Prop := a < c ∧ c < b ∧ b < d

/-- A dependency graph is planar if no two links alternate, so that its arcs can be drawn above
the sentence without crossing ([kuhlmann-nivre-2006], Definition 4). -/
def Graph.IsPlanar : Prop :=
  ∀ ⦃a b c d : Fin n⦄, g.Linked a b → g.Linked c d → ¬ Alternate a b c d

/-- The subtrees at `v` and `w` interleave if each contributes two positions
and the two pairs alternate. -/
def Graph.Interleave (v w : Fin n) : Prop :=
  ∃ a ∈ g.yield v, ∃ b ∈ g.yield v, ∃ c ∈ g.yield w, ∃ d ∈ g.yield w,
    Alternate a b c d

/-- A dependency graph is well-nested if interleaved subtrees are never disjoint, one of the two
roots always dominating the other ([kuhlmann-nivre-2006], Definition 8). -/
def Graph.IsWellNested : Prop :=
  ∀ v w : Fin n, g.Interleave v w → Dominates g v w ∨ Dominates g w v

theorem Graph.isProjective_iff :
    g.IsProjective ↔ ∀ v x, Dominates g v x → ∀ y, Dominates g v y →
      ∀ z, x ≤ z → z ≤ y → Dominates g v z := by
  simp [Graph.IsProjective, Set.ordConnected_def, Set.subset_def]

instance : Decidable g.IsProjective := decidable_of_iff _ g.isProjective_iff.symm

/-- The arc form of projectivity ([de-marneffe-nivre-2019] §2.4, after Lecerf, Hays,
Gaifman and Marcus): every position between the endpoints of an arc is dominated by
its head. -/
def Graph.IsArcProjective : Prop :=
  ∀ ⦃h d⦄, g.Adj h d → ∀ w ∈ Set.uIcc h d, Dominates g h w

theorem Graph.IsArcProjective.dominates_of_mem_uIcc {g : Graph L n} (hA : g.IsArcProjective)
    {v x : Fin n} (hx : Dominates g v x) {w : Fin n} (hw : w ∈ Set.uIcc v x) :
    Dominates g v w := by
  induction hx with
  | refl => exact (Set.uIcc_self.subset hw : w ∈ ({v} : Set (Fin n))) ▸ .refl
  | tail hvc hcx ih =>
    rcases Set.uIcc_subset_uIcc_union_uIcc hw with h₁ | h₂
    · exact ih h₁
    · exact hvc.trans (hA hcx w h₂)

theorem Graph.isProjective_iff_isArcProjective : g.IsProjective ↔ g.IsArcProjective := by
  constructor
  · intro hP h d hd w hw
    exact (hP h).uIcc_subset (Graph.mem_yield.2 .refl) (Graph.mem_yield.2 (.single hd)) hw
  · intro hA v
    refine ⟨fun x hx y hy z hz ↦ ?_⟩
    rcases Set.uIcc_subset_uIcc_union_uIcc (b := v) (Set.Icc_subset_uIcc hz) with h₁ | h₂
    · exact hA.dominates_of_mem_uIcc hx (Set.uIcc_comm x v ▸ h₁)
    · exact hA.dominates_of_mem_uIcc hy h₂

instance : Decidable g.IsArcProjective := decidable_of_iff _ g.isProjective_iff_isArcProjective
instance : Decidable g.IsPlanar := inferInstanceAs (Decidable (∀ _, _))
instance (v w : Fin n) : Decidable (g.Interleave v w) :=
  inferInstanceAs (Decidable (∃ _, _))
instance : Decidable g.IsWellNested := inferInstanceAs (Decidable (∀ _, _))

/-! ### Gap degree -/

theorem Graph.projection_pairwise_lt (v : Fin n) :
    (g.projection v).Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _

/-- The gap degree of a position counts the discontinuities in its projection, the adjacent
members more than one position apart ([kuhlmann-nivre-2006], Definition 6). -/
def Graph.gapDegreeAt (v : Fin n) : Nat :=
  ((g.projection v).zip (g.projection v).tail).countP
    (fun p ↦ decide (1 < p.2.val - p.1.val))

/-- The gap degree of a graph is the maximum over its positions. -/
def Graph.gapDegree : Nat := Finset.univ.sup g.gapDegreeAt

/-! ### Crossings -/

/-- The number of crossing link pairs, counted as quadruples `a < c < b < d`
carrying links `{a, b}` and `{c, d}`. Each crossing pair contributes once,
since of the two ways to order the pairs only one alternates. -/
def Graph.crossings : Nat :=
  (Finset.univ.filter (fun x : Fin n × Fin n × Fin n × Fin n ↦
    g.Linked x.1 x.2.1 ∧ g.Linked x.2.2.1 x.2.2.2 ∧
      Alternate x.1 x.2.1 x.2.2.1 x.2.2.2)).card

variable {g}

/-! ### Projectivity as gap degree zero -/

/-- Planarity is having no crossings — the binary constraint as the least
value of the count. -/
theorem Graph.isPlanar_iff_crossings_eq_zero : g.IsPlanar ↔ g.crossings = 0 := by
  rw [Graph.crossings, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h ⟨a, b, c, d⟩ - ⟨h1, h2, h3⟩
    exact h h1 h2 h3
  · exact fun h a b c d h1 h2 h3 ↦ h (Finset.mem_univ (a, b, c, d)) ⟨h1, h2, h3⟩


private theorem gapfree_iff_ordConnected {l : List ℕ} (h : l.IsChain (· < ·)) :
    (∀ q ∈ l.zip l.tail, q.2 - q.1 ≤ 1) ↔ Set.OrdConnected {x | x ∈ l} := by
  rw [Set.ordConnected_iff]
  simp only [Set.subset_def, Set.mem_Icc, Set.mem_ofPred_eq, and_imp]
  induction h with
  | nil => simp
  | singleton a => simp; omega
  | @cons_cons a b t hab hchain ih =>
    have hpw : (b :: t).Pairwise (· < ·) := List.isChain_iff_pairwise.mp hchain
    have hble : ∀ y ∈ b :: t, b ≤ y := by
      rintro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      exacts [Nat.le_refl _, ((List.pairwise_cons.mp hpw).1 y hy').le]
    rw [List.tail_cons, List.zip_cons_cons, List.forall_mem_cons]
    constructor
    · rintro ⟨hba, hrest⟩ x hx y hy hxy z hxz hzy
      have hb : b = a + 1 := by omega
      have hconv := ih.mp hrest
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases Nat.eq_or_lt_of_le hxz with rfl | hlt
        · exact List.mem_cons_self
        rcases List.mem_cons.mp hy with rfl | hy'
        · omega
        · exact List.mem_cons_of_mem _
            (hconv b List.mem_cons_self y hy' (hble y hy') z (by omega) hzy)
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd (hble x hx') (by omega)
        · exact List.mem_cons_of_mem _ (hconv x hx' y hy' hxy z hxz hzy)
    · intro hconv
      refine ⟨?_, ih.mpr (fun x hx y hy hxy z hxz hzy ↦ ?_)⟩
      · by_contra hgap
        rcases List.mem_cons.mp (hconv a List.mem_cons_self b
          (List.mem_cons_of_mem _ List.mem_cons_self) hab.le (a + 1) (by omega) (by omega))
          with heq | hin
        · omega
        · exact absurd (hble _ hin) (by omega)
      · rcases List.mem_cons.mp (hconv x (List.mem_cons_of_mem _ hx)
          y (List.mem_cons_of_mem _ hy) hxy z hxz hzy) with rfl | hin
        · exact absurd (hble x hx) (by omega)
        · exact hin

private theorem mem_projection_map {v : Fin n} {k : ℕ} :
    k ∈ (g.projection v).map (·.val) ↔ ∃ x : Fin n, Dominates g v x ∧ x.val = k := by
  simp [List.mem_map]

theorem Graph.gapDegreeAt_eq_zero_iff {v : Fin n} :
    g.gapDegreeAt v = 0 ↔ (g.yield v).OrdConnected := by
  have hmap : g.gapDegreeAt v =
      (((g.projection v).map (·.val)).zip ((g.projection v).map (·.val)).tail).countP
        (fun p ↦ decide (1 < p.2 - p.1)) := by
    simp [Graph.gapDegreeAt, ← List.map_tail, List.zip_map, List.countP_map,
      Function.comp_def]
  rw [hmap, List.countP_eq_zero]
  have hgf := gapfree_iff_ordConnected (l := (g.projection v).map (·.val))
    (List.isChain_iff_pairwise.mpr
      (List.Pairwise.map _ (fun _ _ h ↦ h) (g.projection_pairwise_lt v)))
  simp only [decide_eq_true_eq, Nat.not_lt] at *
  rw [hgf, Set.ordConnected_iff, Set.ordConnected_iff]
  simp only [Set.subset_def, Set.mem_Icc, Set.mem_ofPred_eq, mem_projection_map,
    Graph.mem_yield, and_imp]
  constructor
  · rintro h x hx y hy hxy z hxz hzy
    obtain ⟨w, hw, hwv⟩ := h x.val ⟨x, hx, rfl⟩ y.val ⟨y, hy, rfl⟩ hxy z.val hxz hzy
    exact (Fin.val_injective (hwv : w.val = z.val)) ▸ hw
  · rintro h k ⟨x, hx, rfl⟩ m ⟨y, hy, rfl⟩ hxy z hxz hzy
    exact ⟨⟨z, lt_of_le_of_lt hzy y.isLt⟩, h x hx y hy hxy ⟨z, _⟩ hxz hzy, rfl⟩

/-- **Projectivity is gap degree zero**: the parametric constraint at its
least value is the binary one. -/
theorem Graph.isProjective_iff_gapDegree_eq_zero :
    g.IsProjective ↔ g.gapDegree = 0 := by
  rw [Graph.gapDegree, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff]
  simp [Graph.IsProjective, Graph.gapDegreeAt_eq_zero_iff]

/-! ### The hierarchy on forests -/

theorem Graph.IsProjective.dominates_of_mem_uIcc (hP : g.IsProjective)
    {p t x : Fin n} (h : g.Adj p t) (hx : x ∈ Set.uIcc p t) : Dominates g p x :=
  (hP p).uIcc_subset .refl (.single h) hx

/-- Every projective forest is planar. -/
theorem Graph.IsProjective.isPlanar (hF : g.IsForest) (hP : g.IsProjective) :
    g.IsPlanar := by
  rintro a b c d hL1 hL2 ⟨hac, hcb, hbd⟩
  -- The head of an arc dominates the head of any arc it spans an endpoint of.
  have step : ∀ {p t q u x : Fin n}, g.Adj p t → g.Adj q u →
      x ∈ Set.uIcc p t → (x = q ∨ x = u) → p ≠ x → Dominates g p q := by
    rintro p t q u x h1 h2 hx (rfl | rfl) hne
    exacts [hP.dominates_of_mem_uIcc h1 hx,
            hF.dominates_head (hP.dominates_of_mem_uIcc h1 hx) hne h2]
  have hab : c ∈ Set.uIcc a b := by simp [Set.mem_uIcc]; omega
  have hba : c ∈ Set.uIcc b a := by simp [Set.mem_uIcc]; omega
  have hcd : b ∈ Set.uIcc c d := by simp [Set.mem_uIcc]; omega
  have hdc : b ∈ Set.uIcc d c := by simp [Set.mem_uIcc]; omega
  rcases hL1 with h1 | h1 <;> rcases hL2 with h2 | h2
  · exact hac.ne (hF.dominates_antisymm
      (step h1 h2 hab (.inl rfl) hac.ne) (step h2 h1 hcd (.inr rfl) hcb.ne))
  · exact ((hac.trans hcb).trans hbd).ne (hF.dominates_antisymm
      (step h1 h2 hab (.inr rfl) hac.ne) (step h2 h1 hdc (.inr rfl) hbd.ne'))
  · exact hcb.ne' (hF.dominates_antisymm
      (step h1 h2 hba (.inl rfl) hcb.ne') (step h2 h1 hcd (.inl rfl) hcb.ne))
  · exact hbd.ne (hF.dominates_antisymm
      (step h1 h2 hba (.inr rfl) hcb.ne') (step h2 h1 hdc (.inl rfl) hbd.ne'))

theorem Graph.IsPlanar.mem_uIcc_of_linked (hPl : g.IsPlanar) {lo hi p q : Fin n}
    (hL : g.Linked lo hi) (hL' : g.Linked p q)
    (hlp : lo < p) (hph : p < hi) : q ∈ Set.uIcc lo hi := by
  by_contra hq
  simp only [Set.mem_uIcc] at hq
  push Not at hq
  rcases (show q < lo ∨ hi < q by omega) with h | h
  · exact hPl hL'.symm hL ⟨h, hlp, hph⟩
  · exact hPl hL hL' ⟨hlp, hph, h⟩

theorem Graph.IsPlanar.no_strict_straddle (hPl : g.IsPlanar) {p q p' q' : Fin n}
    (hL : g.Linked p q) (hL' : g.Linked p' q') (hin : p' ∈ Set.uIcc p q)
    (hne1 : p' ≠ p) (hne2 : p' ≠ q) (hout : q' ∉ Set.uIcc p q) : False := by
  simp only [Set.mem_uIcc] at hin
  rcases lt_trichotomy p q with h | rfl | h
  · exact hout (hPl.mem_uIcc_of_linked hL hL' (by omega) (by omega))
  · omega
  · rw [Set.uIcc_comm] at hout
    exact hout (hPl.mem_uIcc_of_linked hL.symm hL' (by omega) (by omega))

/-- Every planar forest is well-nested: interleaved subtrees would force a link
below one of them to straddle a link below the other. -/
theorem Graph.IsPlanar.isWellNested (hF : g.IsForest) (hPl : g.IsPlanar) :
    g.IsWellNested := by
  rintro v w ⟨a, hva, b, hvb, c, hwc, d, hwd, hac, hcb, hbd⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hvw, hwv⟩ := hcon
  have hdis : ∀ {x}, Dominates g v x → Dominates g w x → False :=
    fun h1 h2 ↦ Set.disjoint_left.mp (hF.disjoint_yield hvw hwv) h1 h2
  have hab : a < b := hac.trans hcb
  -- A link below `w` crosses the boundary of the span of `a` and `b`.
  have hcS : c ∈ Set.uIcc a b := by simp [Set.mem_uIcc]; omega
  have hdS : d ∉ Set.uIcc a b := by simp [Set.mem_uIcc]; omega
  obtain ⟨p, q, hLpq, hwp, hwq, hpS, hqS⟩ := exists_link_across hwc hwd hcS hdS
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hpS hqS
  push Not at hqS
  have hap : a < p := lt_of_le_of_ne hpS.1 (fun h ↦ hdis hva (h ▸ hwp))
  have hpb : p < b := lt_of_le_of_ne hpS.2 (fun h ↦ hdis hvb (h ▸ hwp))
  -- A link below `v` spanning that link's endpoints contradicts planarity.
  have main : ∀ {x y : Fin n}, Dominates g v x → Dominates g v y →
      x ∈ Set.uIcc p q → y ∉ Set.uIcc p q → False := by
    intro x y hx hy hin hout
    obtain ⟨_, _, hL', hvp', _, hin', hout'⟩ := exists_link_across hx hy hin hout
    exact hPl.no_strict_straddle hLpq hL' hin'
      (fun h ↦ hdis hvp' (h ▸ hwp)) (fun h ↦ hdis hvp' (h ▸ hwq)) hout'
  -- `q` falls on one side or the other, putting exactly one of `a`, `b` inside.
  rcases (show q < a ∨ b < q by omega) with hq | hq
  · exact main hva hvb (by simp [Set.mem_uIcc]; omega)
      (by simp [Set.mem_uIcc]; omega)
  · exact main hvb hva (by simp [Set.mem_uIcc]; omega)
      (by simp [Set.mem_uIcc]; omega)

/-- In a planar tree every gap contains the root: if `v` dominates `i` and `j`
but skips a position between them, the root lies strictly between `i` and
`j`. So a planar tree rooted at a sentence boundary is projective, which
is why planarity buys nothing once the root is given a boundary
position. -/
theorem Graph.IsPlanar.root_mem_gap (hT : g.IsTree) (hPl : g.IsPlanar)
    {v i j k : Fin n} (hi : Dominates g v i) (hj : Dominates g v j)
    (hik : i < k) (hkj : k < j) (hk : ¬ Dominates g v k) :
    i < g.root ∧ g.root < j := by
  by_contra hcon
  push Not at hcon
  -- `v` is not the root, so the root is not among the positions `v` dominates.
  have hvr : ¬ Dominates g v g.root := fun h ↦
    hk ((hT.dominates_antisymm h (hT.root_dominates v)).symm ▸
      hT.root_dominates k)
  have hri : g.root ≠ i := fun h ↦ hvr (h ▸ hi)
  have hrj : g.root ≠ j := fun h ↦ hvr (h ▸ hj)
  have hij : i < j := hik.trans hkj
  have hkS : k ∈ Set.uIcc i j := by simp [Set.mem_uIcc]; omega
  have hrS : g.root ∉ Set.uIcc i j := by simp [Set.mem_uIcc]; omega
  -- The root's path to `k` enters the span of `i` and `j` at an arc that
  -- misses everything `v` dominates.
  obtain ⟨p, q, hpq, hpS', hqS', -, hqk⟩ :=
    (hT.root_dominates k).exists_boundary (S := (Set.uIcc i j)ᶜ) hrS
      (not_not_intro hkS)
  have hpS : p ∉ Set.uIcc i j := hpS'
  have hqS : q ∈ Set.uIcc i j := not_not.mp hqS'
  have hqv : ¬ Dominates g v q := fun h ↦ hk (h.trans hqk)
  have hpv : ¬ Dominates g v p := fun h ↦
    hk (h.trans ((Relation.ReflTransGen.single hpq).trans hqk))
  rw [Set.uIcc_of_le hij.le, Set.mem_Icc] at hpS hqS
  push Not at hpS
  have hiq : i < q := lt_of_le_of_ne hqS.1 (fun h ↦ hqv (h ▸ hi))
  have hqj : q < j := lt_of_le_of_ne hqS.2 (fun h ↦ hqv (h ▸ hj))
  have main : ∀ {x y : Fin n}, Dominates g v x → Dominates g v y →
      x ∈ Set.uIcc p q → y ∉ Set.uIcc p q → False := by
    intro x y hx hy hin hout
    obtain ⟨_, _, hL', hvp', _, hin', hout'⟩ := exists_link_across hx hy hin hout
    exact hPl.no_strict_straddle (Or.inl hpq) hL' hin'
      (fun h ↦ hpv (h ▸ hvp')) (fun h ↦ hqv (h ▸ hvp')) hout'
  rcases (show p < i ∨ j < p by omega) with hp | hp
  · exact main hi hj (by simp [Set.mem_uIcc]; omega) (by simp [Set.mem_uIcc]; omega)
  · exact main hj hi (by simp [Set.mem_uIcc]; omega) (by simp [Set.mem_uIcc]; omega)

/-- A planar tree whose root precedes every position is projective: a gap
would have to contain the root, and nothing lies to its left. -/
theorem Graph.IsPlanar.isProjective_of_isBot (hT : g.IsTree) (hPl : g.IsPlanar)
    (hr : IsBot g.root) : g.IsProjective := by
  rw [g.isProjective_iff]
  intro v x hx y hy z hxz hzy
  by_contra hz
  have hxz' : x < z := lt_of_le_of_ne hxz (fun h ↦ hz (h ▸ hx))
  have hzy' : z < y := lt_of_le_of_ne hzy (fun h ↦ hz (h ▸ hy))
  exact absurd (hPl.root_mem_gap hT hx hy hxz' hzy' hz).1 (not_lt.mpr (hr x))

/-- Every projective forest is well-nested, via planarity. -/
theorem Graph.IsProjective.isWellNested (hF : g.IsForest) (hP : g.IsProjective) :
    g.IsWellNested := (hP.isPlanar hF).isWellNested hF

end DependencyGrammar
