/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Tree
public import Linglib.Core.Combinatorics.SimpleGraph.Crossings
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
* `Graph.gapDegree`: the greatest number of discontinuities in the yield of a position.
* `Graph.crossings`: the number of crossing pairs of links, `SimpleGraph.crossings` of the
  undirected view.

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
  ∀ v w : Fin n, g.Interleave v w → g.Dominates v w ∨ g.Dominates w v

theorem Graph.isProjective_iff :
    g.IsProjective ↔ ∀ v x, g.Dominates v x → ∀ y, g.Dominates v y →
      ∀ z, x ≤ z → z ≤ y → g.Dominates v z := by
  simp [Graph.IsProjective, Set.ordConnected_def, Set.subset_def]

instance : Decidable g.IsProjective := decidable_of_iff _ g.isProjective_iff.symm

/-- The arc form of projectivity ([de-marneffe-nivre-2019] §2.4, after Lecerf, Hays,
Gaifman and Marcus): every position between the endpoints of an arc is dominated by
its head. -/
def Graph.IsArcProjective : Prop :=
  ∀ ⦃h d⦄, g.Adj h d → ∀ w ∈ Set.uIcc h d, g.Dominates h w

theorem Graph.IsArcProjective.dominates_of_mem_uIcc {g : Graph L n} (hA : g.IsArcProjective)
    {v x : Fin n} (hx : g.Dominates v x) {w : Fin n} (hw : w ∈ Set.uIcc v x) :
    g.Dominates v w := by
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

/-- The gap degree of a position counts the discontinuities in its yield: the positions of the
yield whose successor lies outside it though a later position lies inside
([kuhlmann-nivre-2006], Definition 6). -/
def Graph.gapDegreeAt (v : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Fin n ↦ x ∈ g.yield v ∧
    ∃ z : Fin n, z.val = x.val + 1 ∧ z ∉ g.yield v ∧ ∃ y, z < y ∧ y ∈ g.yield v).card

/-- The gap degree of a graph is the maximum over its positions. -/
def Graph.gapDegree : Nat := Finset.univ.sup g.gapDegreeAt

/-! ### Crossings -/

/-- The number of crossing pairs of links, the crossings of the undirected view. -/
abbrev Graph.crossings : ℕ := g.toSimpleGraph.crossings

variable {g}

/-! ### The constraints as least values of the counts -/

/-- Planarity is having no crossings — the binary constraint as the least
value of the count. -/
theorem Graph.isPlanar_iff_crossings_eq_zero : g.IsPlanar ↔ g.crossings = 0 := by
  rw [Graph.crossings, SimpleGraph.crossings, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro h ⟨a, b, c, d⟩ - ⟨h1, h2, h3⟩
    exact h h1.2 h2.2 h3
  · exact fun h a b c d h1 h2 h3 ↦ h (Finset.mem_univ (a, b, c, d))
      ⟨⟨(h3.1.trans h3.2.1).ne, h1⟩, ⟨(h3.2.1.trans h3.2.2).ne, h2⟩, h3⟩


/-- The crossings of a transported graph are those of its undirected view relabelled. -/
theorem Graph.crossings_map (g : Graph L n) (σ : Equiv.Perm (Fin n)) :
    (g.map σ).crossings = (g.toSimpleGraph.comap σ.symm).crossings := by
  unfold Graph.crossings SimpleGraph.crossings
  refine congrArg Finset.card (Finset.filter_congr fun x _ ↦ ?_)
  simp

theorem Graph.gapDegreeAt_eq_zero_iff {v : Fin n} :
    g.gapDegreeAt v = 0 ↔ (g.yield v).OrdConnected := by
  rw [Graph.gapDegreeAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Set.ordConnected_iff]
  refine ⟨fun h x hx y hy _ z hz ↦ ?_, fun h x _ ⟨hx, z, hz, hzY, y, hzy, hy⟩ ↦
    hzY (h x hx y hy (by omega) ⟨by omega, hzy.le⟩)⟩
  by_contra hzY
  have hxz : x.val < z.val := lt_of_le_of_ne hz.1 fun e ↦ hzY (Fin.ext e ▸ hx)
  -- the least position after `x` outside the yield, and its predecessor inside
  have hex : ∃ k, x.val < k ∧ ∃ w : Fin n, w.val = k ∧ w ∉ g.yield v := ⟨z, hxz, z, rfl, hzY⟩
  classical
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.find hex := ⟨_, rfl⟩
  obtain ⟨hxk, w, hwk, hwY⟩ := Nat.find_spec hex
  have hkz : k ≤ z := hk ▸ Nat.find_min' hex ⟨hxz, z, rfl, hzY⟩
  rw [← hk] at hxk hwk
  have hp : k - 1 < n := by omega
  have hpY : (⟨k - 1, hp⟩ : Fin n) ∈ g.yield v := by
    by_contra hpY
    rcases Nat.lt_or_ge x.val (k - 1) with hlt | hge
    · exact Nat.find_min hex (by omega : k - 1 < Nat.find hex) ⟨hlt, _, rfl, hpY⟩
    · exact hpY ((Fin.ext (by simp only; omega) : (⟨k - 1, hp⟩ : Fin n) = x) ▸ hx)
  have hwy : w < y :=
    lt_of_le_of_ne (Fin.le_def.2 (by have := Fin.le_def.1 hz.2; omega)) fun e ↦ hwY (e ▸ hy)
  exact h (Finset.mem_univ ⟨k - 1, hp⟩) ⟨hpY, w, by simp only; omega, hwY, y, hwy, hy⟩

/-- **Projectivity is gap degree zero**: the parametric constraint at its
least value is the binary one. -/
theorem Graph.isProjective_iff_gapDegree_eq_zero :
    g.IsProjective ↔ g.gapDegree = 0 := by
  rw [Graph.gapDegree, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff]
  simp [Graph.IsProjective, Graph.gapDegreeAt_eq_zero_iff]

/-! ### The hierarchy on forests -/

theorem Graph.IsProjective.dominates_of_mem_uIcc (hP : g.IsProjective)
    {p t x : Fin n} (h : g.Adj p t) (hx : x ∈ Set.uIcc p t) : g.Dominates p x :=
  (hP p).uIcc_subset .refl (.single h) hx

/-- Every projective forest is planar. -/
theorem Graph.IsProjective.isPlanar (hF : g.IsForest) (hP : g.IsProjective) :
    g.IsPlanar := by
  rintro a b c d hL1 hL2 ⟨hac, hcb, hbd⟩
  -- The head of an arc dominates the head of any arc it spans an endpoint of.
  have step : ∀ {p t q u x : Fin n}, g.Adj p t → g.Adj q u →
      x ∈ Set.uIcc p t → (x = q ∨ x = u) → p ≠ x → g.Dominates p q := by
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
  have hdis : ∀ {x}, g.Dominates v x → g.Dominates w x → False :=
    fun h1 h2 ↦ Set.disjoint_left.mp (hF.disjoint_yield hvw hwv) h1 h2
  have hab : a < b := hac.trans hcb
  -- A link below `w` crosses the boundary of the span of `a` and `b`.
  have hcS : c ∈ Set.uIcc a b := by simp [Set.mem_uIcc]; omega
  have hdS : d ∉ Set.uIcc a b := by simp [Set.mem_uIcc]; omega
  obtain ⟨p, q, hLpq, hwp, hwq, hpS, hqS⟩ := Graph.exists_link_across hwc hwd hcS hdS
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hpS hqS
  push Not at hqS
  have hap : a < p := lt_of_le_of_ne hpS.1 (fun h ↦ hdis hva (h ▸ hwp))
  have hpb : p < b := lt_of_le_of_ne hpS.2 (fun h ↦ hdis hvb (h ▸ hwp))
  -- A link below `v` spanning that link's endpoints contradicts planarity.
  have main : ∀ {x y : Fin n}, g.Dominates v x → g.Dominates v y →
      x ∈ Set.uIcc p q → y ∉ Set.uIcc p q → False := by
    intro x y hx hy hin hout
    obtain ⟨_, _, hL', hvp', _, hin', hout'⟩ := Graph.exists_link_across hx hy hin hout
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
    {v i j k : Fin n} (hi : g.Dominates v i) (hj : g.Dominates v j)
    (hik : i < k) (hkj : k < j) (hk : ¬ g.Dominates v k) :
    i < g.root ∧ g.root < j := by
  by_contra hcon
  push Not at hcon
  -- `v` is not the root, so the root is not among the positions `v` dominates.
  have hvr : ¬ g.Dominates v g.root := fun h ↦
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
  have hqv : ¬ g.Dominates v q := fun h ↦ hk (h.trans hqk)
  have hpv : ¬ g.Dominates v p := fun h ↦
    hk (h.trans ((Relation.ReflTransGen.single hpq).trans hqk))
  rw [Set.uIcc_of_le hij.le, Set.mem_Icc] at hpS hqS
  push Not at hpS
  have hiq : i < q := lt_of_le_of_ne hqS.1 (fun h ↦ hqv (h ▸ hi))
  have hqj : q < j := lt_of_le_of_ne hqS.2 (fun h ↦ hqv (h ▸ hj))
  have main : ∀ {x y : Fin n}, g.Dominates v x → g.Dominates v y →
      x ∈ Set.uIcc p q → y ∉ Set.uIcc p q → False := by
    intro x y hx hy hin hout
    obtain ⟨_, _, hL', hvp', _, hin', hout'⟩ := Graph.exists_link_across hx hy hin hout
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
