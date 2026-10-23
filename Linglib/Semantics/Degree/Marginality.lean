/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Setoid.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Comparable
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.RelClasses
public import Linglib.Core.Algebra.Order.Archimedean.Class

/-!
# Marginal and large differences

Dinis and Jacinto's ML theory orders degrees by smaller than together with a relation of being
marginally smaller. A degree is largely smaller than another when it is smaller but not
marginally so. A marginal scale, the theory's ML scale, is a linear order with a
marginally-smaller-than relation obeying the five axioms of their 2026 paper, which simplify the
original theory of 2025.

Largely smaller than is a strict weak order, and its incomparability relation is at most
marginal difference. The degrees therefore fall into order-connected blocks of marginally
different degrees, no block having an endpoint that faces another block, and every such partition
of a linear order is a marginal scale. Two families of examples are lexicographic pairs of a
block and a location within it, among them the representative model `ℚ ×ₗ ℤ`, and the
differences lying in an order-connected subgroup of an ordered group, such as the infinitesimals
among the hyperreals.

## Main definitions

* `Degree.MarginalScale`: a marginal scale, with `MarginallyLT` marginally smaller than,
  `LargelyLT` largely smaller than, and `AtMostMarginal` at most marginal difference.
* `Degree.MarginalScale.ofSetoid`, `Degree.MarginalScale.lex`,
  `Degree.MarginalScale.ofAddSubgroup`: marginal scales from order-connected partitions,
  lexicographic pairs, and order-connected subgroups.
* `Degree.MarginalScale.IsHom`: a homomorphism of marginal scales.

## Main statements

* `Degree.MarginalScale.atMostMarginal_iff_incompRel`: largely smaller than is a strict weak
  order whose incomparability is at most marginal difference.
* `Degree.MarginalScale.ofSetoid_atMostMarginalSetoid`: marginal scales correspond to their
  partitions into blocks.
* `Degree.MarginalScale.isHom_lex_iff`: a map into a lexicographic marginal scale is a
  homomorphism exactly when its block coordinate pulls back largely smaller than and its location
  coordinate grows along marginal steps.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
-/

@[expose] public section

namespace Degree

/-- A marginal scale is a linear order with a relation of being marginally smaller, subject to the
five axioms of ML theory. A degree is largely smaller than another when it is smaller but not
marginally smaller. -/
structure MarginalScale (α : Type*) [LinearOrder α] where
  /-- `x` is marginally smaller than `y`. -/
  MarginallyLT : α → α → Prop
  /-- Axiom 1 says that some element is largely smaller than another. -/
  exists_large : ∃ x y, x < y ∧ ¬ MarginallyLT x y
  /-- Axiom 2 says that marginally smaller than implies smaller than. -/
  lt_of_marginallyLT : ∀ ⦃x y⦄, MarginallyLT x y → x < y
  /-- Axiom 3, M-irrelevance, says that when `x` is marginally smaller than `y`, whatever is
  largely smaller than `y` is largely smaller than `x`, and `y` is largely smaller than whatever
  `x` is largely smaller than. -/
  irrelevance : ∀ ⦃x y⦄ z, MarginallyLT x y →
    (z < y ∧ ¬ MarginallyLT z y → z < x ∧ ¬ MarginallyLT z x) ∧
      (x < z ∧ ¬ MarginallyLT x z → y < z ∧ ¬ MarginallyLT y z)
  /-- Axiom 4 says that whatever is smaller than something largely smaller than `z` is largely
  smaller than `z`, and whatever is largely smaller than something smaller than `z` is largely
  smaller than `z`. -/
  extends_lt : ∀ ⦃x y⦄ z, x < y →
    (y < z ∧ ¬ MarginallyLT y z → x < z ∧ ¬ MarginallyLT x z) ∧
      (z < x ∧ ¬ MarginallyLT z x → z < y ∧ ¬ MarginallyLT z y)
  /-- Axiom 5, Decomposition, says that a large difference is a marginal step followed by a
  large one, and a large one followed by a marginal step. -/
  decomposition : ∀ ⦃x y⦄, x < y ∧ ¬ MarginallyLT x y →
    (∃ z, MarginallyLT x z ∧ z < y ∧ ¬ MarginallyLT z y) ∧
      ∃ w, MarginallyLT w y ∧ x < w ∧ ¬ MarginallyLT x w

namespace MarginalScale

variable {α : Type*} [LinearOrder α] (ml : MarginalScale α)

/-- `x` is largely smaller than `y` when it is smaller but not marginally smaller. -/
def LargelyLT (x y : α) : Prop := x < y ∧ ¬ ml.MarginallyLT x y

/-- Two degrees differ at most marginally when they are equal or one is marginally smaller than
the other. -/
def AtMostMarginal : α → α → Prop := Relation.ReflGen (Relation.SymmGen ml.MarginallyLT)

variable {ml} {x y z : α}

@[grind =]
theorem atMostMarginal_iff :
    ml.AtMostMarginal x y ↔ x = y ∨ ml.MarginallyLT x y ∨ ml.MarginallyLT y x :=
  (Relation.reflGen_iff _ _ _).trans (or_congr_left eq_comm)

@[grind →]
theorem MarginallyLT.lt (h : ml.MarginallyLT x y) : x < y := ml.lt_of_marginallyLT h

@[grind →]
theorem LargelyLT.lt (h : ml.LargelyLT x y) : x < y := h.1

theorem MarginallyLT.not_largelyLT (h : ml.MarginallyLT x y) : ¬ ml.LargelyLT x y := fun h' ↦ h'.2 h

theorem marginallyLT_or_largelyLT_of_lt (h : x < y) : ml.MarginallyLT x y ∨ ml.LargelyLT x y :=
  (em _).imp_right (⟨h, ·⟩)

theorem LargelyLT.of_lt_of_largelyLT (hxy : x < y) (h : ml.LargelyLT y z) : ml.LargelyLT x z :=
  (ml.extends_lt z hxy).1 h

theorem LargelyLT.trans_lt (h : ml.LargelyLT x y) (hyz : y < z) : ml.LargelyLT x z :=
  (ml.extends_lt x hyz).2 h

theorem LargelyLT.trans (hxy : ml.LargelyLT x y) (hyz : ml.LargelyLT y z) : ml.LargelyLT x z :=
  hxy.trans_lt hyz.lt

/-- Marginal steps do not accrue to a large difference. -/
theorem MarginallyLT.trans (hxy : ml.MarginallyLT x y) (hyz : ml.MarginallyLT y z) :
    ml.MarginallyLT x z := by
  grind [ml.irrelevance, MarginallyLT.lt]

theorem MarginallyLT.bounded (hxz : ml.MarginallyLT x z) (hxy : x < y) (hyz : y < z) :
    ml.MarginallyLT x y ∧ ml.MarginallyLT y z := by
  grind [ml.extends_lt]

instance : IsTrans α ml.MarginallyLT := ⟨fun _ _ _ ↦ MarginallyLT.trans⟩

instance : Std.Asymm ml.LargelyLT := ⟨fun _ _ h h' ↦ h.lt.asymm h'.lt⟩

/-- Largely smaller than is negatively transitive. When one degree is largely smaller than
another, any third degree is largely greater than the first or largely smaller than the
second. -/
instance : IsOrderConnected α ml.LargelyLT where
  conn a b c h := by
    rcases le_or_gt b a with hba | hab
    · exact .inr (hba.eq_or_lt.elim (· ▸ h) (LargelyLT.of_lt_of_largelyLT · h))
    rcases le_or_gt c b with hcb | hbc
    · exact .inl (hcb.eq_or_lt.elim (· ▸ h) h.trans_lt)
    exact (marginallyLT_or_largelyLT_of_lt hab).elim
      (fun hm ↦ (marginallyLT_or_largelyLT_of_lt hbc).imp
        (fun hm' ↦ absurd (hm.trans hm') h.2) id) .inl

instance instIsStrictWeakOrderLargelyLT : IsStrictWeakOrder α ml.LargelyLT :=
  isStrictWeakOrder_of_isOrderConnected

/-- At most marginal difference is incomparability under largely smaller than. -/
theorem atMostMarginal_iff_incompRel : ml.AtMostMarginal x y ↔ IncompRel ml.LargelyLT x y := by
  simp only [AtMostMarginal, Relation.reflGen_iff, Relation.SymmGen, IncompRel]
  grind [marginallyLT_or_largelyLT_of_lt, MarginallyLT.not_largelyLT]

theorem AtMostMarginal.refl (x : α) : ml.AtMostMarginal x x := Relation.ReflGen.refl

theorem AtMostMarginal.symm (h : ml.AtMostMarginal x y) : ml.AtMostMarginal y x :=
  atMostMarginal_iff_incompRel.2 (atMostMarginal_iff_incompRel.1 h).symm

theorem AtMostMarginal.trans (hxy : ml.AtMostMarginal x y) (hyz : ml.AtMostMarginal y z) :
    ml.AtMostMarginal x z :=
  atMostMarginal_iff_incompRel.2 <| IsStrictWeakOrder.incomp_trans _ _ _
    (atMostMarginal_iff_incompRel.1 hxy) (atMostMarginal_iff_incompRel.1 hyz)

variable (ml) in
/-- At most marginal difference is an equivalence relation, sameness for present purposes. -/
def atMostMarginalSetoid : Setoid α :=
  ⟨ml.AtMostMarginal, ⟨AtMostMarginal.refl, AtMostMarginal.symm, AtMostMarginal.trans⟩⟩

theorem AtMostMarginal.largelyLT_congr_left (h : ml.AtMostMarginal x y) :
    ml.LargelyLT x z ↔ ml.LargelyLT y z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ y _ h').resolve_left h.1,
    fun h' ↦ (IsOrderConnected.conn _ x _ h').resolve_left h.2⟩

theorem AtMostMarginal.largelyLT_congr_right (h : ml.AtMostMarginal y z) :
    ml.LargelyLT x y ↔ ml.LargelyLT x z :=
  have h := atMostMarginal_iff_incompRel.1 h
  ⟨fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.2,
    fun h' ↦ (IsOrderConnected.conn _ _ _ h').resolve_right h.1⟩

theorem marginallyLT_iff_lt_and_atMostMarginal :
    ml.MarginallyLT x y ↔ x < y ∧ ml.AtMostMarginal x y := by
  grind [atMostMarginal_iff_incompRel, IncompRel, LargelyLT]

theorem ordConnected_setOf_atMostMarginal (x : α) :
    {y | ml.AtMostMarginal x y}.OrdConnected :=
  ⟨fun y hy z hz w ⟨hyw, hwz⟩ ↦ by
    rcases hyw.eq_or_lt with rfl | hyw; · exact hy
    rcases hwz.eq_or_lt with rfl | hwz; · exact hz
    have hyz := marginallyLT_iff_lt_and_atMostMarginal.2 ⟨hyw.trans hwz, hy.symm.trans hz⟩
    exact hy.trans (.single (.inl (hyz.bounded hyw hwz).1))⟩

theorem LargelyLT.infinite_setOf (h : ml.LargelyLT x y) :
    {z | ml.MarginallyLT x z ∧ ml.LargelyLT z y}.Infinite := fun hfin ↦ by
  obtain ⟨z₀, hz₀⟩ := (ml.decomposition h).1
  obtain ⟨z, ⟨hxz, hzy⟩, hmax⟩ := hfin.exists_maximal ⟨z₀, hz₀⟩
  obtain ⟨w, hzw, hwy⟩ := (ml.decomposition hzy).1
  exact (hmax ⟨hxz.trans hzw, hwy⟩ hzw.lt.le).not_gt hzw.lt

theorem LargelyLT.infinite_Ioo (h : ml.LargelyLT x y) : (Set.Ioo x y).Infinite :=
  h.infinite_setOf.mono fun _ hz ↦ ⟨hz.1.lt, hz.2.lt⟩

theorem isUpperSet_setOf_largelyLT (x : α) : IsUpperSet {y | ml.LargelyLT x y} :=
  fun _ _ hle h ↦ hle.eq_or_lt.elim (· ▸ h) h.trans_lt

/-! ### Constructions -/

/-- A partition of a linear order into order-connected blocks, at least two of them and none
with an endpoint facing another block, is a marginal scale whose marginal differences are the
differences within a block. -/
def ofSetoid (s : Setoid α) (hconv : ∀ x, {y | s x y}.OrdConnected) (hne : ∃ x y, ¬ s x y)
    (hgt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ z, x < z ∧ s x z)
    (hlt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ w, w < y ∧ s w y) : MarginalScale α where
  MarginallyLT x y := x < y ∧ s x y
  exists_large := by
    obtain ⟨x, y, h⟩ := hne
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact ⟨x, y, hxy, fun h' ↦ h h'.2⟩
    · exact absurd (s.refl x) h
    · exact ⟨y, x, hxy, fun h' ↦ h (s.symm h'.2)⟩
  lt_of_marginallyLT _ _ h := h.1
  irrelevance x y z hxy := by
    have hc := hconv x
    refine ⟨fun ⟨hzy, hn⟩ ↦ ⟨lt_of_not_ge fun hxz ↦ hn ⟨hzy, ?_⟩,
      fun h ↦ hn ⟨hzy, s.trans h.2 hxy.2⟩⟩, fun ⟨hxz, hn⟩ ↦ ⟨lt_of_not_ge fun hzy ↦
      hn ⟨hxz, hc.out (s.refl x) hxy.2 ⟨hxz.le, hzy⟩⟩, fun h ↦ hn ⟨hxz, s.trans hxy.2 h.2⟩⟩⟩
    exact s.trans (s.symm (hc.out (s.refl x) hxy.2 ⟨hxz, hzy.le⟩)) hxy.2
  extends_lt x y z hxy :=
    ⟨fun ⟨hyz, hn⟩ ↦ ⟨hxy.trans hyz, fun h ↦ hn ⟨hyz,
      s.trans (s.symm ((hconv x).out (s.refl x) h.2 ⟨hxy.le, hyz.le⟩)) h.2⟩⟩,
    fun ⟨hzx, hn⟩ ↦ ⟨hzx.trans hxy, fun h ↦ hn ⟨hzx,
      s.trans h.2 ((hconv y).out (s.symm h.2) (s.refl y) ⟨hzx.le, hxy.le⟩)⟩⟩⟩
  decomposition x y h := by
    have hn : ¬ s x y := fun hs ↦ h.2 ⟨h.1, hs⟩
    obtain ⟨z, hxz, hsz⟩ := hgt h.1 hn
    obtain ⟨w, hwy, hsw⟩ := hlt h.1 hn
    exact ⟨⟨z, ⟨hxz, hsz⟩, lt_of_not_ge fun hyz ↦ hn ((hconv x).out (s.refl x) hsz ⟨h.1.le, hyz⟩),
        fun hm ↦ hn (s.trans hsz hm.2)⟩,
      ⟨w, ⟨hwy, hsw⟩, lt_of_not_ge fun hwx ↦ hn (s.symm ((hconv y).out (s.symm hsw) (s.refl y)
        ⟨hwx, h.1.le⟩)), fun hm ↦ hn (s.trans hm.2 hsw)⟩⟩

@[ext]
theorem ext {ml ml' : MarginalScale α} (h : ∀ x y, ml.MarginallyLT x y ↔ ml'.MarginallyLT x y) :
    ml = ml' := by
  cases ml; cases ml'
  congr
  exact funext₂ fun x y ↦ propext (h x y)

/-- Every marginal scale is the scale of its partition into blocks of at most marginally different
degrees. -/
theorem ofSetoid_atMostMarginalSetoid :
    ofSetoid ml.atMostMarginalSetoid ordConnected_setOf_atMostMarginal
      (let ⟨x, y, h⟩ := ml.exists_large;
        ⟨x, y, fun h' ↦ h.2 (marginallyLT_iff_lt_and_atMostMarginal.2 ⟨h.1, h'⟩)⟩)
      (fun _ _ hxy hn ↦ let ⟨z, hz, _⟩ := (ml.decomposition ⟨hxy, fun hm ↦ hn (.single
        (.inl hm))⟩).1; ⟨z, hz.lt, .single (.inl hz)⟩)
      (fun _ _ hxy hn ↦ let ⟨w, hw, _⟩ := (ml.decomposition ⟨hxy, fun hm ↦ hn (.single
        (.inl hm))⟩).2; ⟨w, hw.lt, .single (.inl hw)⟩) = ml :=
  ext fun _ _ ↦ marginallyLT_iff_lt_and_atMostMarginal.symm

theorem atMostMarginalSetoid_ofSetoid {s : Setoid α} {hconv hne hgt hlt} :
    (ofSetoid s hconv hne hgt hlt).atMostMarginalSetoid = s := by
  refine Setoid.ext fun x y ↦ ⟨fun h ↦ ?_, fun h ↦ atMostMarginal_iff.2 ?_⟩
  · rcases atMostMarginal_iff.1 h with rfl | h | h
    exacts [s.refl _, h.2, s.symm h.2]
  · rcases lt_trichotomy x y with hxy | rfl | hxy
    exacts [.inr (.inl ⟨hxy, h⟩), .inl rfl, .inr (.inr ⟨hxy, s.symm h⟩)]

section Lex

variable (β γ : Type*) [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ]

/-- Lexicographic pairs of a block and a location form a marginal scale in which one pair is
marginally smaller than another when they share a block and its location is smaller. -/
def lex : MarginalScale (β ×ₗ γ) :=
  ofSetoid (Setoid.ker fun p ↦ (ofLex p).1)
    (fun x ↦ by
      convert (Set.ordConnected_singleton (a := (ofLex x).1)).preimage_mono
        Prod.Lex.monotone_fst_ofLex using 1
      ext
      simp [Setoid.ker_def, eq_comm])
    (let ⟨a, b, hab⟩ := exists_pair_ne β; let ⟨c⟩ := ‹Nonempty γ›
      ⟨toLex (a, c), toLex (b, c), hab⟩)
    (fun x _ _ _ ↦ let ⟨c, hc⟩ := exists_gt (ofLex x).2
      ⟨toLex ((ofLex x).1, c), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hc⟩), rfl⟩)
    (fun _ y _ _ ↦ let ⟨d, hd⟩ := exists_lt (ofLex y).2
      ⟨toLex ((ofLex y).1, d), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hd⟩), rfl⟩)

variable {β γ}

theorem lex_marginallyLT_iff {x y : β ×ₗ γ} :
    (lex β γ).MarginallyLT x y ↔ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 := by
  change x < y ∧ (ofLex x).1 = (ofLex y).1 ↔ _
  grind [Prod.Lex.lt_iff]

theorem lex_largelyLT_iff {x y : β ×ₗ γ} : (lex β γ).LargelyLT x y ↔ (ofLex x).1 < (ofLex y).1 := by
  change x < y ∧ ¬ (x < y ∧ (ofLex x).1 = (ofLex y).1) ↔ _
  grind [Prod.Lex.lt_iff]

end Lex

section AddSubgroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The differences lying in an order-connected subgroup that is neither trivial nor everything
are the marginal differences of a marginal scale. -/
def ofAddSubgroup (H : AddSubgroup G) (hconv : (H : Set G).OrdConnected) (hbot : H ≠ ⊥)
    (htop : H ≠ ⊤) : MarginalScale G :=
  ofSetoid (QuotientAddGroup.leftRel H)
    (fun x ↦ by
      simp only [QuotientAddGroup.leftRel_apply]
      exact hconv.preimage_mono (f := fun y ↦ -x + y) fun _ _ h ↦ by simpa using h)
    (by
      obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
        by_contra! h
        exact htop (eq_top_iff.2 fun g _ ↦ h g)
      exact ⟨0, g, by simpa [QuotientAddGroup.leftRel_apply] using hg⟩)
    (fun x _ _ _ ↦ by
      obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
      exact ⟨x + h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩)
    (fun _ y _ _ ↦ by
      obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
      exact ⟨y - h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩)

theorem ofAddSubgroup_marginallyLT_iff {H : AddSubgroup G} {hconv hbot htop} {x y : G} :
    (ofAddSubgroup H hconv hbot htop).MarginallyLT x y ↔ x < y ∧ y - x ∈ H := by
  simp [ofAddSubgroup, ofSetoid, QuotientAddGroup.leftRel_apply, neg_add_eq_sub]

theorem atMostMarginalSetoid_ofAddSubgroup {H : AddSubgroup G} {hconv hbot htop} :
    (ofAddSubgroup H hconv hbot htop).atMostMarginalSetoid = QuotientAddGroup.leftRel H :=
  atMostMarginalSetoid_ofSetoid

theorem ofAddSubgroup_atMostMarginal_iff {H : AddSubgroup G} {hconv hbot htop} {x y : G} :
    (ofAddSubgroup H hconv hbot htop).AtMostMarginal x y ↔ y - x ∈ H := by
  rw [← neg_add_eq_sub, ← QuotientAddGroup.leftRel_apply, ← atMostMarginalSetoid_ofAddSubgroup]
  rfl

end AddSubgroup

/-! ### Homomorphisms -/

/-- A homomorphism of marginal scales preserves and reflects smaller than and marginally smaller
than. -/
structure IsHom {β : Type*} [LinearOrder β] (ml : MarginalScale α) (ml' : MarginalScale β)
    (f : α → β) : Prop where
  strictMono : StrictMono f
  marginallyLT_iff : ∀ x y, ml'.MarginallyLT (f x) (f y) ↔ ml.MarginallyLT x y

theorem IsHom.largelyLT_iff {β : Type*} [LinearOrder β] {ml' : MarginalScale β} {f : α → β}
    (hf : ml.IsHom ml' f) : ml'.LargelyLT (f x) (f y) ↔ ml.LargelyLT x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.marginallyLT_iff x y))

section Lex

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ] {f : α → β ×ₗ γ}

/-- A map into a lexicographic marginal scale is a homomorphism exactly when its block coordinate
pulls back largely smaller than and its location coordinate grows along marginal steps. -/
theorem isHom_lex_iff :
    ml.IsHom (lex β γ) f ↔ (∀ x y, ml.LargelyLT x y ↔ (ofLex (f x)).1 < (ofLex (f y)).1) ∧
      ∀ ⦃x y⦄, ml.MarginallyLT x y → (ofLex (f x)).2 < (ofLex (f y)).2 := by
  refine ⟨fun hf ↦ ⟨fun x y ↦ hf.largelyLT_iff.symm.trans lex_largelyLT_iff,
    fun x y h ↦ (lex_marginallyLT_iff.1 ((hf.marginallyLT_iff x y).2 h)).2⟩, fun ⟨hL, hM⟩ ↦ ?_⟩
  have hfst (x y : α) : (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y := by
    rw [atMostMarginal_iff_incompRel, IncompRel, hL, hL]
    grind
  refine ⟨fun x y hxy ↦ ?_, fun x y ↦ ?_⟩
  · rw [Prod.Lex.lt_iff, hfst]
    grind [marginallyLT_or_largelyLT_of_lt]
  · rw [lex_marginallyLT_iff, hfst]
    grind

theorem IsHom.fst_eq_fst_iff (hf : ml.IsHom (lex β γ) f) :
    (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y := by
  rw [atMostMarginal_iff_incompRel, IncompRel, ← hf.largelyLT_iff, ← hf.largelyLT_iff,
    lex_largelyLT_iff, lex_largelyLT_iff]
  grind

end Lex

end MarginalScale

end Degree
