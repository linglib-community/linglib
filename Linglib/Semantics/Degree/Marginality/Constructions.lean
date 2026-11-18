/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Linglib.Core.Algebra.Order.Archimedean.Class
public import Linglib.Semantics.Degree.Marginality.Basic

/-!
# Constructions of marginal scales

[Marginal scales correspond to the partitions into blocks](##MarginalScale.equivSetoid) of the
underlying order: partitions whose classes are order-connected, at least two in number, and
without an endpoint facing another class. [Lexicographic pairs](##MarginalScale.lex) of a block
and a location within it are marginal scales, among them the representative model `ℚ ×ₗ ℤ` of
[dinis-jacinto-2025], as are [the differences in an order-connected
subgroup](##MarginalScale.ofAddSubgroup) of an ordered group.

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
-/

@[expose] public section

namespace MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α} {x y z : α}

/-- A partition of a linear order is into blocks when its classes are order-connected, there are
at least two of them, and none has an endpoint facing another class. -/
@[mk_iff]
structure IsBlocks (s : Setoid α) : Prop where
  /-- Each class is order-connected. -/
  ordConnected : ∀ x, {y | s x y}.OrdConnected
  /-- There are at least two classes. -/
  exists_not_rel : ∃ x y, ¬ s x y
  /-- A class below another has no greatest element. -/
  exists_gt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ z, x < z ∧ s x z
  /-- A class above another has no least element. -/
  exists_lt : ∀ ⦃x y⦄, x < y → ¬ s x y → ∃ w, w < y ∧ s w y

/-- A partition of a linear order into blocks is a marginal scale whose marginal differences are
the differences within a block. -/
def ofSetoid (s : Setoid α) (hs : IsBlocks s) : MarginalScale α where
  MarginallyLT x y := x < y ∧ s x y
  exists_large := by
    obtain ⟨x, y, h⟩ := hs.exists_not_rel
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · exact ⟨x, y, hxy, fun h' ↦ h h'.2⟩
    · exact absurd (s.refl x) h
    · exact ⟨y, x, hxy, fun h' ↦ h (s.symm h'.2)⟩
  lt_of_marginallyLT _ _ h := h.1
  irrelevance x y z hxy := by
    have hc := hs.ordConnected x
    refine ⟨fun ⟨hzy, hn⟩ ↦ ⟨lt_of_not_ge fun hxz ↦ hn ⟨hzy, ?_⟩,
      fun h ↦ hn ⟨hzy, s.trans h.2 hxy.2⟩⟩, fun ⟨hxz, hn⟩ ↦ ⟨lt_of_not_ge fun hzy ↦
      hn ⟨hxz, hc.out (s.refl x) hxy.2 ⟨hxz.le, hzy⟩⟩, fun h ↦ hn ⟨hxz, s.trans hxy.2 h.2⟩⟩⟩
    exact s.trans (s.symm (hc.out (s.refl x) hxy.2 ⟨hxz, hzy.le⟩)) hxy.2
  extends_lt x y z hxy :=
    ⟨fun ⟨hyz, hn⟩ ↦ ⟨hxy.trans hyz, fun h ↦ hn ⟨hyz,
      s.trans (s.symm ((hs.ordConnected x).out (s.refl x) h.2 ⟨hxy.le, hyz.le⟩)) h.2⟩⟩,
    fun ⟨hzx, hn⟩ ↦ ⟨hzx.trans hxy, fun h ↦ hn ⟨hzx,
      s.trans h.2 ((hs.ordConnected y).out (s.symm h.2) (s.refl y) ⟨hzx.le, hxy.le⟩)⟩⟩⟩
  decomposition x y h := by
    have hn : ¬ s x y := fun hxy ↦ h.2 ⟨h.1, hxy⟩
    obtain ⟨z, hxz, hsz⟩ := hs.exists_gt h.1 hn
    obtain ⟨w, hwy, hsw⟩ := hs.exists_lt h.1 hn
    exact ⟨⟨z, ⟨hxz, hsz⟩, lt_of_not_ge fun hyz ↦
        hn ((hs.ordConnected x).out (s.refl x) hsz ⟨h.1.le, hyz⟩), fun hm ↦ hn (s.trans hsz hm.2)⟩,
      ⟨w, ⟨hwy, hsw⟩, lt_of_not_ge fun hwx ↦ hn (s.symm ((hs.ordConnected y).out (s.symm hsw)
        (s.refl y) ⟨hwx, h.1.le⟩)), fun hm ↦ hn (s.trans hm.2 hsw)⟩⟩

section ofSetoid

variable {s : Setoid α} {hs : IsBlocks s}

@[simp]
theorem ofSetoid_marginallyLT_iff : (ofSetoid s hs).MarginallyLT x y ↔ x < y ∧ s x y := Iff.rfl

@[simp]
theorem ofSetoid_atMostMarginal_iff : (ofSetoid s hs).AtMostMarginal x y ↔ s x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ atMostMarginal_iff.2 ?_⟩
  · rcases atMostMarginal_iff.1 h with rfl | h | h
    exacts [s.refl _, h.2, s.symm h.2]
  · rcases lt_trichotomy x y with hxy | rfl | hxy
    exacts [.inr (.inl ⟨hxy, h⟩), .inl rfl, .inr (.inr ⟨hxy, s.symm h⟩)]

theorem atMostMarginalSetoid_ofSetoid : (ofSetoid s hs).atMostMarginalSetoid = s :=
  Setoid.ext fun _ _ ↦ ofSetoid_atMostMarginal_iff

end ofSetoid

variable (ml) in
theorem isBlocks_atMostMarginalSetoid : IsBlocks ml.atMostMarginalSetoid where
  ordConnected := ordConnected_setOf_atMostMarginal
  exists_not_rel := let ⟨x, y, h⟩ := ml.exists_largelyLT; ⟨x, y, h.not_atMostMarginal⟩
  exists_gt _ _ hxy hn :=
    let ⟨z, hz, _⟩ := LargelyLT.exists_marginallyLT_largelyLT
      ((marginallyLT_or_largelyLT_of_lt hxy).resolve_left fun hm ↦ hn hm.atMostMarginal)
    ⟨z, hz.lt, hz.atMostMarginal⟩
  exists_lt _ _ hxy hn :=
    let ⟨w, _, hw⟩ := LargelyLT.exists_largelyLT_marginallyLT
      ((marginallyLT_or_largelyLT_of_lt hxy).resolve_left fun hm ↦ hn hm.atMostMarginal)
    ⟨w, hw.lt, hw.atMostMarginal⟩

/-- Every marginal scale is the scale of its partition into blocks of at most marginally different
degrees. -/
theorem ofSetoid_atMostMarginalSetoid :
    ofSetoid ml.atMostMarginalSetoid ml.isBlocks_atMostMarginalSetoid = ml :=
  ext fun _ _ ↦ marginallyLT_iff_lt_and_atMostMarginal.symm

variable (α) in
/-- Marginal scales on a linear order correspond to its partitions into blocks. -/
@[simps]
def equivSetoid : MarginalScale α ≃ {s : Setoid α // IsBlocks s} where
  toFun ml := ⟨ml.atMostMarginalSetoid, ml.isBlocks_atMostMarginalSetoid⟩
  invFun s := ofSetoid s.val s.property
  left_inv _ := ofSetoid_atMostMarginalSetoid
  right_inv _ := Subtype.ext atMostMarginalSetoid_ofSetoid

section Lex

variable (β γ : Type*) [LinearOrder β] [LinearOrder γ] [Nontrivial β] [Nonempty γ]
  [NoMaxOrder γ] [NoMinOrder γ]

/-- Lexicographic pairs of a block and a location form a marginal scale in which one pair is
marginally smaller than another when they share a block and its location is smaller. -/
def lex : MarginalScale (β ×ₗ γ) :=
  ofSetoid (Setoid.ker fun p ↦ (ofLex p).1)
    { ordConnected := fun x ↦ by
        convert (Set.ordConnected_singleton (a := (ofLex x).1)).preimage_mono
          Prod.Lex.monotone_fst_ofLex using 1
        ext
        simp [Setoid.ker_def, eq_comm]
      exists_not_rel :=
        let ⟨a, b, hab⟩ := exists_pair_ne β
        let ⟨c⟩ := ‹Nonempty γ›
        ⟨toLex (a, c), toLex (b, c), hab⟩
      exists_gt := fun x _ _ _ ↦
        let ⟨c, hc⟩ := exists_gt (ofLex x).2
        ⟨toLex ((ofLex x).1, c), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hc⟩), rfl⟩
      exists_lt := fun _ y _ _ ↦
        let ⟨d, hd⟩ := exists_lt (ofLex y).2
        ⟨toLex ((ofLex y).1, d), Prod.Lex.lt_iff.2 (.inr ⟨rfl, hd⟩), rfl⟩ }

variable {β γ}

@[simp]
theorem lex_marginallyLT_iff {x y : β ×ₗ γ} :
    (lex β γ).MarginallyLT x y ↔ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 < (ofLex y).2 := by
  change x < y ∧ (ofLex x).1 = (ofLex y).1 ↔ _
  grind [Prod.Lex.lt_iff]

@[simp]
theorem lex_largelyLT_iff {x y : β ×ₗ γ} : (lex β γ).LargelyLT x y ↔ (ofLex x).1 < (ofLex y).1 := by
  change x < y ∧ ¬ (x < y ∧ (ofLex x).1 = (ofLex y).1) ↔ _
  grind [Prod.Lex.lt_iff]

@[simp]
theorem lex_atMostMarginal_iff {x y : β ×ₗ γ} :
    (lex β γ).AtMostMarginal x y ↔ (ofLex x).1 = (ofLex y).1 :=
  ofSetoid_atMostMarginal_iff

variable (β γ) in
/-- The blocks of lexicographic pairs are their first coordinates. -/
noncomputable def lexBlockOrderIso : (lex β γ).Block ≃o β :=
  StrictMono.orderIsoOfSurjective
    (Quotient.lift (fun p : β ×ₗ γ ↦ (ofLex p).1) fun _ _ h ↦
      lex_atMostMarginal_iff.1 (toBlock_eq_toBlock.1 (Quotient.sound h)))
    (fun a b ↦ Quotient.inductionOn₂ a b fun _ _ h ↦ lex_largelyLT_iff.1 (toBlock_lt_toBlock.1 h))
    fun b ↦ let ⟨c⟩ := ‹Nonempty γ›; ⟨(lex β γ).toBlock (toLex (b, c)), rfl⟩

@[simp]
theorem lexBlockOrderIso_toBlock (p : β ×ₗ γ) :
    lexBlockOrderIso β γ ((lex β γ).toBlock p) = (ofLex p).1 :=
  rfl

end Lex

section AddSubgroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The differences lying in an order-connected subgroup that is neither trivial nor everything
are the marginal differences of a marginal scale. -/
def ofAddSubgroup (H : AddSubgroup G) (hconv : (H : Set G).OrdConnected) (hbot : H ≠ ⊥)
    (htop : H ≠ ⊤) : MarginalScale G :=
  ofSetoid (QuotientAddGroup.leftRel H)
    { ordConnected := fun x ↦ by
        simp only [QuotientAddGroup.leftRel_apply]
        exact hconv.preimage_mono (f := fun y ↦ -x + y) fun _ _ h ↦ by simpa using h
      exists_not_rel := by
        obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
          by_contra! h
          exact htop (eq_top_iff.2 fun g _ ↦ h g)
        exact ⟨0, g, by simpa [QuotientAddGroup.leftRel_apply] using hg⟩
      exists_gt := fun x _ _ _ ↦ by
        obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
        exact ⟨x + h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩
      exists_lt := fun _ y _ _ ↦ by
        obtain ⟨h, hH, hpos⟩ := H.exists_pos_mem_of_ne_bot hbot
        exact ⟨y - h, by simpa using hpos, by simpa [QuotientAddGroup.leftRel_apply] using hH⟩ }

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

end MarginalScale
