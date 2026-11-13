/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Linglib.Core.Algebra.Order.Archimedean.Class
public import Linglib.Semantics.Degree.CresswellDegree

/-!
# Marginal and large differences

Dinis and Jacinto's ML theory orders degrees by smaller than together with a relation of being
marginally smaller, and a degree is largely smaller than another when it is smaller but not
marginally so. A `MarginalScale` is a linear order with such a relation obeying the five axioms of
their 2026 paper, which simplify the original theory of 2025. Largely smaller than is a strict weak
order [whose incomparability is at most marginal
difference](##MarginalScale.atMostMarginal_iff_incompRel), so the degrees fall into
[blocks](##MarginalScale.Block), the degrees that Cresswell builds from the comparison largely
smaller than, and [taking a degree to its block](##MarginalScale.toBlock_lt_toBlock) is monotone.
[Marginal scales correspond to the partitions into blocks](##MarginalScale.equivSetoid) of the
underlying order. [Lexicographic pairs](##MarginalScale.lex) of a block and a location within it
are marginal scales, among them the representative model `ℚ ×ₗ ℤ`, as are [the differences in an
order-connected subgroup](##MarginalScale.ofAddSubgroup) of an ordered group. A
[homomorphism](##MarginalScale.IsHom) of marginal scales [embeds the blocks of one in those of the
other](##MarginalScale.IsHom.mapBlock).

## References

* [dinis-jacinto-2025]
* [dinis-jacinto-2026]
* [cresswell-1976]
-/

@[expose] public section

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

@[ext]
theorem ext {ml ml' : MarginalScale α} (h : ∀ x y, ml.MarginallyLT x y ↔ ml'.MarginallyLT x y) :
    ml = ml' := by
  cases ml; cases ml'
  congr
  exact funext₂ fun x y ↦ propext (h x y)

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

variable (ml) in
theorem exists_largelyLT : ∃ x y, ml.LargelyLT x y := ml.exists_large

@[grind →]
theorem MarginallyLT.lt (h : ml.MarginallyLT x y) : x < y := ml.lt_of_marginallyLT h

@[grind →]
theorem LargelyLT.lt (h : ml.LargelyLT x y) : x < y := h.1

theorem MarginallyLT.not_largelyLT (h : ml.MarginallyLT x y) : ¬ ml.LargelyLT x y := fun h' ↦ h'.2 h

theorem MarginallyLT.atMostMarginal (h : ml.MarginallyLT x y) : ml.AtMostMarginal x y :=
  .single (.inl h)

theorem LargelyLT.exists_marginallyLT_largelyLT (h : ml.LargelyLT x y) :
    ∃ z, ml.MarginallyLT x z ∧ ml.LargelyLT z y :=
  (ml.decomposition h).1

theorem LargelyLT.exists_largelyLT_marginallyLT (h : ml.LargelyLT x y) :
    ∃ w, ml.LargelyLT x w ∧ ml.MarginallyLT w y :=
  let ⟨w, hw⟩ := (ml.decomposition h).2
  ⟨w, hw.symm⟩

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

instance : IsStrictOrder α ml.MarginallyLT where
  irrefl _ h := h.lt.false
  trans _ _ _ := MarginallyLT.trans

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

theorem LargelyLT.not_atMostMarginal (h : ml.LargelyLT x y) : ¬ ml.AtMostMarginal x y :=
  fun h' ↦ (atMostMarginal_iff_incompRel.1 h').1 h

/-! ### Blocks -/

variable (ml) in
/-- The blocks of a marginal scale are its classes of at most marginally different degrees,
ordered by largely smaller than. They are the degrees that [cresswell-1976] builds from the
comparison largely smaller than. -/
def Block : Type _ := CresswellDegree (Function.swap ml.LargelyLT)

variable (ml) in
/-- The block of a degree. -/
def toBlock (x : α) : ml.Block := Quotient.mk _ x

noncomputable instance : LinearOrder ml.Block := by
  classical exact inferInstanceAs (LinearOrder (CresswellDegree (Function.swap ml.LargelyLT)))

@[elab_as_elim]
protected theorem Block.ind {p : ml.Block → Prop} (h : ∀ x, p (ml.toBlock x)) (b : ml.Block) :
    p b :=
  Quotient.ind h b

variable (ml) in
theorem toBlock_surjective : Function.Surjective ml.toBlock := Block.ind fun x ↦ ⟨x, rfl⟩

/-- One block comes before another exactly when its degrees are largely smaller. -/
@[simp]
theorem toBlock_lt_toBlock : ml.toBlock x < ml.toBlock y ↔ ml.LargelyLT x y := Iff.rfl

@[simp]
theorem toBlock_eq_toBlock : ml.toBlock x = ml.toBlock y ↔ ml.AtMostMarginal x y := by
  rw [atMostMarginal_iff_incompRel, ← incompRel_swap, ← cresswellSetoid_iff_incompRel]
  exact Quotient.eq

theorem toBlock_le_toBlock : ml.toBlock x ≤ ml.toBlock y ↔ ¬ ml.LargelyLT y x :=
  not_lt.symm.trans (not_congr toBlock_lt_toBlock)

variable (ml) in
theorem toBlock_mono : Monotone ml.toBlock :=
  fun _ _ h ↦ toBlock_le_toBlock.2 fun h' ↦ h'.lt.not_ge h

variable (ml) in
/-- Taking a degree to its block, as an order homomorphism. -/
@[simps]
def toBlockHom : α →o ml.Block := ⟨ml.toBlock, ml.toBlock_mono⟩

instance : Nontrivial ml.Block :=
  let ⟨_, _, h⟩ := ml.exists_largelyLT
  ⟨_, _, (toBlock_lt_toBlock.2 h).ne⟩

instance [Countable α] : Countable ml.Block := ml.toBlock_surjective.countable

/-- Two degrees differ at most marginally or one is largely smaller than the other. -/
theorem largelyLT_or_atMostMarginal_or_largelyLT (x y : α) :
    ml.LargelyLT x y ∨ ml.AtMostMarginal x y ∨ ml.LargelyLT y x := by
  simpa using lt_trichotomy (ml.toBlock x) (ml.toBlock y)

theorem ordConnected_setOf_atMostMarginal (x : α) :
    {y | ml.AtMostMarginal x y}.OrdConnected := by
  convert (Set.ordConnected_singleton (a := ml.toBlock x)).preimage_mono ml.toBlock_mono using 1
  ext y
  exact toBlock_eq_toBlock.symm.trans eq_comm

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

/-! ### Homomorphisms -/

/-- A homomorphism of marginal scales preserves and reflects smaller than and marginally smaller
than. -/
structure IsHom {β : Type*} [LinearOrder β] (ml : MarginalScale α) (ml' : MarginalScale β)
    (f : α → β) : Prop where
  strictMono : StrictMono f
  marginallyLT_iff : ∀ x y, ml'.MarginallyLT (f x) (f y) ↔ ml.MarginallyLT x y

section IsHom

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] {ml' : MarginalScale β}
  {ml'' : MarginalScale γ} {f : α → β} {g : β → γ}

theorem IsHom.largelyLT_iff (hf : ml.IsHom ml' f) : ml'.LargelyLT (f x) (f y) ↔ ml.LargelyLT x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.marginallyLT_iff x y))

theorem IsHom.atMostMarginal_iff (hf : ml.IsHom ml' f) :
    ml'.AtMostMarginal (f x) (f y) ↔ ml.AtMostMarginal x y := by
  simp only [atMostMarginal_iff_incompRel, IncompRel, hf.largelyLT_iff]

theorem IsHom.injective (hf : ml.IsHom ml' f) : Function.Injective f := hf.strictMono.injective

/-- A map is a homomorphism exactly when it is strictly monotone and preserves and reflects at
most marginal difference. -/
theorem isHom_iff_atMostMarginal : ml.IsHom ml' f ↔
    StrictMono f ∧ ∀ x y, ml'.AtMostMarginal (f x) (f y) ↔ ml.AtMostMarginal x y :=
  ⟨fun hf ↦ ⟨hf.strictMono, fun _ _ ↦ hf.atMostMarginal_iff⟩, fun ⟨hf, h⟩ ↦ ⟨hf, fun x y ↦ by
    rw [marginallyLT_iff_lt_and_atMostMarginal, marginallyLT_iff_lt_and_atMostMarginal,
      hf.lt_iff_lt, h]⟩⟩

variable (ml) in
protected theorem IsHom.id : ml.IsHom ml id := ⟨strictMono_id, fun _ _ ↦ Iff.rfl⟩

theorem IsHom.comp (hg : ml'.IsHom ml'' g) (hf : ml.IsHom ml' f) : ml.IsHom ml'' (g ∘ f) :=
  ⟨hg.strictMono.comp hf.strictMono,
    fun x y ↦ (hg.marginallyLT_iff _ _).trans (hf.marginallyLT_iff x y)⟩

/-- A homomorphism of marginal scales embeds the blocks of one in the blocks of the other. -/
noncomputable def IsHom.mapBlock (hf : ml.IsHom ml' f) : ml.Block ↪o ml'.Block :=
  OrderEmbedding.ofStrictMono
    (Quotient.lift (fun x ↦ ml'.toBlock (f x)) fun _ _ h ↦
      toBlock_eq_toBlock.2 (hf.atMostMarginal_iff.2 (toBlock_eq_toBlock.1 (Quotient.sound h))))
    fun a b ↦ Quotient.inductionOn₂ a b fun _ _ h ↦
      toBlock_lt_toBlock.2 (hf.largelyLT_iff.2 (toBlock_lt_toBlock.1 h))

@[simp]
theorem IsHom.mapBlock_toBlock (hf : ml.IsHom ml' f) (x : α) :
    hf.mapBlock (ml.toBlock x) = ml'.toBlock (f x) :=
  rfl

variable (ml) in
@[simp]
theorem IsHom.mapBlock_id : (IsHom.id ml).mapBlock = RelEmbedding.refl _ :=
  DFunLike.ext _ _ <| Block.ind fun _ ↦ rfl

theorem IsHom.mapBlock_comp (hg : ml'.IsHom ml'' g) (hf : ml.IsHom ml' f) :
    (hg.comp hf).mapBlock = hf.mapBlock.trans hg.mapBlock :=
  DFunLike.ext _ _ <| Block.ind fun _ ↦ rfl

end IsHom

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
    (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y :=
  lex_atMostMarginal_iff.symm.trans hf.atMostMarginal_iff

end Lex

end MarginalScale
