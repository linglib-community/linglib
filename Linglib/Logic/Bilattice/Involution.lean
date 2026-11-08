module

public import Linglib.Logic.Bilattice.Defs
public import Linglib.Core.Order.InvolutiveCompl
public import Mathlib.Order.Hom.Basic

/-!
# Negation and conflation

This file defines negation and conflation on a bilattice. A negation is an involutive complement
of the truth order that preserves the knowledge order; a conflation `−` is an involutive complement
of the knowledge order, on the synonym `Know B`, that preserves the truth order. Both are mixins
over `InvolutiveCompl`, which supplies each order's De Morgan laws. A value `a` is consistent when
`a ≤ₖ −a`, anticonsistent when `−a ≤ₖ a` and exact when `−a = a`, abstracting the value spaces of
Kleene's, Priest's and classical logic; each class is closed under the truth operations, and
[every consistent value lies below an exact one](##IsConsistent.kLE_sup_conf).

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
-/

@[expose] public section

universe u

variable {B : Type u}

namespace Bilattice

/-! ### Negation -/

section Negation

/-- A negation ([avron-1996] Def 2.3): the complement `ᶜ`, involutive (i) and reversing the truth
order (ii) by `InvolutiveCompl`, also preserves the knowledge order (iii). -/
class Negation (B : Type u) [Compl B] [LE (Know B)] : Prop where
  /-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
  compl_kLE_compl : ∀ {a b : B}, a ≤ₖ b → aᶜ ≤ₖ bᶜ

export Negation (compl_kLE_compl)

variable [LE B] [InvolutiveCompl B]

section LE

variable [LE (Know B)] [Negation B]

theorem compl_kLE_compl_iff {a b : B} : aᶜ ≤ₖ bᶜ ↔ a ≤ₖ b :=
  ⟨fun h ↦ by simpa only [InvolutiveCompl.compl_compl] using compl_kLE_compl h,
    compl_kLE_compl⟩

/-- Negation as an automorphism of the knowledge order. -/
def Negation.knowIso : Know B ≃o Know B where
  toFun X := toKnow (ofKnow X)ᶜ
  invFun X := toKnow (ofKnow X)ᶜ
  left_inv _ := congrArg toKnow (InvolutiveCompl.compl_compl _)
  right_inv _ := congrArg toKnow (InvolutiveCompl.compl_compl _)
  map_rel_iff' := compl_kLE_compl_iff

end LE

section Lattice

variable [Lattice (Know B)] [Negation B]

/-- Negation commutes with the knowledge meet, `(a ⊓ₖ b)ᶜ = aᶜ ⊓ₖ bᶜ` (note following
[avron-1996] Def 2.3). -/
theorem compl_kInf (a b : B) : (a ⊓ₖ b)ᶜ = aᶜ ⊓ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_inf (toKnow a) (toKnow b))

/-- Negation commutes with the knowledge join, `(a ⊔ₖ b)ᶜ = aᶜ ⊔ₖ bᶜ` (note following
[avron-1996] Def 2.3). -/
theorem compl_kSup (a b : B) : (a ⊔ₖ b)ᶜ = aᶜ ⊔ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_sup (toKnow a) (toKnow b))

end Lattice

section Bounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [Negation B]

/-- Negation fixes the knowledge bounds, `∼⊤ = ⊤` (note following [avron-1996] Def 2.3). -/
@[simp] theorem compl_ofKnow_top : (ofKnow (⊤ : Know B))ᶜ = ofKnow ⊤ :=
  congrArg ofKnow Negation.knowIso.map_top

/-- `∼⊥ = ⊥` (note following [avron-1996] Def 2.3). -/
@[simp] theorem compl_ofKnow_bot : (ofKnow (⊥ : Know B))ᶜ = ofKnow ⊥ :=
  congrArg ofKnow Negation.knowIso.map_bot

end Bounds

end Negation

/-! ### Conflation

A conflation is the negation of the dual bilattice `Know B`: an involutive complement of the
knowledge order that preserves the truth order. Its laws for the knowledge order are those of
`InvolutiveCompl (Know B)`, and its laws for the truth order are the negation laws read on
`Know B`. -/

section Conflation

/-- Conflation `−a` ([fitting-2021] §8.4): the complement of the knowledge order, read on `B`. An
`InvolutiveCompl (Know B)` makes it an involution (Con-3) reversing the knowledge order (Con-1). -/
def conf [Compl (Know B)] (a : B) : B := ofKnow (toKnow a)ᶜ

@[simp] theorem toKnow_conf [Compl (Know B)] (a : B) : toKnow (conf a) = (toKnow a)ᶜ := rfl

/-- A conflation ([fitting-2021] §8.4) is a negation of the dual bilattice `Know B`: the involutive
complement `conf` of the knowledge order also preserves the truth order (Con-2). -/
class Conflation (B : Type u) [LE B] [Compl (Know B)] : Prop extends Negation (Know B)

/-- Negation and conflation commute (Con-4). -/
class NegConfComm (B : Type u) [Compl B] [Compl (Know B)] : Prop where
  compl_conf : ∀ a : B, (conf a)ᶜ = conf aᶜ

export NegConfComm (compl_conf)

/-! #### The knowledge order -/

@[simp] theorem conf_conf [LE (Know B)] [InvolutiveCompl (Know B)] (a : B) : conf (conf a) = a :=
  InvolutiveCompl.compl_compl (toKnow a)

/-- Conflation reverses the knowledge order (Con-1). -/
theorem conf_kLE_conf [LE (Know B)] [InvolutiveCompl (Know B)] {a b : B} (h : a ≤ₖ b) :
    conf b ≤ₖ conf a :=
  InvolutiveCompl.compl_le_compl h

section KnowLattice

variable [Lattice (Know B)] [InvolutiveCompl (Know B)]

/-- Conflation exchanges the knowledge meet and join, `−(a ⊗ b) = −a ⊕ −b` ([fitting-2021] §8.4,
(CDeM-3)). -/
theorem conf_kInf (a b : B) : conf (a ⊓ₖ b) = conf a ⊔ₖ conf b :=
  congrArg ofKnow (InvolutiveCompl.compl_inf (toKnow a) (toKnow b))

/-- `−(a ⊕ b) = −a ⊗ −b` ([fitting-2021] §8.4, (CDeM-4)). -/
theorem conf_kSup (a b : B) : conf (a ⊔ₖ b) = conf a ⊓ₖ conf b :=
  congrArg ofKnow (InvolutiveCompl.compl_sup (toKnow a) (toKnow b))

end KnowLattice

section KnowBounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [InvolutiveCompl (Know B)]

/-- Conflation exchanges the knowledge bounds. -/
@[simp] theorem conf_ofKnow_top : conf (ofKnow (⊤ : Know B)) = ofKnow ⊥ :=
  congrArg ofKnow InvolutiveCompl.compl_top

@[simp] theorem conf_ofKnow_bot : conf (ofKnow (⊥ : Know B)) = ofKnow ⊤ :=
  congrArg ofKnow InvolutiveCompl.compl_bot

end KnowBounds

/-! #### The truth order, by duality -/

section Truth

variable [LE B] [LE (Know B)] [InvolutiveCompl (Know B)] [Conflation B]

/-- Conflation preserves the truth order (Con-2). -/
theorem conf_le_conf {a b : B} (h : a ≤ b) : conf a ≤ conf b :=
  compl_kLE_compl (B := Know B) (a := toKnow a) (b := toKnow b) h

theorem conf_le_conf_iff {a b : B} : conf a ≤ conf b ↔ a ≤ b :=
  compl_kLE_compl_iff (B := Know B) (a := toKnow a) (b := toKnow b)

end Truth

section TruthLattice

variable [Lattice B] [LE (Know B)] [InvolutiveCompl (Know B)] [Conflation B]

/-- `−(a ∧ b) = −a ∧ −b` ([fitting-2021] §8.4, (CDeM-1)), the dual of `compl_kInf`. -/
theorem conf_inf (a b : B) : conf (a ⊓ b) = conf a ⊓ conf b :=
  congrArg ofKnow (compl_kInf (B := Know B) (toKnow a) (toKnow b))

/-- `−(a ∨ b) = −a ∨ −b` ([fitting-2021] §8.4, (CDeM-2)), the dual of `compl_kSup`. -/
theorem conf_sup (a b : B) : conf (a ⊔ b) = conf a ⊔ conf b :=
  congrArg ofKnow (compl_kSup (B := Know B) (toKnow a) (toKnow b))

end TruthLattice

section TruthBounds

variable [PartialOrder B] [BoundedOrder B] [LE (Know B)] [InvolutiveCompl (Know B)]
  [Conflation B]

/-- Conflation fixes the truth bounds, the dual of `compl_ofKnow_top`. -/
@[simp] theorem conf_top : conf (⊤ : B) = ⊤ := congrArg ofKnow (compl_ofKnow_top (B := Know B))

@[simp] theorem conf_bot : conf (⊥ : B) = ⊥ := congrArg ofKnow (compl_ofKnow_bot (B := Know B))

end TruthBounds

/-! #### The consistent, anticonsistent and exact values -/

section Classes

variable [LE (Know B)] [Compl (Know B)]

/-- Consistent values, `a ≤ₖ −a` ([fitting-2021] Def 8.5.1): the abstract form
of the Kleene value space. -/
def IsConsistent (a : B) : Prop := a ≤ₖ conf a

/-- Anticonsistent values, `−a ≤ₖ a` ([fitting-2021] Def 8.5.1): the abstract
form of Priest's LP value space. -/
def IsAnticonsistent (a : B) : Prop := conf a ≤ₖ a

/-- Exact values, `−a = a` ([fitting-2021] Def 8.5.1): the abstract classical
value space, the fixed points of conflation. -/
abbrev IsExact (a : B) : Prop := Function.IsFixedPt conf a

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsConsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (a ≤ₖ conf a))

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsAnticonsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (conf a ≤ₖ a))

end Classes

/-! The facts that read only the knowledge order. -/

theorem IsExact.isConsistent [Preorder (Know B)] [Compl (Know B)] {a : B} (h : IsExact a) :
    IsConsistent a := by
  rw [IsConsistent, h.eq]

theorem IsExact.isAnticonsistent [Preorder (Know B)] [Compl (Know B)] {a : B} (h : IsExact a) :
    IsAnticonsistent a := by
  rw [IsAnticonsistent, h.eq]

/-- The consistent values form a lower set of the knowledge order. -/
theorem IsConsistent.anti [Preorder (Know B)] [InvolutiveCompl (Know B)] {a b : B}
    (hb : IsConsistent b) (h : a ≤ₖ b) : IsConsistent a :=
  kLE_trans (kLE_trans h hb) (conf_kLE_conf h)

/-- The consensus of a consistent value with any value is consistent ([fitting-1994]
Theorem 9.3). -/
theorem IsConsistent.kInf [Lattice (Know B)] [InvolutiveCompl (Know B)] {a : B}
    (ha : IsConsistent a) (b : B) : IsConsistent (a ⊓ₖ b) :=
  ha.anti (inf_le_left (α := Know B))

/-- The exact values form a knowledge-order antichain ([fitting-2021] Prop 8.5.4). -/
theorem IsExact.eq_of_kLE [PartialOrder (Know B)] [InvolutiveCompl (Know B)] {a b : B}
    (ha : IsExact a) (hb : IsExact b) (h : a ≤ₖ b) : a = b :=
  kLE_antisymm h (by simpa only [ha.eq, hb.eq] using conf_kLE_conf h)

section KnowledgeBounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [InvolutiveCompl (Know B)]

/-- Over a nontrivial knowledge order the knowledge top is not exact ([fitting-1994]
Theorem 9.2). -/
theorem not_isExact_ofKnow_top (h : (⊥ : Know B) ≠ ⊤) : ¬ IsExact (ofKnow (⊤ : Know B)) :=
  fun hx ↦ h (ofKnow.injective (conf_ofKnow_top.symm.trans hx.eq))

/-- Over a nontrivial knowledge order the knowledge bottom is not exact ([fitting-1994]
Theorem 9.2). -/
theorem not_isExact_ofKnow_bot (h : (⊥ : Know B) ≠ ⊤) : ¬ IsExact (ofKnow (⊥ : Know B)) :=
  fun hx ↦ h (ofKnow.injective (hx.eq.symm.trans conf_ofKnow_bot))

end KnowledgeBounds

/-! The facts that read the truth order. -/

section Exact

variable [Lattice B] [LE (Know B)] [InvolutiveCompl (Know B)] [Conflation B]

/-- The exact values are closed under truth meet ([fitting-2021] Prop 8.5.2). -/
theorem IsExact.inf {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊓ b) :=
  (conf_inf a b).trans (by rw [ha.eq, hb.eq])

theorem IsExact.sup {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊔ b) :=
  (conf_sup a b).trans (by rw [ha.eq, hb.eq])

/-- `a ∨ −a` is exact, for every value `a`. -/
theorem isExact_sup_conf (a : B) : IsExact (a ⊔ conf a) :=
  (conf_sup _ _).trans (by rw [conf_conf, sup_comm])

/-- `a ∧ −a` is exact, for every value `a`. -/
theorem isExact_inf_conf (a : B) : IsExact (a ⊓ conf a) :=
  (conf_inf _ _).trans (by rw [conf_conf, inf_comm])

end Exact

section Interlaced

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [InvolutiveCompl (Know B)]
  [Conflation B]

/-- The consistent values are closed under truth meet ([fitting-2021] Prop 8.5.2). -/
theorem IsConsistent.inf {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊓ b) := by
  rw [IsConsistent, conf_inf]
  exact inf_kLE_inf ha hb

theorem IsConsistent.sup {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊔ b) := by
  rw [IsConsistent, conf_sup]
  exact sup_kLE_sup ha hb

theorem IsAnticonsistent.inf {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊓ b) := by
  rw [IsAnticonsistent, conf_inf]
  exact inf_kLE_inf ha hb

theorem IsAnticonsistent.sup {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊔ b) := by
  rw [IsAnticonsistent, conf_sup]
  exact sup_kLE_sup ha hb

end Interlaced

/-- A consistent value lies knowledge-below the exact value `a ∨ −a` ([fitting-2021]
Prop 8.5.3). -/
theorem IsConsistent.kLE_sup_conf [Lattice B] [Lattice (Know B)] [IsInterlaced B]
    [Compl (Know B)] {a : B} (ha : IsConsistent a) : a ≤ₖ a ⊔ conf a := by
  simpa only [sup_idem] using sup_kLE_sup (kLE_refl a) ha

/-- An anticonsistent value lies knowledge-above the exact value `a ∧ −a` ([fitting-2021]
Prop 8.5.3). -/
theorem IsAnticonsistent.inf_conf_kLE [Lattice B] [Lattice (Know B)] [IsInterlaced B]
    [Compl (Know B)] {a : B} (ha : IsAnticonsistent a) : a ⊓ conf a ≤ₖ a := by
  simpa only [inf_idem] using inf_kLE_inf (kLE_refl a) ha

section ClassesCompl

variable [Compl B] [Compl (Know B)] [NegConfComm B]

/-- The exact values are closed under negation ([fitting-2021] Prop 8.5.2). -/
theorem IsExact.compl {a : B} (ha : IsExact a) : IsExact aᶜ :=
  (compl_conf a).symm.trans (congrArg _ ha.eq)

variable [LE (Know B)] [Negation B]

theorem IsConsistent.compl {a : B} (ha : IsConsistent a) : IsConsistent aᶜ := by
  rw [IsConsistent, ← compl_conf]
  exact compl_kLE_compl ha

theorem IsAnticonsistent.compl {a : B} (ha : IsAnticonsistent a) : IsAnticonsistent aᶜ := by
  rw [IsAnticonsistent, ← compl_conf]
  exact compl_kLE_compl ha

end ClassesCompl

end Conflation

end Bilattice
