module

public import Linglib.Core.Order.Bilattice.Defs
public import Linglib.Core.Order.InvolutiveCompl
public import Mathlib.Order.Hom.Basic

/-!
# Negation and conflation

A negation on a bilattice ([avron-1996] Def 2.3) is an involution that reverses the truth order
and preserves the knowledge order. Its first two conditions are an `InvolutiveCompl` on the
truth order, which already supplies the De Morgan laws and the exchange of the truth bounds;
`Negation` adds the third. A conflation ([fitting-2021] §8.4) is an
involution that preserves the truth order and reverses the knowledge order. It splits the
carrier into consistent values `a ≤ₖ −a`, anticonsistent values `−a ≤ₖ a` and exact values
`−a = a`, the abstract forms of the value spaces of Kleene's, Priest's and classical logic
([fitting-2021] Def 8.5.1). The three classes are closed under the truth operations and, when
negation and conflation commute, under negation.

## Main definitions

* `Bilattice.Negation`: the truth-lattice involution preserves the knowledge order.
* `Bilattice.Conflation`: the knowledge-reversing involution `conf`.
* `Bilattice.NegConfComm`: negation and conflation commute.
* `Bilattice.IsConsistent`, `Bilattice.IsAnticonsistent`, `Bilattice.IsExact`: the three classes;
  the exact values are the fixed points of `conf`.

## Main results

* `Bilattice.compl_kInf`, `Bilattice.compl_kSup`: negation commutes with the knowledge
  operations.
* `Bilattice.IsConsistent.inf` and its kin: the closure laws ([fitting-2021] Prop 8.5.2), and
  `Bilattice.IsConsistent.kInf`: consistency survives knowledge meets.
* `Bilattice.IsConsistent.exists_exact_kLE`, `Bilattice.IsExact.eq_of_kLE`: interpolation and
  the antichain law ([fitting-2021] Props 8.5.3 and 8.5.4).

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
class Negation (B : Type u) [Compl B] [Preorder (Know B)] : Prop where
  /-- Negation preserves the knowledge order ([avron-1996] Def 2.3(iii)). -/
  compl_kLE_compl : ∀ {a b : B}, a ≤ₖ b → aᶜ ≤ₖ bᶜ

export Negation (compl_kLE_compl)

variable [LE B] [InvolutiveCompl B]

section Preorder

variable [Preorder (Know B)] [Negation B]

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

end Preorder

variable [Lattice (Know B)] [Negation B]

/-- Negation commutes with the knowledge meet, `(a ⊓ₖ b)ᶜ = aᶜ ⊓ₖ bᶜ` (note following
[avron-1996] Def 2.3). -/
theorem compl_kInf (a b : B) : (a ⊓ₖ b)ᶜ = aᶜ ⊓ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_inf (toKnow a) (toKnow b))

/-- Negation commutes with the knowledge join, `(a ⊔ₖ b)ᶜ = aᶜ ⊔ₖ bᶜ` (note following
[avron-1996] Def 2.3). -/
theorem compl_kSup (a b : B) : (a ⊔ₖ b)ᶜ = aᶜ ⊔ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_sup (toKnow a) (toKnow b))

end Negation

/-! ### Conflation

The knowledge-order counterpart of negation, [fitting-1994]'s coinage with the axioms of
[fitting-2021]. -/

section Conflation

section Defs

variable [Preorder B] [Preorder (Know B)]

/-- A **conflation** ([fitting-2021] §8.4): an involution (Con-3) that
preserves the truth order (Con-2) and reverses the knowledge order (Con-1). -/
class Conflation (B : Type u) [Preorder B] [Preorder (Know B)] : Type u where
  /-- The conflation operation `−`. -/
  conf : B → B
  /-- Conflation is an involution (Con-3). -/
  conf_conf : ∀ a : B, conf (conf a) = a
  /-- Conflation preserves the truth order (Con-2). -/
  conf_le_conf : ∀ {a b : B}, a ≤ b → conf a ≤ conf b
  /-- Conflation reverses the knowledge order (Con-1). -/
  conf_kLE_conf : ∀ {a b : B}, a ≤ₖ b → conf b ≤ₖ conf a

export Conflation (conf conf_conf conf_le_conf conf_kLE_conf)

attribute [simp] Conflation.conf_conf

/-- Negation and conflation commute (Con-4). -/
class NegConfComm (B : Type u) [Preorder B] [Compl B] [Preorder (Know B)] [Conflation B] :
    Prop where
  compl_conf : ∀ a : B, (conf a)ᶜ = conf aᶜ

export NegConfComm (compl_conf)

variable [Conflation B]

theorem conf_le_conf_iff {a b : B} : conf a ≤ conf b ↔ a ≤ b :=
  ⟨fun h ↦ by simpa only [conf_conf] using conf_le_conf h, conf_le_conf⟩

theorem conf_kLE_conf_iff {a b : B} : conf b ≤ₖ conf a ↔ a ≤ₖ b :=
  ⟨fun h ↦ by simpa only [conf_conf] using conf_kLE_conf h, conf_kLE_conf⟩

/-- Conflation as an automorphism of the truth order. -/
def Conflation.orderIso : B ≃o B where
  toFun := conf
  invFun := conf
  left_inv := conf_conf
  right_inv := conf_conf
  map_rel_iff' := conf_le_conf_iff

end Defs

section Bounds

variable [PartialOrder B] [Preorder (Know B)] [BoundedOrder B] [Conflation B]

@[simp] theorem conf_top : conf (⊤ : B) = ⊤ := Conflation.orderIso.map_top

@[simp] theorem conf_bot : conf (⊥ : B) = ⊥ := Conflation.orderIso.map_bot

end Bounds

section DeMorgan

variable [Lattice B] [Preorder (Know B)] [Conflation B]

theorem conf_inf (a b : B) : conf (a ⊓ b) = conf a ⊓ conf b :=
  Conflation.orderIso.map_inf a b

theorem conf_sup (a b : B) : conf (a ⊔ b) = conf a ⊔ conf b :=
  Conflation.orderIso.map_sup a b

end DeMorgan

/-! #### The consistent / anticonsistent / exact classes -/

section Classes

variable [Preorder B] [Preorder (Know B)] [Conflation B]

/-- Consistent values, `a ≤ₖ −a` ([fitting-2021] Def 8.5.1): the abstract form
of the Kleene value space. -/
def IsConsistent (a : B) : Prop := a ≤ₖ conf a

/-- Anticonsistent values, `−a ≤ₖ a` ([fitting-2021] Def 8.5.1): the abstract
form of Priest's LP value space. -/
def IsAnticonsistent (a : B) : Prop := conf a ≤ₖ a

/-- Exact values, `−a = a` ([fitting-2021] Def 8.5.1): the abstract classical
value space, the fixed points of conflation. -/
abbrev IsExact (a : B) : Prop := Function.IsFixedPt conf a

theorem IsExact.isConsistent {a : B} (h : IsExact a) : IsConsistent a := by
  rw [IsConsistent, h.eq]

theorem IsExact.isAnticonsistent {a : B} (h : IsExact a) : IsAnticonsistent a := by
  rw [IsAnticonsistent, h.eq]

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsConsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (a ≤ₖ conf a))

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsAnticonsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (conf a ≤ₖ a))

end Classes

section ClassesClosure

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [Conflation B]

/-- The consistent values are closed under truth meet
([fitting-2021] Prop 8.5.2). -/
theorem IsConsistent.inf {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊓ b) := by
  rw [IsConsistent, conf_inf]
  calc a ⊓ b ≤ₖ conf a ⊓ b := IsInterlaced.inf_kmono ha b
    _ = b ⊓ conf a := inf_comm ..
    _ ≤ₖ conf b ⊓ conf a := IsInterlaced.inf_kmono hb (conf a)
    _ = conf a ⊓ conf b := inf_comm ..

theorem IsConsistent.sup {a b : B} (ha : IsConsistent a) (hb : IsConsistent b) :
    IsConsistent (a ⊔ b) := by
  rw [IsConsistent, conf_sup]
  calc a ⊔ b ≤ₖ conf a ⊔ b := IsInterlaced.sup_kmono ha b
    _ = b ⊔ conf a := sup_comm ..
    _ ≤ₖ conf b ⊔ conf a := IsInterlaced.sup_kmono hb (conf a)
    _ = conf a ⊔ conf b := sup_comm ..

/-- The anticonsistent values are closed under truth meet. -/
theorem IsAnticonsistent.inf {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊓ b) := by
  rw [IsAnticonsistent, conf_inf]
  calc conf a ⊓ conf b ≤ₖ a ⊓ conf b := IsInterlaced.inf_kmono ha (conf b)
    _ = conf b ⊓ a := inf_comm ..
    _ ≤ₖ b ⊓ a := IsInterlaced.inf_kmono hb a
    _ = a ⊓ b := inf_comm ..

theorem IsAnticonsistent.sup {a b : B} (ha : IsAnticonsistent a)
    (hb : IsAnticonsistent b) : IsAnticonsistent (a ⊔ b) := by
  rw [IsAnticonsistent, conf_sup]
  calc conf a ⊔ conf b ≤ₖ a ⊔ conf b := IsInterlaced.sup_kmono ha (conf b)
    _ = conf b ⊔ a := sup_comm ..
    _ ≤ₖ b ⊔ a := IsInterlaced.sup_kmono hb a
    _ = a ⊔ b := sup_comm ..

omit [IsInterlaced B] in
/-- The exact values are closed under truth meet. -/
theorem IsExact.inf {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊓ b) :=
  (conf_inf a b).trans (by rw [ha.eq, hb.eq])

omit [IsInterlaced B] in
theorem IsExact.sup {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊔ b) :=
  (conf_sup a b).trans (by rw [ha.eq, hb.eq])

end ClassesClosure

section ClassesCompl

variable [Preorder B] [Compl B] [Preorder (Know B)] [Negation B] [Conflation B]
  [NegConfComm B]

theorem IsConsistent.compl {a : B} (ha : IsConsistent a) : IsConsistent aᶜ := by
  rw [IsConsistent, ← compl_conf]
  exact compl_kLE_compl ha

theorem IsAnticonsistent.compl {a : B} (ha : IsAnticonsistent a) : IsAnticonsistent aᶜ := by
  rw [IsAnticonsistent, ← compl_conf]
  exact compl_kLE_compl ha

omit [Negation B] in
theorem IsExact.compl {a : B} (ha : IsExact a) : IsExact aᶜ :=
  (compl_conf a).symm.trans (congrArg _ ha.eq)

end ClassesCompl

section KnowledgeMeet

variable [Preorder B] [Lattice (Know B)] [Conflation B]

/-- The consensus of a consistent value with any value is consistent ([fitting-1994]
Theorem 9.3, there for products). -/
theorem IsConsistent.kInf {a : B} (ha : IsConsistent a) (b : B) : IsConsistent (a ⊓ₖ b) :=
  have h : a ⊓ₖ b ≤ₖ a := (inf_le_left : toKnow a ⊓ toKnow b ≤ toKnow a)
  kLE_trans (kLE_trans h ha) (conf_kLE_conf h)

end KnowledgeMeet

section Interpolation

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [Conflation B]

/-- Every consistent value is knowledge-below an exact value
([fitting-2021] Prop 8.5.3): `a ⊔ −a` is exact. -/
theorem IsConsistent.exists_exact_kLE {a : B} (ha : IsConsistent a) :
    ∃ b : B, IsExact b ∧ a ≤ₖ b := by
  refine ⟨a ⊔ conf a, (conf_sup _ _).trans (by rw [conf_conf, sup_comm]), ?_⟩
  calc a ≤ₖ conf a ⊔ a := by
        simpa only [sup_idem] using IsInterlaced.sup_kmono ha a
    _ = a ⊔ conf a := sup_comm ..

/-- Every anticonsistent value is knowledge-above an exact value
([fitting-2021] Prop 8.5.3): `a ⊓ −a` is exact. -/
theorem IsAnticonsistent.exists_exact_kLE {a : B} (ha : IsAnticonsistent a) :
    ∃ b : B, IsExact b ∧ b ≤ₖ a := by
  refine ⟨a ⊓ conf a, (conf_inf _ _).trans (by rw [conf_conf, inf_comm]), ?_⟩
  calc a ⊓ conf a = conf a ⊓ a := inf_comm ..
    _ ≤ₖ a := by simpa only [inf_idem] using IsInterlaced.inf_kmono ha a

end Interpolation

section ExactAntichain

variable [Preorder B] [PartialOrder (Know B)] [Conflation B]

/-- The exact values form a knowledge-order antichain
([fitting-2021] Prop 8.5.4). -/
theorem IsExact.eq_of_kLE {a b : B} (ha : IsExact a) (hb : IsExact b)
    (h : a ≤ₖ b) : a = b :=
  kLE_antisymm h (by
    have h' := conf_kLE_conf h
    rwa [ha.eq, hb.eq] at h')

end ExactAntichain

end Conflation

end Bilattice
