module

public import Linglib.Logic.Bilattice.Defs
public import Linglib.Core.Order.InvolutiveCompl
public import Mathlib.Order.Hom.Basic

/-!
# Negation and conflation

A bilattice has two orders, and so two ways to turn a value over. A **negation** reverses the truth
order and leaves the knowledge order alone: it exchanges true and false and keeps what is known. A
**conflation**, written `−`, does the opposite: it reverses the knowledge order and leaves the truth
order alone. Each undoes itself. Conflation sorts the values. A value is **consistent** when it is
at or below its conflation in the knowledge order, **anticonsistent** when it is at or above it, and
**exact** when the two coincide. These are, in the abstract, the values of Kleene's logic, of
Priest's, and of classical logic. Each class is closed under the truth operations, and [every
consistent value lies below an exact one](##IsConsistent.kLE_sup_conf).

## Implementation notes

Both are mixins over `InvolutiveCompl`, which supplies each order's De Morgan laws; a conflation is
an involutive complement on the synonym `Know B`. In symbols, `a` is consistent when `a ≤ₖ −a`,
anticonsistent when `−a ≤ₖ a` and exact when `−a = a`.

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
-/

@[expose] public section

universe u

variable {B : Type u}

namespace Bilattice

/-!
### Negation

A negation undoes itself, reverses the truth order and preserves the knowledge order. It therefore
exchanges the truth meet and join, as in the De Morgan laws, and commutes with the knowledge meet
and join.
-/

section Negation

/-- A **negation** on a bilattice is an operation that undoes itself, reverses the truth order and
preserves the knowledge order ([avron-1996] Def 2.3). -/
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

/-- Negation maps the knowledge order isomorphically onto itself. -/
def Negation.knowIso : Know B ≃o Know B where
  toFun X := toKnow (ofKnow X)ᶜ
  invFun X := toKnow (ofKnow X)ᶜ
  left_inv _ := congrArg toKnow (InvolutiveCompl.compl_compl _)
  right_inv _ := congrArg toKnow (InvolutiveCompl.compl_compl _)
  map_rel_iff' := compl_kLE_compl_iff

end LE

section Lattice

variable [Lattice (Know B)] [Negation B]

/-- The negation of a knowledge meet is the knowledge meet of the negations (note following
[avron-1996] Def 2.3). -/
theorem compl_kInf (a b : B) : (a ⊓ₖ b)ᶜ = aᶜ ⊓ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_inf (toKnow a) (toKnow b))

/-- The negation of a knowledge join is the knowledge join of the negations (note following
[avron-1996] Def 2.3). -/
theorem compl_kSup (a b : B) : (a ⊔ₖ b)ᶜ = aᶜ ⊔ₖ bᶜ :=
  toKnow.injective (Negation.knowIso.map_sup (toKnow a) (toKnow b))

end Lattice

section Bounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [Negation B]

/-- Negation leaves fixed the top of the knowledge order, the value with all the information (note
following [avron-1996] Def 2.3). -/
@[simp] theorem compl_ofKnow_top : (ofKnow (⊤ : Know B))ᶜ = ofKnow ⊤ :=
  congrArg ofKnow Negation.knowIso.map_top

/-- Negation leaves fixed the bottom of the knowledge order, the value with no information (note
following [avron-1996] Def 2.3). -/
@[simp] theorem compl_ofKnow_bot : (ofKnow (⊥ : Know B))ᶜ = ofKnow ⊥ :=
  congrArg ofKnow Negation.knowIso.map_bot

end Bounds

end Negation

/-!
### Conflation

A conflation is a negation with the two orders exchanged: it undoes itself, reverses the knowledge
order and preserves the truth order. Its laws are those of negation, read in the bilattice with
truth and knowledge exchanged.
-/

section Conflation

/-- The **conflation** of a value, written `−a`, is its complement in the knowledge order
([fitting-2021] §8.4). When that complement undoes itself and reverses the knowledge order, so does
conflation (Con-3, Con-1). -/
def conf [Compl (Know B)] (a : B) : B := ofKnow (toKnow a)ᶜ

@[simp] theorem toKnow_conf [Compl (Know B)] (a : B) : toKnow (conf a) = (toKnow a)ᶜ := rfl

/-- A **conflation** on a bilattice is a complement of the knowledge order that also preserves the
truth order (Con-2). It is a negation of the bilattice with the two orders exchanged ([fitting-2021]
§8.4). -/
class Conflation (B : Type u) [LE B] [Compl (Know B)] : Prop extends Negation (Know B)

/-- Negation and conflation **commute** when negating the conflation of a value gives the conflation
of its negation (Con-4). -/
class NegConfComm (B : Type u) [Compl B] [Compl (Know B)] : Prop where
  compl_conf : ∀ a : B, (conf a)ᶜ = conf aᶜ

export NegConfComm (compl_conf)

/-!
#### The knowledge order

Since conflation reverses the knowledge order, it exchanges the knowledge meet and join and the two
knowledge bounds.
-/

@[simp] theorem conf_conf [LE (Know B)] [InvolutiveCompl (Know B)] (a : B) : conf (conf a) = a :=
  InvolutiveCompl.compl_compl (toKnow a)

/-- Conflation reverses the knowledge order (Con-1). -/
theorem conf_kLE_conf [LE (Know B)] [InvolutiveCompl (Know B)] {a b : B} (h : a ≤ₖ b) :
    conf b ≤ₖ conf a :=
  InvolutiveCompl.compl_le_compl h

section KnowLattice

variable [Lattice (Know B)] [InvolutiveCompl (Know B)]

/-- The conflation of a knowledge meet is the knowledge join of the conflations ([fitting-2021]
§8.4, (CDeM-3)). -/
theorem conf_kInf (a b : B) : conf (a ⊓ₖ b) = conf a ⊔ₖ conf b :=
  congrArg ofKnow (InvolutiveCompl.compl_inf (toKnow a) (toKnow b))

/-- The conflation of a knowledge join is the knowledge meet of the conflations ([fitting-2021]
§8.4, (CDeM-4)). -/
theorem conf_kSup (a b : B) : conf (a ⊔ₖ b) = conf a ⊓ₖ conf b :=
  congrArg ofKnow (InvolutiveCompl.compl_sup (toKnow a) (toKnow b))

end KnowLattice

section KnowBounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [InvolutiveCompl (Know B)]

/-- Conflation sends the top of the knowledge order to its bottom. -/
@[simp] theorem conf_ofKnow_top : conf (ofKnow (⊤ : Know B)) = ofKnow ⊥ :=
  congrArg ofKnow InvolutiveCompl.compl_top

@[simp] theorem conf_ofKnow_bot : conf (ofKnow (⊥ : Know B)) = ofKnow ⊤ :=
  congrArg ofKnow InvolutiveCompl.compl_bot

end KnowBounds

/-!
#### The truth order, by duality

Since conflation preserves the truth order, it commutes with the truth meet and join and leaves true
and false fixed. Each of these facts is a fact about negation, read in the bilattice with the two
orders exchanged.
-/

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

/-- The conflation of a truth meet is the truth meet of the conflations ([fitting-2021] §8.4,
(CDeM-1)). -/
theorem conf_inf (a b : B) : conf (a ⊓ b) = conf a ⊓ conf b :=
  congrArg ofKnow (compl_kInf (B := Know B) (toKnow a) (toKnow b))

/-- The conflation of a truth join is the truth join of the conflations ([fitting-2021] §8.4,
(CDeM-2)). -/
theorem conf_sup (a b : B) : conf (a ⊔ b) = conf a ⊔ conf b :=
  congrArg ofKnow (compl_kSup (B := Know B) (toKnow a) (toKnow b))

end TruthLattice

section TruthBounds

variable [PartialOrder B] [BoundedOrder B] [LE (Know B)] [InvolutiveCompl (Know B)]
  [Conflation B]

/-- Conflation leaves true, the top of the truth order, fixed. -/
@[simp] theorem conf_top : conf (⊤ : B) = ⊤ := congrArg ofKnow (compl_ofKnow_top (B := Know B))

@[simp] theorem conf_bot : conf (⊥ : B) = ⊥ := congrArg ofKnow (compl_ofKnow_bot (B := Know B))

end TruthBounds

/-!
#### The consistent, anticonsistent and exact values

Conflation compares a value with its mirror image in the knowledge order. A consistent value says no
more than its conflation, an anticonsistent one no less, and an exact one is left fixed. Among pairs
of sets of worlds, the consistent pairs are those whose two sets do not overlap, and the exact ones
those that also leave no world out.
-/

section Classes

variable [LE (Know B)] [Compl (Know B)]

/-- A value is **consistent** when it is at or below its conflation in the knowledge order
([fitting-2021] Def 8.5.1). The consistent values are the abstract form of the values of Kleene's
logic. -/
def IsConsistent (a : B) : Prop := a ≤ₖ conf a

/-- A value is **anticonsistent** when its conflation is at or below it in the knowledge order
([fitting-2021] Def 8.5.1). The anticonsistent values are the abstract form of the values of
Priest's LP. -/
def IsAnticonsistent (a : B) : Prop := conf a ≤ₖ a

/-- A value is **exact** when conflation leaves it fixed ([fitting-2021] Def 8.5.1). The exact
values are the abstract form of the classical truth values. -/
abbrev IsExact (a : B) : Prop := Function.IsFixedPt conf a

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsConsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (a ≤ₖ conf a))

instance [DecidableRel (kLE (B := B))] : DecidablePred (IsAnticonsistent (B := B)) :=
  fun a ↦ inferInstanceAs (Decidable (conf a ≤ₖ a))

end Classes

/-! The following facts use the knowledge order alone. -/

theorem IsExact.isConsistent [Preorder (Know B)] [Compl (Know B)] {a : B} (h : IsExact a) :
    IsConsistent a := by
  rw [IsConsistent, h.eq]

theorem IsExact.isAnticonsistent [Preorder (Know B)] [Compl (Know B)] {a : B} (h : IsExact a) :
    IsAnticonsistent a := by
  rw [IsAnticonsistent, h.eq]

/-- Every value at or below a consistent value in the knowledge order is consistent. -/
theorem IsConsistent.anti [Preorder (Know B)] [InvolutiveCompl (Know B)] {a b : B}
    (hb : IsConsistent b) (h : a ≤ₖ b) : IsConsistent a :=
  kLE_trans (kLE_trans h hb) (conf_kLE_conf h)

/-- The knowledge meet of a consistent value with any value is consistent ([fitting-1994] Theorem
9.3). -/
theorem IsConsistent.kInf [Lattice (Know B)] [InvolutiveCompl (Know B)] {a : B}
    (ha : IsConsistent a) (b : B) : IsConsistent (a ⊓ₖ b) :=
  ha.anti (inf_le_left (α := Know B))

/-- Two exact values that are comparable in the knowledge order are equal ([fitting-2021] Prop
8.5.4). -/
theorem IsExact.eq_of_kLE [PartialOrder (Know B)] [InvolutiveCompl (Know B)] {a b : B}
    (ha : IsExact a) (hb : IsExact b) (h : a ≤ₖ b) : a = b :=
  kLE_antisymm h (by simpa only [ha.eq, hb.eq] using conf_kLE_conf h)

section KnowledgeBounds

variable [PartialOrder (Know B)] [BoundedOrder (Know B)] [InvolutiveCompl (Know B)]

/-- If the top and the bottom of the knowledge order differ, the top is not exact ([fitting-1994]
Theorem 9.2). -/
theorem not_isExact_ofKnow_top (h : (⊥ : Know B) ≠ ⊤) : ¬ IsExact (ofKnow (⊤ : Know B)) :=
  fun hx ↦ h (ofKnow.injective (conf_ofKnow_top.symm.trans hx.eq))

/-- If the top and the bottom of the knowledge order differ, the bottom is not exact ([fitting-1994]
Theorem 9.2). -/
theorem not_isExact_ofKnow_bot (h : (⊥ : Know B) ≠ ⊤) : ¬ IsExact (ofKnow (⊥ : Know B)) :=
  fun hx ↦ h (ofKnow.injective (hx.eq.symm.trans conf_ofKnow_bot))

end KnowledgeBounds

/-! The following facts also use the truth order. -/

section Exact

variable [Lattice B] [LE (Know B)] [InvolutiveCompl (Know B)] [Conflation B]

/-- The truth meet of two exact values is exact ([fitting-2021] Prop 8.5.2). -/
theorem IsExact.inf {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊓ b) :=
  (conf_inf a b).trans (by rw [ha.eq, hb.eq])

theorem IsExact.sup {a b : B} (ha : IsExact a) (hb : IsExact b) : IsExact (a ⊔ b) :=
  (conf_sup a b).trans (by rw [ha.eq, hb.eq])

/-- The truth join of any value with its conflation is exact. -/
theorem isExact_sup_conf (a : B) : IsExact (a ⊔ conf a) :=
  (conf_sup _ _).trans (by rw [conf_conf, sup_comm])

/-- The truth meet of any value with its conflation is exact. -/
theorem isExact_inf_conf (a : B) : IsExact (a ⊓ conf a) :=
  (conf_inf _ _).trans (by rw [conf_conf, inf_comm])

end Exact

section Interlaced

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] [InvolutiveCompl (Know B)]
  [Conflation B]

/-- In an interlaced bilattice the truth meet of two consistent values is consistent ([fitting-2021]
Prop 8.5.2). -/
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

/-- In an interlaced bilattice a consistent value lies at or below, in the knowledge order, the
truth join of itself with its conflation, which is exact ([fitting-2021] Prop 8.5.3). -/
theorem IsConsistent.kLE_sup_conf [Lattice B] [Lattice (Know B)] [IsInterlaced B]
    [Compl (Know B)] {a : B} (ha : IsConsistent a) : a ≤ₖ a ⊔ conf a := by
  simpa only [sup_idem] using sup_kLE_sup (kLE_refl a) ha

/-- In an interlaced bilattice an anticonsistent value lies at or above, in the knowledge order, the
truth meet of itself with its conflation, which is exact ([fitting-2021] Prop 8.5.3). -/
theorem IsAnticonsistent.inf_conf_kLE [Lattice B] [Lattice (Know B)] [IsInterlaced B]
    [Compl (Know B)] {a : B} (ha : IsAnticonsistent a) : a ⊓ conf a ≤ₖ a := by
  simpa only [inf_idem] using inf_kLE_inf (kLE_refl a) ha

section ClassesCompl

variable [Compl B] [Compl (Know B)] [NegConfComm B]

/-- When negation and conflation commute, the negation of an exact value is exact ([fitting-2021]
Prop 8.5.2). -/
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
