module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Basic.Sign.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Polarity

This file defines the polarity of an expression, positive or negative. The two polarities form the
group of order two, [the units of `ℤ`](##Polarity.unitsEquiv), and a homomorphism out of it is
[fixed by an element whose square is one](##Polarity.lift), so that the polarities act through any
involution. The polarity of a sentence acts on propositions by complement, and
[the orbit of a proposition](##Polarity.orbit_eq_pair_compl) is the pair of its polarity
alternatives, the focus value of a focused polarity and the answers of a polar question. The
polarity of an antonym acts on degrees by negation. A polarity
[directs a function](##Polarity.StrictMonoBy), and directions compose as polarities multiply.

## Implementation notes

A polarity coerces into `SignType`, whose third value records the absence of a direction, as for
a non-monotone context. The action on an additive group goes through `ℤˣ`, so that on a function
space it is pointwise by definition.

## References

* [wilder-2013]
* [gutzmann-2012]
-/

@[expose] public section

/-- The polarity of an expression, positive or negative. -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq, Inhabited, Fintype

namespace Polarity

instance : One Polarity where
  one := positive

/-- Polarities compose, two negations cancelling. -/
instance : Mul Polarity where
  mul
    | positive, s => s
    | negative, positive => negative
    | negative, negative => positive

/-- The polarities form the group of order two, each polarity its own inverse. -/
instance : CommGroup Polarity where
  inv := id
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_comm := by decide

@[simp] theorem one_eq_positive : (1 : Polarity) = positive := rfl

@[simp] theorem inv_eq_self (s : Polarity) : s⁻¹ = s := rfl

@[simp] theorem mul_self (s : Polarity) : s * s = positive := by cases s <;> rfl

@[simp] theorem positive_mul (s : Polarity) : positive * s = s := rfl

@[simp] theorem mul_positive (s : Polarity) : s * positive = s := mul_one s

/-- A polarity as a sign, positive `1` and negative `-1`. -/
@[coe] def toSignType : Polarity → SignType
  | positive => 1
  | negative => -1

instance : Coe Polarity SignType := ⟨toSignType⟩

@[simp] theorem coe_positive : ((positive : Polarity) : SignType) = 1 := rfl

@[simp] theorem coe_negative : ((negative : Polarity) : SignType) = -1 := rfl

@[simp] theorem coe_mul (s t : Polarity) : ((s * t : Polarity) : SignType) = s * t := by
  cases s <;> cases t <;> rfl

theorem coe_ne_zero (s : Polarity) : (s : SignType) ≠ 0 := by
  cases s <;> decide

/-- The polarities are the units of `ℤ`, `positive` being `1` and `negative` being `-1`. -/
def unitsEquiv : Polarity ≃* ℤˣ where
  toFun
    | positive => 1
    | negative => -1
  invFun u := if u = 1 then positive else negative
  left_inv s := by cases s <;> decide
  right_inv u := by rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  map_mul' s t := by cases s <;> cases t <;> decide

/-! ### Homomorphisms out of the polarities -/

section Lift

variable {M : Type*} [Monoid M]

/-- A homomorphism out of the polarities is fixed by its value at the negative polarity, an
element whose square is one. -/
def lift : {m : M // m * m = 1} ≃ (Polarity →* M) where
  toFun m :=
    { toFun
        | positive => 1
        | negative => m
      map_one' := rfl
      map_mul' := by rintro (_ | _) (_ | _) <;> simp [m.2] }
  invFun f := ⟨f negative, by rw [← map_mul, mul_self, ← one_eq_positive, map_one]⟩
  left_inv _ := rfl
  right_inv f := MonoidHom.ext <| by rintro (_ | _) <;> simp [← one_eq_positive]

@[simp] theorem lift_apply_positive (m : {m : M // m * m = 1}) : lift m positive = 1 := rfl

@[simp] theorem lift_apply_negative (m : {m : M // m * m = 1}) : lift m negative = m := rfl

@[ext] theorem hom_ext {f g : Polarity →* M} (h : f negative = g negative) : f = g :=
  lift.symm.injective (Subtype.ext h)

end Lift

/-! ### Actions -/

@[simp] theorem positive_smul {M : Type*} [MulAction Polarity M] (x : M) : positive • x = x :=
  one_smul _ x

/-- The orbit of an element under the polarities is the element and its image under the negative
polarity. -/
theorem orbit_eq_pair {M : Type*} [MulAction Polarity M] (x : M) :
    MulAction.orbit Polarity x = {x, negative • x} := by
  ext y
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_ | _, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    exacts [⟨positive, positive_smul _⟩, ⟨negative, rfl⟩]

variable {α : Type*}

/-- The polarity of a sentence acts on propositions. The positive polarity leaves a proposition,
the negative one takes its complement. -/
instance : MulAction Polarity (Set α) := .ofEndHom (lift ⟨compl, compl_involutive.comp_self⟩)

@[simp] theorem negative_smul_set (p : Set α) : negative • p = pᶜ := rfl

/-- Over a nonempty type the action on propositions is free, since no proposition is its own
complement. -/
instance [Nonempty α] : IsCancelSMul Polarity (Set α) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun s p h ↦ by
    cases s
    · rfl
    · exact absurd h compl_ne_self

/-- The polarity alternatives of a proposition are the proposition and its complement. -/
theorem orbit_eq_pair_compl (p : Set α) : MulAction.orbit Polarity p = {p, pᶜ} :=
  orbit_eq_pair p

/-- A polarity acts on an additive group through the units of `ℤ`, the negative polarity
negating. -/
instance [AddCommGroup α] : MulAction Polarity α :=
  MulAction.compHom α unitsEquiv.toMonoidHom

@[simp] theorem negative_smul [AddCommGroup α] (x : α) : negative • x = -x :=
  show ((-1 : ℤˣ) : ℤ) • x = -x by simp

/-- A polarity acts on signs, and so pointwise on trivalent propositions, the negative polarity
acting as Kleene negation. -/
instance : MulAction Polarity SignType := .ofEndHom (lift ⟨Neg.neg, neg_involutive.comp_self⟩)

@[simp] theorem negative_smul_signType (a : SignType) : negative • a = -a := rfl

/-- The action on signs is multiplication by the sign of the polarity. -/
theorem smul_signType (s : Polarity) (a : SignType) : s • a = s * a := by
  cases s <;> simp

section Directed

variable {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]

/-- A function directed by a polarity is strictly monotone under the positive polarity and
strictly antitone under the negative one. -/
def StrictMonoBy : Polarity → (α → β) → Prop
  | positive, f => StrictMono f
  | negative, f => StrictAnti f

theorem StrictMonoBy.comp {s t : Polarity} {g : β → γ} {f : α → β} (hg : s.StrictMonoBy g)
    (hf : t.StrictMonoBy f) : (s * t).StrictMonoBy (g ∘ f) := by
  cases s <;> cases t
  exacts [StrictMono.comp hg hf, StrictMono.comp_strictAnti hg hf,
    StrictAnti.comp_strictMono hg hf, StrictAnti.comp hg hf]

end Directed

end Polarity
