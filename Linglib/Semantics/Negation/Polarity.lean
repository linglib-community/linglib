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
public import Linglib.Logic.Trivalent.Connectives

/-!
# Polarity

This file defines the polarity of an expression, positive or negative. The two polarities form a
group of order two with the positive polarity as its identity, so a homomorphism out of them is
given by an element whose square is one. In this way the polarities act on the sets of a type and on
propositions by complement, on an additive group by negation, and on signs and three-valued truth
values by their negations. The orbit of a proposition is the pair of its polarity alternatives. A
polarity also gives a function between preorders a direction: the positive polarity directs the
monotone functions and the negative polarity the antitone ones.

## Main definitions

* `Polarity.lift`: the equivalence between the elements of a monoid whose square is one and the
  homomorphisms out of the polarities.
* `Polarity.MonoBy`: a function is directed by the positive polarity when it is monotone and by the
  negative polarity when it is antitone.

## Main results

* `Polarity.orbit_eq_pair_compl`: the orbit of a set under the polarities is the set and its
  complement.
* `Polarity.MonoBy.comp`: the composition of a function directed by `s` with one directed by `t` is
  directed by `s * t`.

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

/-- The polarities act on a Boolean algebra by complement: the positive polarity leaves an
element, the negative one takes its complement. -/
def complHom [BooleanAlgebra α] : Polarity →* Function.End α :=
  lift ⟨compl, compl_involutive.comp_self⟩

@[simp] theorem complHom_positive [BooleanAlgebra α] (x : α) : complHom positive x = x := rfl

@[simp] theorem complHom_negative [BooleanAlgebra α] (x : α) : complHom negative x = xᶜ := rfl

/-- Different polarities take an element to complementary elements. -/
theorem complHom_of_ne [BooleanAlgebra α] {s t : Polarity} (h : s ≠ t) (x : α) :
    complHom s x = (complHom t x)ᶜ := by
  cases s <;> cases t <;> simp_all

/-- The polarity of a sentence acts on propositions. The positive polarity leaves a proposition,
the negative one takes its complement. -/
instance : MulAction Polarity (Set α) := .ofEndHom complHom

@[simp] theorem negative_smul_set (p : Set α) : negative • p = pᶜ := rfl

instance decidableMemSMul (p : Polarity) (s : Set α) [DecidablePred (· ∈ s)] :
    DecidablePred (· ∈ p • s) :=
  match p with
  | .positive => fun a ↦ inferInstanceAs (Decidable (a ∈ s))
  | .negative => fun a ↦ inferInstanceAs (Decidable (a ∉ s))

/-- The polarity of a sentence acts on truth values, the negative polarity negating. -/
instance : MulAction Polarity Prop := .ofEndHom complHom

@[simp] theorem negative_smul_prop (p : Prop) : negative • p = ¬ p := rfl

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

/-- A polarity acts on signs, the negative polarity reversing the sign. -/
instance : MulAction Polarity SignType := .ofEndHom (lift ⟨Neg.neg, neg_involutive.comp_self⟩)

@[simp] theorem negative_smul_signType (a : SignType) : negative • a = -a := rfl

/-- A polarity acts on truth values, and so pointwise on trivalent propositions, the negative
polarity acting as Kleene negation. -/
instance : MulAction Polarity Trivalent :=
  .ofEndHom (lift ⟨compl,
    (show Function.Involutive (compl : Trivalent → Trivalent) from
      Trivalent.compl_compl).comp_self⟩)

@[simp] theorem negative_smul_trivalent (a : Trivalent) : negative • a = aᶜ := rfl

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

/-- A function directed by a polarity is monotone under the positive polarity and antitone under
the negative one. -/
def MonoBy : Polarity → (α → β) → Prop
  | positive, f => Monotone f
  | negative, f => Antitone f

@[simp] theorem monoBy_positive {f : α → β} : positive.MonoBy f ↔ Monotone f := .rfl

@[simp] theorem monoBy_negative {f : α → β} : negative.MonoBy f ↔ Antitone f := .rfl

theorem MonoBy.comp {s t : Polarity} {g : β → γ} {f : α → β} (hg : s.MonoBy g)
    (hf : t.MonoBy f) : (s * t).MonoBy (g ∘ f) := by
  cases s <;> cases t
  exacts [Monotone.comp (g := g) hg hf, Monotone.comp_antitone (g := g) hg hf,
    Antitone.comp_monotone (g := g) hg hf, Antitone.comp (g := g) hg hf]

end Directed

end Polarity
