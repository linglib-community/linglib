module

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

The polarity of an expression is positive or negative. The two polarities form the group of order
two, a negation cancelling a negation; they are the units of `ℤ` (`Polarity.unitsEquiv`). Each
notion of polarity in the library is an action of this one group:

* the polarity of a sentence acts on propositions, the negative polarity by complement
  (`negative • p = pᶜ`), the meaning of sentential negation, whose forms are in
  `Syntax/Negation`, and the orbit of a proposition, the proposition and its negation, is
  the set of its polarity alternatives (`orbit_eq_pair_compl`): the focus value of a focused
  polarity and the answers of the polar question. Once there is a world the action is free,
  no proposition being its own negation;
* the polarity of an antonym acts on degrees by negation (`negative • x = -x`) and on scales by
  duality (`Semantics/Degree/Antonymy`);
* the relative polarity of a response to an antecedent, [same] or [reverse], is the quotient of
  their polarities, the polarity taking the antecedent's proposition to the response's;
* the direction of a function, strictly monotone or strictly antitone (`StrictMonoBy`), with
  directions composing as polarities multiply.

Since these are one group acting in different ways, their interaction is statable: the negative
antonym *short* measures on the dual scale of *tall*, while sentential negation takes the
complement, so *not short* does not entail *tall*.

A polarity is a sign: it coerces into `SignType` as `1` or `-1`. The three-valued sign also
records what a polarity cannot, the absence of a direction: the monotonicity of a context,
upward, downward or neither (`NaturalLogic.Signature.sign`), and a body of evidence or belief
bearing on a proposition, for it, against it or neither (`Question.BiasValue`). `UD.Polarity`, a
morphological feature of the annotation scheme, is a distinct type.

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

@[simp] theorem positive_smul {M : Type*} [MulAction Polarity M] (x : M) : positive • x = x :=
  one_smul _ x

variable {α : Type*}

/-- The polarity of a sentence acts on propositions. The positive polarity leaves a proposition,
the negative one takes its complement. -/
instance : MulAction Polarity (Set α) where
  smul
    | positive, p => p
    | negative, p => pᶜ
  one_smul _ := rfl
  mul_smul s t p := by cases s <;> cases t <;> first | rfl | exact (compl_compl p).symm

@[simp] theorem negative_smul_set (p : Set α) : negative • p = pᶜ := rfl

/-- Over a nonempty type the action on propositions is free, since no proposition is its own
complement. -/
instance [Nonempty α] : IsCancelSMul Polarity (Set α) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun s p h ↦ by
    cases s
    · rfl
    · exact absurd h compl_ne_self

theorem orbit_eq_pair_compl (p : Set α) : MulAction.orbit Polarity p = {p, pᶜ} := by
  ext q
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    cases s <;> simp
  · rintro (rfl | rfl)
    exacts [⟨positive, positive_smul _⟩, ⟨negative, negative_smul_set _⟩]

/-- A polarity acts on an additive group through the units of `ℤ`, the negative polarity
negating. -/
instance [AddCommGroup α] : MulAction Polarity α :=
  MulAction.compHom α unitsEquiv.toMonoidHom

@[simp] theorem negative_smul [AddCommGroup α] (x : α) : negative • x = -x :=
  show ((-1 : ℤˣ) : ℤ) • x = -x by simp

/-- A polarity acts on signs by multiplication, and so pointwise on trivalent propositions, the
negative polarity acting as Kleene negation. -/
instance : MulAction Polarity SignType where
  smul s a := s * a
  one_smul := one_mul
  mul_smul s t a := show ((s * t : Polarity) : SignType) * a = s * (t * a) by
    rw [coe_mul, mul_assoc]

@[simp] theorem negative_smul_signType (a : SignType) : negative • a = -a :=
  show (-1 : SignType) * a = -a from neg_one_mul a

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
