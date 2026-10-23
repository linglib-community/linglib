module

public import Linglib.Core.Order.Interval.Set.ProjIcc
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype

/-!
# Scale boundedness

This file defines `Degree.Boundedness`, the classification of scales by the endpoints they have,
for which Kennedy and McNally and, independently, Rotstein and Winter gave evidence from degree
modifiers. A boundedness is the endpoint profile of an order, and `Boundedness.ofOrder D` reads
it off `D` from the existence of a least and a greatest element, so that a scale's tag is a fact
about its degrees. The tag is what a lexical entry stores, since a record field cannot hold an
`OrderTop` instance.

The negative member of an antonym pair measures on the same degrees in the reverse order, and
`Boundedness.dual` is that operation on tags. The file also defines the standards of the positive
form and Kennedy's Interpretive Economy, which selects among them by the tag. A scale with an
endpoint rules out the contextual standard, and a totally closed scale prefers its maximum. A
difference function, which measures on the ray above a degree, always has the minimum standard,
and at it the positive form is a comparative.

## Main definitions

* `Boundedness`: the four endpoint profiles, with the predicates `HasMin` and `HasMax`.
* `Boundedness.ofOrder`: the boundedness of an order.
* `Boundedness.dual`: the boundedness with its ends exchanged.
* `Boundedness.withMin`: the boundedness with a least degree adjoined.
* `Boundedness.withMax`: the boundedness with a greatest degree adjoined.
* `Boundedness.DegreeShape`: a linear order of each boundedness.
* `PositiveStandard`: the standards of the positive form.
* `PositiveStandard.Complementary`: the standards of contradictory poles.
* `MinStandardPos`, `MaxStandardPos`, `RelativePos`: the positive form at Kennedy's standards.
* `Boundedness.Admits`: the standards Interpretive Economy admits on a scale.
* `Boundedness.defaultStandard`: the standard Interpretive Economy prefers on a scale.
* `EndpointModifier`, `Boundedness.Licenses`: maximizers and minimizers, licensed by an endpoint.

## Main statements

* `Boundedness.ofOrder_orderDual`: the order dual has the dual boundedness.
* `Boundedness.ofOrder_degreeShape`: every boundedness is that of a linear order.
* `Boundedness.admits_withMin_iff`: a scale with a least degree adjoined admits the minimum
  standard, and the maximum exactly when the original scale has one.
* `minStandardPos_projIci_comp_iff`: a comparative is the positive form of a difference function
  at the minimum standard.
* `Boundedness.defaultStandard_eq_maxEndpoint_iff`: the default standard is the maximum iff any.
* `Boundedness.complementary_defaultStandard_dual_iff`: poles on a half-closed scale contradict.

## References

* [C. Kennedy and L. McNally, *Scale Structure, Degree Modification, and the Semantics of Gradable
  Predicates* (2005)][kennedy-mcnally-2005]
* [C. Kennedy, *Vagueness and Grammar: The Semantics of Relative and Absolute Gradable Adjectives*
  (2007)][kennedy-2007]
* [C. Rotstein and Y. Winter, *Total Adjectives vs. Partial Adjectives: Scale Structure and
  Higher-Order Modifiers* (2004)][rotstein-winter-2004]
* [C. Kennedy and B. Levin, *Measure of Change: The Adjectival Core of Degree Achievements*
  (2008)][kennedy-levin-2008]
* [E. Klein, *A Semantics for Positive and Comparative Adjectives* (1980)][klein-1980]
* [A. Beltrama, *Evaluation, Thresholds, and Practical Commitments: The Grammar of Adjectival
  Mildness* (2025)][beltrama-2025]
* [M. Morzycki, *Adjectival Extremeness: Degree Modification and Contextually Restricted Scales*
  (2012)][morzycki-2012]
-/

@[expose] public section

namespace Degree

/-- Which endpoints a scale has ([kennedy-mcnally-2005] (23), [kennedy-2007] (59)). Open
scales may further approach a value without reaching it or be unbounded ([kennedy-2007]
fn. 28); the tag does not record that. -/
inductive Boundedness where
  | open_        -- neither endpoint: *tall*
  | lowerClosed -- a minimum, no maximum: *wet*
  | upperClosed -- a maximum, no minimum: *dry*
  | closed       -- both: *full*
  deriving DecidableEq, Repr, Fintype

namespace Boundedness

/-! ### Endpoints -/

/-- The scale has a minimum. -/
def HasMin : Boundedness → Prop
  | .lowerClosed | .closed => True
  | .open_ | .upperClosed => False

/-- The scale has a maximum. -/
def HasMax : Boundedness → Prop
  | .upperClosed | .closed => True
  | .open_ | .lowerClosed => False

instance : DecidablePred HasMin
  | .open_ | .upperClosed => isFalse id
  | .lowerClosed | .closed => isTrue trivial

instance : DecidablePred HasMax
  | .open_ | .lowerClosed => isFalse id
  | .upperClosed | .closed => isTrue trivial

/-- A boundedness is determined by which endpoints it has. -/
@[ext] theorem ext {b c : Boundedness} (hmin : b.HasMin ↔ c.HasMin) (hmax : b.HasMax ↔ c.HasMax) :
    b = c := by
  revert hmin hmax; cases b <;> cases c <;> decide

/-- A scale is upper closed exactly when it has a maximum and no minimum. -/
theorem eq_upperClosed_iff {b : Boundedness} : b = .upperClosed ↔ b.HasMax ∧ ¬ b.HasMin := by
  cases b <;> decide

/-! ### The boundedness of an order -/

section OfOrder
variable {D : Type*}

open Classical in
/-- The boundedness of an order records which of a least and a greatest element it has. -/
noncomputable def ofOrder (D : Type*) [LE D] : Boundedness :=
  if ∃ m : D, IsBot m then if ∃ m : D, IsTop m then closed else lowerClosed
  else if ∃ m : D, IsTop m then upperClosed else open_

section LE
variable [LE D]

theorem hasMin_ofOrder : (ofOrder D).HasMin ↔ ∃ m : D, IsBot m := by
  unfold ofOrder; split_ifs <;> simp [HasMin, *]

theorem hasMax_ofOrder : (ofOrder D).HasMax ↔ ∃ m : D, IsTop m := by
  unfold ofOrder; split_ifs <;> simp [HasMax, *]

@[simp] theorem hasMin_ofOrder_of_orderBot [OrderBot D] : (ofOrder D).HasMin :=
  hasMin_ofOrder.2 ⟨⊥, isBot_bot⟩

@[simp] theorem hasMax_ofOrder_of_orderTop [OrderTop D] : (ofOrder D).HasMax :=
  hasMax_ofOrder.2 ⟨⊤, isTop_top⟩

end LE

section Preorder
variable [Preorder D]

@[simp] theorem not_hasMin_ofOrder [NoMinOrder D] : ¬ (ofOrder D).HasMin :=
  fun h ↦ let ⟨m, hm⟩ := hasMin_ofOrder.1 h; not_isMin m hm.isMin

@[simp] theorem not_hasMax_ofOrder [NoMaxOrder D] : ¬ (ofOrder D).HasMax :=
  fun h ↦ let ⟨m, hm⟩ := hasMax_ofOrder.1 h; not_isMax m hm.isMax

end Preorder
end OfOrder

/-! ### The ends exchanged -/

/-- The dual of a boundedness exchanges its ends, giving the scale of the antonym
([kennedy-2007] (60)). -/
def dual : Boundedness → Boundedness
  | .open_ => .open_
  | .lowerClosed => .upperClosed
  | .upperClosed => .lowerClosed
  | .closed => .closed

@[simp] theorem hasMin_dual {b : Boundedness} : b.dual.HasMin ↔ b.HasMax := by
  cases b <;> exact Iff.rfl

@[simp] theorem hasMax_dual {b : Boundedness} : b.dual.HasMax ↔ b.HasMin := by
  cases b <;> exact Iff.rfl

theorem dual_involutive : Function.Involutive dual := fun b ↦ by cases b <;> rfl

@[simp] theorem dual_dual (b : Boundedness) : b.dual.dual = b := dual_involutive b

/-- Reversing the order of the degrees exchanges the ends of the scale, so the negative antonym,
which measures on the order dual ([kennedy-2007] (60), [kennedy-mcnally-2005]), has the dual
boundedness. -/
@[simp] theorem ofOrder_orderDual {D : Type*} [LE D] : ofOrder Dᵒᵈ = (ofOrder D).dual :=
  ext (by simp [hasMin_ofOrder, hasMax_ofOrder, OrderDual.exists])
    (by simp [hasMin_ofOrder, hasMax_ofOrder, OrderDual.exists])

/-! ### An endpoint adjoined -/

/-- `b.withMin` is `b` with a least degree adjoined, the shape of a ray `Set.Ici a`. -/
def withMin : Boundedness → Boundedness
  | .open_ | .lowerClosed => .lowerClosed
  | .upperClosed | .closed => .closed

/-- `b.withMax` is `b` with a greatest degree adjoined, the shape of a ray `Set.Iic a`. -/
def withMax : Boundedness → Boundedness
  | .open_ | .upperClosed => .upperClosed
  | .lowerClosed | .closed => .closed

@[simp] theorem hasMin_withMin (b : Boundedness) : b.withMin.HasMin := by cases b <;> trivial

@[simp] theorem hasMax_withMin {b : Boundedness} : b.withMin.HasMax ↔ b.HasMax := by
  cases b <;> exact Iff.rfl

@[simp] theorem hasMax_withMax (b : Boundedness) : b.withMax.HasMax := by cases b <;> trivial

@[simp] theorem hasMin_withMax {b : Boundedness} : b.withMax.HasMin ↔ b.HasMin := by
  cases b <;> exact Iff.rfl

@[simp] theorem dual_withMin (b : Boundedness) : b.withMin.dual = b.dual.withMax := by
  cases b <;> rfl

@[simp] theorem dual_withMax (b : Boundedness) : b.withMax.dual = b.dual.withMin := by
  cases b <;> rfl

section Ray
variable {D : Type*} [Preorder D] {a : D}

/-- The ray from `a` up has a least degree, `a`, and a greatest one exactly when `D` has. -/
theorem ofOrder_Ici [IsDirectedOrder D] : ofOrder (Set.Ici a) = (ofOrder D).withMin := by
  refine ext (iff_of_true (hasMin_ofOrder.2 ⟨⟨a, le_rfl⟩, fun x ↦ x.2⟩) (hasMin_withMin _)) ?_
  rw [hasMax_ofOrder, hasMax_withMin, hasMax_ofOrder]
  refine ⟨fun ⟨⟨m, _⟩, hm⟩ ↦ ⟨m, fun x ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨⟨m, hm a⟩, fun x ↦ hm x⟩⟩
  obtain ⟨c, hxc, hac⟩ := exists_ge_ge x a
  exact le_trans hxc (hm ⟨c, hac⟩)

/-- The ray from `a` down has a greatest degree, `a`, and a least one exactly when `D` has. -/
theorem ofOrder_Iic [IsCodirectedOrder D] : ofOrder (Set.Iic a) = (ofOrder D).withMax := by
  refine ext ?_ (iff_of_true (hasMax_ofOrder.2 ⟨⟨a, le_rfl⟩, fun x ↦ x.2⟩) (hasMax_withMax _))
  rw [hasMin_ofOrder, hasMin_withMax, hasMin_ofOrder]
  refine ⟨fun ⟨⟨m, _⟩, hm⟩ ↦ ⟨m, fun x ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨⟨m, hm a⟩, fun x ↦ hm x⟩⟩
  obtain ⟨c, hcx, hca⟩ := exists_le_le x a
  exact le_trans (hm ⟨c, hca⟩) hcx

end Ray

section Interval
variable {D : Type*} [Preorder D] {a b : D}

/-- A closed interval is a totally closed scale, as the probability scale `[0, 1]` is. -/
theorem ofOrder_Icc (h : a ≤ b) : ofOrder (Set.Icc a b) = closed :=
  ext (iff_of_true (hasMin_ofOrder.2 ⟨⟨a, le_rfl, h⟩, fun x ↦ x.2.1⟩) trivial)
    (iff_of_true (hasMax_ofOrder.2 ⟨⟨b, h, le_rfl⟩, fun x ↦ x.2.2⟩) trivial)

/-- An open interval of a dense order is a totally open scale. -/
theorem ofOrder_Ioo [DenselyOrdered D] : ofOrder (Set.Ioo a b) = open_ :=
  ext (iff_of_false not_hasMin_ofOrder id) (iff_of_false not_hasMax_ofOrder id)

/-- A half-open interval `(a, b]` of a dense order is an upper closed scale. -/
theorem ofOrder_Ioc [DenselyOrdered D] (h : a < b) : ofOrder (Set.Ioc a b) = upperClosed :=
  ext (iff_of_false not_hasMin_ofOrder id)
    (iff_of_true (hasMax_ofOrder.2 ⟨⟨b, h, le_rfl⟩, fun x ↦ x.2.2⟩) trivial)

end Interval

/-! ### A linear order of each shape -/

/-- `b.DegreeShape` is the integers with the endpoints of `b` adjoined, a linear order of each
boundedness. -/
abbrev DegreeShape : Boundedness → Type
  | .open_ => ℤ
  | .lowerClosed => WithBot ℤ
  | .upperClosed => WithTop ℤ
  | .closed => WithTop (WithBot ℤ)

instance instLinearOrderDegreeShape (b : Boundedness) : LinearOrder b.DegreeShape := by
  cases b <;> exact inferInstance

/-- Every boundedness is that of a linear order, since `DegreeShape` is a section of `ofOrder`. -/
@[simp] theorem ofOrder_degreeShape : ∀ b : Boundedness, ofOrder b.DegreeShape = b
  | .open_ => ext (iff_of_false not_hasMin_ofOrder id) (iff_of_false not_hasMax_ofOrder id)
  | .lowerClosed =>
    ext (iff_of_true hasMin_ofOrder_of_orderBot trivial) (iff_of_false not_hasMax_ofOrder id)
  | .upperClosed =>
    ext (iff_of_false not_hasMin_ofOrder id) (iff_of_true hasMax_ofOrder_of_orderTop trivial)
  | .closed =>
    ext (iff_of_true hasMin_ofOrder_of_orderBot trivial)
      (iff_of_true hasMax_ofOrder_of_orderTop trivial)

theorem exists_isBot_degreeShape (b : Boundedness) : (∃ m : b.DegreeShape, IsBot m) ↔ b.HasMin := by
  rw [← hasMin_ofOrder, ofOrder_degreeShape]

theorem exists_isTop_degreeShape (b : Boundedness) : (∃ m : b.DegreeShape, IsTop m) ↔ b.HasMax := by
  rw [← hasMax_ofOrder, ofOrder_degreeShape]

end Boundedness

/-! ### Standards and Interpretive Economy

The positive form of a gradable predicate is true of what meets a standard on its scale.
Interpretive Economy maximizes the contribution of conventional meaning, so a scale with an endpoint
rules out the contextual standard, and a totally closed scale admits both endpoint standards and
prefers the maximum. -/

/-- A positive standard is the kind of threshold the positive form compares a degree with, a
contextual norm on an open scale and an endpoint on a closed one ([kennedy-2007]), or a standard
an adjective fixes lexically outside that choice. -/
inductive PositiveStandard where
  /-- The norm of a comparison class, as for *tall*. -/
  | contextual
  /-- The minimum of the scale, as for *bent* and *wet*. -/
  | minEndpoint
  /-- The maximum of the scale, as for *full* and *dry*. -/
  | maxEndpoint
  /-- The minimum degree for pursuit ([beltrama-2025]). -/
  | necessity
  /-- A standard beyond that of the weak adjective on the same pole, as for *gigantic* and
  *pristine* ([morzycki-2012]). -/
  | extreme
  deriving DecidableEq, Repr

/-- A standard requires a comparison class when fixing it needs contextual information about a
domain. [kennedy-2007] argues against a comparison-class argument of the positive form, as in
[klein-1980], and states the positive form with a standard-fixing function,
`⟦pos⟧ = λg.λx. g(x) ⪰ s(g)` ((27)), which still needs that information for the contextual and
necessity standards. An extreme standard lies beyond the degrees a context makes salient
([morzycki-2012]), so it needs that information too. -/
def PositiveStandard.RequiresComparisonClass : PositiveStandard → Prop
  | .contextual  => True
  | .minEndpoint => False
  | .maxEndpoint => False
  | .necessity   => True
  | .extreme     => True

instance : DecidablePred PositiveStandard.RequiresComparisonClass
  | .contextual  => inferInstanceAs (Decidable True)
  | .minEndpoint => inferInstanceAs (Decidable False)
  | .maxEndpoint => inferInstanceAs (Decidable False)
  | .necessity   => inferInstanceAs (Decidable True)
  | .extreme     => inferInstanceAs (Decidable True)

/-- Two standards are complementary when one is the minimum and the other the maximum. The poles
of an antonym pair that take them are contradictory, denying one asserting the other
([kennedy-2007] (47)), and any other pair of standards leaves a gap. -/
def PositiveStandard.Complementary (s t : PositiveStandard) : Prop :=
  s = .minEndpoint ∧ t = .maxEndpoint ∨ s = .maxEndpoint ∧ t = .minEndpoint

instance : DecidableRel PositiveStandard.Complementary := fun _ _ ↦ by
  unfold PositiveStandard.Complementary; infer_instance

/-! ### The positive form at Kennedy's standards -/

section PositiveForm
variable {α D : Type*} [Preorder D] (μ : α → D)

/-- The positive form at the minimum standard holds of `x` when its degree is above the least
degree of the scale, as for *wet* and *bent*. -/
def MinStandardPos [OrderBot D] (x : α) : Prop := ⊥ < μ x

/-- The positive form at the maximum standard holds of `x` when its degree is the greatest degree
of the scale, as for *dry* and *full*. -/
def MaxStandardPos [OrderTop D] (x : α) : Prop := μ x = ⊤

/-- The positive form at a contextual standard `θ` holds of `x` when its degree exceeds `θ`, as
for *tall*. -/
def RelativePos (θ : D) (x : α) : Prop := θ < μ x

variable {μ} in
/-- When the least degree is below the greatest, the positive form at the maximum standard entails
the one at the minimum, which is why a totally closed scale prefers its maximum. -/
theorem MaxStandardPos.minStandardPos [OrderBot D] [OrderTop D] (h : (⊥ : D) < ⊤) {x : α}
    (hx : MaxStandardPos μ x) : MinStandardPos μ x :=
  h.trans_eq (Eq.symm hx)

end PositiveForm

/-! ### Difference functions

The difference function of a measure `μ` at a degree `d` is `Set.projIci d ∘ μ`, which measures on
the ray above `d` and sends every degree at or below `d` to `d`, the derived zero. The ray has a
least degree (`Boundedness.ofOrder_Ici`), so Interpretive Economy admits the minimum standard for
a difference function, giving the truth conditions of a comparative with standard `d`, and the
maximum standard exactly when the scale of `μ` has one. -/

section Difference
variable {α D : Type*} [LinearOrder D] {μ : α → D} {d : D} {x : α}

/-- The positive form of a difference function at the minimum standard holds of what `μ` places
above `d`, the comparative ([kennedy-mcnally-2005], [kennedy-levin-2008] (24)). -/
theorem minStandardPos_projIci_comp_iff : MinStandardPos (Set.projIci d ∘ μ) x ↔ d < μ x :=
  Set.bot_lt_projIci

/-- Unless `d` is the greatest degree, the positive form of a difference function at the maximum
standard is that of `μ` itself ([kennedy-levin-2008] fn. 16). -/
theorem maxStandardPos_projIci_comp_iff [OrderTop D] (hd : d ≠ ⊤) :
    MaxStandardPos (Set.projIci d ∘ μ) x ↔ MaxStandardPos μ x := by
  rw [MaxStandardPos, MaxStandardPos, Function.comp_apply, Set.projIci_eq_top, or_iff_right hd]

end Difference

namespace Boundedness

/-- Interpretive Economy admits an endpoint standard exactly where the scale has that endpoint, the
contextual standard, which context must supply, only on a totally open scale, and the lexical
necessity and extreme standards never ([kennedy-2007] (66)). A totally closed scale therefore
admits both endpoints ((67)–(68)). -/
def Admits (b : Boundedness) : PositiveStandard → Prop
  | .contextual  => b = .open_
  | .minEndpoint => b.HasMin
  | .maxEndpoint => b.HasMax
  | .necessity   => False
  | .extreme     => False

instance (b : Boundedness) (s : PositiveStandard) : Decidable (b.Admits s) := by
  cases s <;> simp only [Admits] <;> infer_instance

/-- The default standard of a scale is the one Interpretive Economy forces where it admits only
one, and the maximum on a totally closed scale, since a maximum standard entails a minimum one. -/
def defaultStandard : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerClosed => .minEndpoint
  | .upperClosed => .maxEndpoint
  | .closed       => .maxEndpoint

/-- The default standard is always admitted. -/
theorem admits_defaultStandard (b : Boundedness) : b.Admits b.defaultStandard := by
  cases b <;> decide

/-- The default standard is the maximum exactly when the scale has one. -/
theorem defaultStandard_eq_maxEndpoint_iff {b : Boundedness} :
    b.defaultStandard = .maxEndpoint ↔ b.HasMax := by
  cases b <;> decide

/-- The default standards of a scale and its dual are complementary exactly when the scale has one
endpoint. An open scale gives both poles a contextual standard and a totally closed one gives both
the maximum, as for *full* and *empty*. -/
theorem complementary_defaultStandard_dual_iff {b : Boundedness} :
    b.defaultStandard.Complementary b.dual.defaultStandard ↔
      b = .lowerClosed ∨ b = .upperClosed := by
  cases b <;> decide

@[simp] theorem admits_contextual {b : Boundedness} : b.Admits .contextual ↔ b = .open_ :=
  Iff.rfl

@[simp] theorem admits_minEndpoint {b : Boundedness} : b.Admits .minEndpoint ↔ b.HasMin :=
  Iff.rfl

@[simp] theorem admits_maxEndpoint {b : Boundedness} : b.Admits .maxEndpoint ↔ b.HasMax :=
  Iff.rfl

@[simp] theorem not_admits_necessity (b : Boundedness) : ¬ b.Admits .necessity := id

@[simp] theorem not_admits_extreme (b : Boundedness) : ¬ b.Admits .extreme := id

/-- Interpretive Economy rules out the contextual standard whenever the scale has an endpoint. -/
theorem not_admits_contextual_of_ne_open {b : Boundedness} (h : b ≠ .open_) :
    ¬ b.Admits .contextual := h

/-- A scale is relative when its default standard needs a comparison class, which is to say when
it is open, as for *tall*, *expensive* and *big*. -/
def IsRelative (b : Boundedness) : Prop := b.defaultStandard.RequiresComparisonClass

instance : DecidablePred IsRelative :=
  fun b ↦ inferInstanceAs (Decidable b.defaultStandard.RequiresComparisonClass)

/-- A scale with a least degree adjoined, the scale of a difference function or a measure of
change ([kennedy-levin-2008] (23), (25)), admits the minimum standard, and the maximum exactly
when the original scale has one. -/
theorem admits_withMin_iff {b : Boundedness} {s : PositiveStandard} :
    b.withMin.Admits s ↔ s = .minEndpoint ∨ s = .maxEndpoint ∧ b.HasMax := by
  cases b <;> cases s <;> simp [Admits, withMin, HasMin, HasMax]

/-- The default standard of a scale with a least degree adjoined is the maximum when the original
scale has one, and the minimum otherwise. -/
theorem defaultStandard_withMin (b : Boundedness) :
    b.withMin.defaultStandard = if b.HasMax then .maxEndpoint else .minEndpoint := by
  cases b <;> rfl

end Boundedness

/-! ### Endpoint modifiers -/

/-- An endpoint modifier is a degree modifier that refers to an endpoint of the scale, a maximizer
such as *completely* or *fully*, or a minimizer such as *slightly* or *partially*
([kennedy-mcnally-2005], [kennedy-2007] (61)). -/
inductive EndpointModifier where
  | maximizer
  | minimizer
  deriving DecidableEq, Repr

/-- A scale licenses an endpoint modifier when it has the endpoint the modifier picks out. -/
def Boundedness.Licenses (b : Boundedness) : EndpointModifier → Prop
  | .maximizer => b.HasMax
  | .minimizer => b.HasMin

instance (b : Boundedness) : DecidablePred b.Licenses
  | .maximizer => inferInstanceAs (Decidable b.HasMax)
  | .minimizer => inferInstanceAs (Decidable b.HasMin)

@[simp] theorem Boundedness.licenses_maximizer {b : Boundedness} :
    b.Licenses .maximizer ↔ b.HasMax := Iff.rfl

@[simp] theorem Boundedness.licenses_minimizer {b : Boundedness} :
    b.Licenses .minimizer ↔ b.HasMin := Iff.rfl

end Degree
