module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype

/-!
# Scale boundedness

`Boundedness` classifies a scale by the endpoints it has, a classification for which Kennedy and
McNally and, independently, Rotstein and Winter gave evidence from degree modifiers. The tag is a
fact about the degrees: [`Boundedness.ofOrder`](##Boundedness.ofOrder) reads it off an order, and
[every tag is the boundedness of a linear order](##Boundedness.ofOrder_degreeShape), the integers
with the endpoints adjoined. The negative member of an antonym pair measures on the same degrees
in the reverse order, which [exchanges the endpoints](##Boundedness.dual), and an endpoint modifier
such as *completely* is [licensed by the endpoint it picks out](##Boundedness.Licenses).

## Implementation notes

A lexical entry stores the tag, since a record field cannot hold an `OrderTop` instance.

## References

* [kennedy-mcnally-2005]
* [rotstein-winter-2004]
* [kennedy-2007]
-/

@[expose] public section

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

@[ext] theorem ext {b c : Boundedness} (hmin : b.HasMin ↔ c.HasMin) (hmax : b.HasMax ↔ c.HasMax) :
    b = c := by
  revert hmin hmax; cases b <;> cases c <;> decide

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

/-- The negative antonym, measuring on the order dual, has the dual boundedness ([kennedy-2007]
(60), [kennedy-mcnally-2005]). -/
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

theorem ofOrder_Ici [IsDirectedOrder D] : ofOrder (Set.Ici a) = (ofOrder D).withMin := by
  refine ext (iff_of_true (hasMin_ofOrder.2 ⟨⟨a, le_rfl⟩, fun x ↦ x.2⟩) (hasMin_withMin _)) ?_
  rw [hasMax_ofOrder, hasMax_withMin, hasMax_ofOrder]
  refine ⟨fun ⟨⟨m, _⟩, hm⟩ ↦ ⟨m, fun x ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨⟨m, hm a⟩, fun x ↦ hm x⟩⟩
  obtain ⟨c, hxc, hac⟩ := exists_ge_ge x a
  exact le_trans hxc (hm ⟨c, hac⟩)

theorem ofOrder_Iic [IsCodirectedOrder D] : ofOrder (Set.Iic a) = (ofOrder D).withMax := by
  refine ext ?_ (iff_of_true (hasMax_ofOrder.2 ⟨⟨a, le_rfl⟩, fun x ↦ x.2⟩) (hasMax_withMax _))
  rw [hasMin_ofOrder, hasMin_withMax, hasMin_ofOrder]
  refine ⟨fun ⟨⟨m, _⟩, hm⟩ ↦ ⟨m, fun x ↦ ?_⟩, fun ⟨m, hm⟩ ↦ ⟨⟨m, hm a⟩, fun x ↦ hm x⟩⟩
  obtain ⟨c, hcx, hca⟩ := exists_le_le x a
  exact le_trans (hm ⟨c, hca⟩) hcx

end Ray

section Interval
variable {D : Type*} [Preorder D] {a b : D}

theorem ofOrder_Icc (h : a ≤ b) : ofOrder (Set.Icc a b) = closed :=
  ext (iff_of_true (hasMin_ofOrder.2 ⟨⟨a, le_rfl, h⟩, fun x ↦ x.2.1⟩) trivial)
    (iff_of_true (hasMax_ofOrder.2 ⟨⟨b, h, le_rfl⟩, fun x ↦ x.2.2⟩) trivial)

theorem ofOrder_Ioo [DenselyOrdered D] : ofOrder (Set.Ioo a b) = open_ :=
  ext (iff_of_false not_hasMin_ofOrder id) (iff_of_false not_hasMax_ofOrder id)

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

theorem exists_not_isBot_not_isTop (b : Boundedness) :
    ∃ x : b.DegreeShape, ¬ IsBot x ∧ ¬ IsTop x := by
  cases b
  · exact ⟨(0 : ℤ), not_isBot _, not_isTop _⟩
  · exact ⟨((0 : ℤ) : WithBot ℤ), fun h ↦ (WithBot.bot_lt_coe 0).not_ge (h ⊥),
      fun h ↦ absurd (h ((1 : ℤ) : WithBot ℤ)) (by simp)⟩
  · exact ⟨((0 : ℤ) : WithTop ℤ), fun h ↦ absurd (h ((-1 : ℤ) : WithTop ℤ)) (by simp),
      fun h ↦ (WithTop.coe_lt_top 0).not_ge (h ⊤)⟩
  · exact ⟨(((0 : ℤ) : WithBot ℤ) : WithTop (WithBot ℤ)),
      fun h ↦ absurd (h ⊥) (by simp), fun h ↦ absurd (h ⊤) (by simp)⟩

private theorem exists_orderIso_withBot {x y : WithBot ℤ} (hx : ¬ IsBot x) (hy : ¬ IsBot y) :
    ∃ f : WithBot ℤ ≃o WithBot ℤ, f x = y := by
  obtain ⟨a, rfl⟩ := WithBot.ne_bot_iff_exists.1 (show x ≠ ⊥ from mt isBot_iff_eq_bot.2 hx)
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.1 (show y ≠ ⊥ from mt isBot_iff_eq_bot.2 hy)
  exact ⟨(OrderIso.addRight (c - a)).withBotCongr, by simp⟩

private theorem exists_orderIso_withTop {x y : WithTop ℤ} (hx : ¬ IsTop x) (hy : ¬ IsTop y) :
    ∃ f : WithTop ℤ ≃o WithTop ℤ, f x = y := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 (show x ≠ ⊤ from mt isTop_iff_eq_top.2 hx)
  obtain ⟨c, rfl⟩ := WithTop.ne_top_iff_exists.1 (show y ≠ ⊤ from mt isTop_iff_eq_top.2 hy)
  exact ⟨(OrderIso.addRight (c - a)).withTopCongr, by simp⟩

private theorem exists_orderIso_withTop_withBot {x y : WithTop (WithBot ℤ)}
    (hxb : ¬ IsBot x) (hxt : ¬ IsTop x) (hyb : ¬ IsBot y) (hyt : ¬ IsTop y) :
    ∃ f : WithTop (WithBot ℤ) ≃o WithTop (WithBot ℤ), f x = y := by
  obtain ⟨x, rfl⟩ := WithTop.ne_top_iff_exists.1 (show x ≠ ⊤ from mt isTop_iff_eq_top.2 hxt)
  obtain ⟨y, rfl⟩ := WithTop.ne_top_iff_exists.1 (show y ≠ ⊤ from mt isTop_iff_eq_top.2 hyt)
  obtain ⟨f, hf⟩ := exists_orderIso_withBot (x := x) (y := y)
    (fun h ↦ hxb (isBot_iff_eq_bot.2 (by simp [isBot_iff_eq_bot.1 h])))
    (fun h ↦ hyb (isBot_iff_eq_bot.2 (by simp [isBot_iff_eq_bot.1 h])))
  exact ⟨f.withTopCongr, by simp [hf]⟩

theorem exists_orderIso_degreeShape (b : Boundedness) (x y : b.DegreeShape)
    (hxb : ¬ IsBot x) (hxt : ¬ IsTop x) (hyb : ¬ IsBot y) (hyt : ¬ IsTop y) :
    ∃ f : b.DegreeShape ≃o b.DegreeShape, f x = y := by
  cases b
  exacts [⟨OrderIso.addRight (y - x), by simp⟩, exists_orderIso_withBot hxb hyb,
    exists_orderIso_withTop hxt hyt, exists_orderIso_withTop_withBot hxb hxt hyb hyt]

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
