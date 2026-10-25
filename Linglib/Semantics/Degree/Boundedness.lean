module

public import Linglib.Core.Order.Interval.Set.ProjIcc
public import Linglib.Core.Order.UpperLower.Principal
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Directed
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
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
form and Kennedy's Interpretive Economy, which selects among them by the tag. A standard is an
upper set of degrees, and the positive form of a measure at it is the preimage of the standard.
Kennedy's standards are the degrees above the least, those from the greatest and those above a
contextual threshold. Interpretive Economy uses a standard the scale itself fixes when there is
one. Where an automorphism carries any degree between the endpoints to any other, the standards
every automorphism fixes are the trivial ones and the endpoint ones, so a scale with an endpoint
rules out the contextual standard. A difference function, which measures on the ray above a
degree, always has the minimum standard, and at it the positive form is a comparative.

## Main definitions

* `Boundedness`: the four endpoint profiles, with the predicates `HasMin` and `HasMax`.
* `Boundedness.ofOrder`: the boundedness of an order.
* `Boundedness.dual`, `Boundedness.withMin`, `Boundedness.withMax`: the ends exchanged, and a
  least or greatest degree adjoined.
* `Boundedness.DegreeShape`: the canonical linear order of each boundedness.
* `Degree.IsInvariant`: a standard every automorphism of the degrees maps to itself.
* `PositiveStandard`, `PositiveStandard.standards`: the kinds of standard of the positive form,
  and the standards of each kind on a scale.
* `Boundedness.Admits`, `Boundedness.defaultStandard`: the standards Interpretive Economy admits
  on a scale, and the one it prefers.
* `EndpointModifier`, `Boundedness.Licenses`: maximizers and minimizers, licensed by an endpoint.

## Main statements

* `Boundedness.ofOrder_degreeShape`: every boundedness is that of a linear order.
* `Degree.isInvariant_iff_of_exists_orderIso`: where an automorphism carries any degree between
  the endpoints to any other, the invariant standards are the trivial and the endpoint ones.
* `Boundedness.admits_contextual`: the contextual standard is admitted exactly on an open scale.
* `PositiveStandard.requiresComparisonClass_iff`, `PositiveStandard.complementary_iff`: the scale
  fixes exactly the endpoint standards, and only the minimum and the maximum are complementary.
* `preimage_projIci_comp_Ioi_bot`: a comparative is the positive form of a difference function
  at the minimum standard.

## Implementation notes

Kennedy states Interpretive Economy as maximizing the contribution of conventional meaning
((66)). Reading the standards a scale contributes as those fixed by every automorphism of its
degrees is this library's. It makes the admissibility of each standard a theorem about the
canonical scale of each tag, the integers with the endpoints adjoined, on which a shift carries
any degree between the endpoints to any other. The preference for the maximum on a totally
closed scale is Kennedy's and stays a stipulation (`defaultStandard`).

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

/-! ### Invariant standards

A standard of a scale is an upper set of its degrees, and the positive form at it holds of what
the measure places in it, so that a stronger standard, a smaller upper set, entails a weaker one.
A standard is invariant when the order alone singles it out, every automorphism of the degrees
mapping it to itself. All degrees and none are invariant, as are the degrees above a least one
and those from a greatest one, and where any degree between the endpoints is carried to any
other by an automorphism, as on the canonical scales, these are all. -/

section Invariant
variable {D : Type*}

/-- A standard is invariant when every order automorphism of the degrees maps it to itself. -/
def IsInvariant [Preorder D] (U : UpperSet D) : Prop := ∀ f : D ≃o D, UpperSet.map f U = U

variable [PartialOrder D] {U : UpperSet D} {m : D}

theorem isInvariant_bot : IsInvariant (⊥ : UpperSet D) := fun f ↦ map_bot (UpperSet.map f)

theorem isInvariant_top : IsInvariant (⊤ : UpperSet D) := fun f ↦ map_top (UpperSet.map f)

theorem isInvariant_Ioi_of_isBot (hm : IsBot m) : IsInvariant (UpperSet.Ioi m) := fun f ↦ by
  rw [UpperSet.map_Ioi, le_antisymm (by simpa using f.monotone (hm (f.symm m))) (hm (f m))]

theorem isInvariant_Ici_of_isTop (hm : IsTop m) : IsInvariant (UpperSet.Ici m) := fun f ↦ by
  rw [UpperSet.map_Ici, le_antisymm (hm (f m)) (by simpa using f.monotone (hm (f.symm m)))]

theorem IsInvariant.apply_mem (hU : IsInvariant U) (f : D ≃o D) {x : D} (hx : x ∈ U) :
    f x ∈ U := by
  rw [← hU f, UpperSet.mem_map]
  simpa using hx

end Invariant

section Homogeneous
variable {D : Type*} [LinearOrder D] {U : UpperSet D}

/-- Where an automorphism carries any degree strictly between the endpoints to any other, the
invariant standards are the trivial ones and the endpoint ones. -/
theorem isInvariant_iff_of_exists_orderIso (hI : ∃ x : D, ¬ IsBot x ∧ ¬ IsTop x)
    (h : ∀ x y : D, ¬ IsBot x → ¬ IsTop x → ¬ IsBot y → ¬ IsTop y → ∃ f : D ≃o D, f x = y) :
    IsInvariant U ↔
      U = ⊥ ∨ U = ⊤ ∨ (∃ m, IsBot m ∧ U = .Ioi m) ∨ ∃ m, IsTop m ∧ U = .Ici m := by
  refine ⟨fun hU ↦ ?_, ?_⟩
  · obtain ⟨x, hxb, hxt⟩ := hI
    by_cases hA : ∃ y ∈ U, ¬ IsBot y ∧ ¬ IsTop y
    · obtain ⟨y, hyU, hyb, hyt⟩ := hA
      -- with one degree between the endpoints, `U` holds every degree that is not least
      have hnb : ∀ z, ¬ IsBot z → z ∈ U := fun z hz ↦ by
        by_cases hzt : IsTop z
        · exact U.upper (hzt y) hyU
        · obtain ⟨f, rfl⟩ := h y z hyb hyt hz hzt
          exact hU.apply_mem f hyU
      by_cases hB : ∃ m : D, IsBot m
      · obtain ⟨m, hm⟩ := hB
        by_cases hmU : m ∈ U
        · exact .inl (SetLike.ext fun z ↦ by simpa using U.upper (hm z) hmU)
        · refine .inr (.inr (.inl ⟨m, hm, SetLike.ext fun z ↦ ?_⟩))
          simp only [UpperSet.mem_Ioi_iff]
          refine ⟨fun hz ↦ (hm z).lt_of_ne ?_, fun hz ↦ hnb z fun hz' ↦ hz.ne' ?_⟩
          · rintro rfl; exact hmU hz
          · exact le_antisymm (hz' m) (hm z)
      · push Not at hB
        exact .inl (SetLike.ext fun z ↦ by simpa using hnb z (hB z))
    · push Not at hA
      -- with none, `U` holds only greatest degrees, since `x` follows a least one
      have hb : ∀ z ∈ U, IsTop z := fun z hz ↦ by
        by_cases hzb : IsBot z
        · exact absurd (hA x (U.upper (hzb x) hz) hxb) hxt
        · exact hA z hz hzb
      by_cases hT : ∃ t, t ∈ U
      · obtain ⟨t, ht⟩ := hT
        refine .inr (.inr (.inr ⟨t, hb t ht, SetLike.ext fun z ↦ ?_⟩))
        simp only [UpperSet.mem_Ici_iff]
        exact ⟨fun hz ↦ hb z hz t, fun hz ↦ U.upper hz ht⟩
      · push Not at hT
        exact .inr (.inl (SetLike.ext fun z ↦ by simpa using fun h' ↦ hT z h'))
  · rintro (rfl | rfl | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    exacts [isInvariant_bot, isInvariant_top, isInvariant_Ioi_of_isBot hm,
      isInvariant_Ici_of_isTop hm]

theorem forall_isInvariant_iff_of_exists_orderIso (hI : ∃ x : D, ¬ IsBot x ∧ ¬ IsTop x)
    (h : ∀ x y : D, ¬ IsBot x → ¬ IsTop x → ¬ IsBot y → ¬ IsTop y → ∃ f : D ≃o D, f x = y) :
    (∀ U : UpperSet D, IsInvariant U → U = ⊥ ∨ U = ⊤) ↔
      (∀ m : D, ¬ IsBot m) ∧ ∀ m : D, ¬ IsTop m := by
  refine ⟨fun H ↦ ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩, fun ⟨hb, ht⟩ U hU ↦ ?_⟩
  · obtain ⟨x, hxb, -⟩ := hI
    rcases H _ (isInvariant_Ioi_of_isBot hm) with h' | h'
    · simpa using congrArg (m ∈ ·) h'
    · have hx : x ∈ UpperSet.Ioi m := (hm x).lt_of_ne fun h ↦ hxb (h ▸ hm)
      exact UpperSet.notMem_top (h' ▸ hx)
  · obtain ⟨x, -, hxt⟩ := hI
    rcases H _ (isInvariant_Ici_of_isTop hm) with h' | h'
    · exact hxt fun z ↦ (hm z).trans (by simpa using congrArg (x ∈ ·) h')
    · simpa using congrArg (m ∈ ·) h'
  · rcases (isInvariant_iff_of_exists_orderIso hI h).1 hU with h' | h' | ⟨m, hm, -⟩ | ⟨m, hm, -⟩
    exacts [.inl h', .inr h', (hb m hm).elim, (ht m hm).elim]

end Homogeneous

theorem Boundedness.isInvariant_degreeShape_iff (b : Boundedness) {U : UpperSet b.DegreeShape} :
    IsInvariant U ↔
      U = ⊥ ∨ U = ⊤ ∨ (∃ m, IsBot m ∧ U = .Ioi m) ∨ ∃ m, IsTop m ∧ U = .Ici m :=
  isInvariant_iff_of_exists_orderIso b.exists_not_isBot_not_isTop b.exists_orderIso_degreeShape

/-! ### Standards and Interpretive Economy

The positive form of a gradable predicate at a standard `U` is the preimage `μ ⁻¹' U` of the
standard under its measure, true of what the measure places in the standard. Kennedy's standards
are the degrees above the least, `Set.Ioi ⊥`, as for *wet* and *bent*; those from the greatest,
`Set.Ici ⊤`, as for *dry* and *full*; and those above a contextual threshold `θ`, `Set.Ioi θ`,
as for *tall*. When the least degree is below the greatest, the maximum standard is stronger than
the minimum (`UpperSet.Ioi_le_Ici`), and the minimum standard is the weakest nontrivial one,
covering the standard every degree meets (`UpperSet.Ici_covBy_Ioi`). Interpretive Economy
maximizes the contribution of conventional meaning, so a scale with an endpoint rules out the
contextual standard, and a totally closed scale admits both endpoint standards and prefers the
maximum. -/

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

/-- The standards of a kind on a scale. A minimum standard is the set of degrees above a least
degree and a maximum standard the set from a greatest one; a contextual, necessity or extreme
standard is a threshold, the degrees above or from some degree, which the context or the lexicon
fixes and the scale does not. -/
def PositiveStandard.standards (s : PositiveStandard) (D : Type*) [Preorder D] :
    Set (UpperSet D) :=
  match s with
  | .minEndpoint => {U | ∃ m, IsBot m ∧ U = .Ioi m}
  | .maxEndpoint => {U | ∃ m, IsTop m ∧ U = .Ici m}
  | .contextual | .necessity | .extreme => {U | ∃ θ, U = .Ioi θ ∨ U = .Ici θ}

namespace PositiveStandard

/-- A kind of standard requires a comparison class when the scale does not fix its standards, an
automorphism of some scale moving one of them. [kennedy-2007] argues against a comparison-class
argument of the positive form, as in [klein-1980], and states the positive form with a
standard-fixing function, `⟦pos⟧ = λg.λx. g(x) ⪰ s(g)` ((27)), which needs contextual information
about a domain to fix a threshold: a contextual or necessity standard, or an extreme one beyond
the degrees a context makes salient ([morzycki-2012]). -/
def RequiresComparisonClass (s : PositiveStandard) : Prop :=
  ∃ (D : Type) (_ : LinearOrder D), ∃ U ∈ s.standards D, ¬ IsInvariant U

/-- The scale fixes exactly the endpoint standards. -/
theorem requiresComparisonClass_iff {s : PositiveStandard} :
    s.RequiresComparisonClass ↔ s ≠ .minEndpoint ∧ s ≠ .maxEndpoint := by
  refine ⟨fun ⟨D, _, U, hU, hn⟩ ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro rfl
    obtain ⟨m, hm, rfl⟩ := hU
    exact hn (isInvariant_Ioi_of_isBot hm)
  · rintro rfl
    obtain ⟨m, hm, rfl⟩ := hU
    exact hn (isInvariant_Ici_of_isTop hm)
  · have h0 : ¬ IsInvariant (UpperSet.Ioi (0 : ℤ)) := fun h ↦ by
      have := h (OrderIso.addRight 1)
      rw [UpperSet.map_Ioi] at this
      simpa using (UpperSet.Ioi_strictMono ℤ).injective this
    cases s
    case minEndpoint => exact absurd rfl h₁
    case maxEndpoint => exact absurd rfl h₂
    all_goals exact ⟨ℤ, inferInstance, UpperSet.Ioi 0, ⟨0, .inl rfl⟩, h0⟩

instance : DecidablePred RequiresComparisonClass :=
  fun _ ↦ decidable_of_iff _ requiresComparisonClass_iff.symm

/-- Two kinds of standard are complementary when on every scale a standard of the one and a
standard of the other on the reversed scale, where the antonym measures, partition the degrees,
so that the poles taking them are contradictory, denying one asserting the other
([kennedy-2007] (47)). -/
def Complementary (s t : PositiveStandard) : Prop :=
  ∀ (D : Type) [LinearOrder D], ∀ U ∈ s.standards D, ∀ V ∈ t.standards Dᵒᵈ,
    IsCompl (U : Set D) (OrderDual.toDual ⁻¹' V)

/-- Only the minimum and the maximum standards are complementary: any other pair leaves a gap or
an overlap on some scale. -/
theorem complementary_iff {s t : PositiveStandard} :
    s.Complementary t ↔
      s = .minEndpoint ∧ t = .maxEndpoint ∨ s = .maxEndpoint ∧ t = .minEndpoint := by
  constructor
  · intro h
    -- a standard of each kind on a closed scale and on its reversal, with three degrees as tests
    let rep : PositiveStandard → UpperSet (WithTop (WithBot ℤ))
      | .minEndpoint => .Ioi ⊥
      | .maxEndpoint => .Ici ⊤
      | _ => .Ioi ((0 : ℤ) : WithBot ℤ)
    let drep : PositiveStandard → UpperSet (WithTop (WithBot ℤ))ᵒᵈ
      | .minEndpoint => .Ioi ⊥
      | .maxEndpoint => .Ici ⊤
      | _ => .Ioi (OrderDual.toDual ((0 : ℤ) : WithBot ℤ))
    have hrep (s : PositiveStandard) : rep s ∈ s.standards _ := by
      cases s
      exacts [⟨_, .inl rfl⟩, ⟨⊥, isBot_bot, rfl⟩, ⟨⊤, isTop_top, rfl⟩, ⟨_, .inl rfl⟩,
        ⟨_, .inl rfl⟩]
    have hdrep (t : PositiveStandard) : drep t ∈ t.standards _ := by
      cases t
      exacts [⟨_, .inl rfl⟩, ⟨⊥, isBot_bot, rfl⟩, ⟨⊤, isTop_top, rfl⟩, ⟨_, .inl rfl⟩,
        ⟨_, .inl rfl⟩]
    have hx := fun x ↦ Set.ext_iff.1 (h _ _ (hrep s) _ (hdrep t)).compl_eq x
    have h0 := hx ((0 : ℤ) : WithBot ℤ)
    have h1 := hx ((1 : ℤ) : WithBot ℤ)
    have h2 := hx ((-1 : ℤ) : WithBot ℤ)
    cases s <;> cases t <;>
      simp only [rep, drep, UpperSet.coe_Ioi, UpperSet.coe_Ici, Set.mem_Ioi, Set.mem_Ici,
        Set.mem_compl_iff, Set.mem_preimage] at h0 h1 h2 <;>
      first | (exfalso; revert h0 h1 h2; decide) | simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) D _ U ⟨m, hm, rfl⟩ V ⟨m', hm', rfl⟩
    · have : OrderDual.ofDual m' = m := le_antisymm (OrderDual.toDual_le.1 (hm' _)) (hm _)
      have hV : OrderDual.toDual ⁻¹' (UpperSet.Ici m' : Set _) = Set.Iic m := by
        ext x; simp [← this, OrderDual.le_toDual]
      rw [hV, UpperSet.coe_Ioi, ← Set.compl_Ioi]
      exact isCompl_compl
    · have : OrderDual.ofDual m' = m := le_antisymm (hm _) (OrderDual.le_toDual.1 (hm' _))
      have hV : OrderDual.toDual ⁻¹' (UpperSet.Ioi m' : Set _) = Set.Iio m := by
        ext x; simp [← this, OrderDual.lt_toDual]
      rw [hV, UpperSet.coe_Ici, ← Set.compl_Ici]
      exact isCompl_compl

instance : DecidableRel Complementary := fun _ _ ↦ decidable_of_iff _ complementary_iff.symm

end PositiveStandard

/-! ### Difference functions

The difference function of a measure `μ` at a degree `d` is `Set.projIci d ∘ μ`, which measures on
the ray above `d` and sends every degree at or below `d` to `d`, the derived zero. The ray has a
least degree (`Boundedness.ofOrder_Ici`), so Interpretive Economy admits the minimum standard for
a difference function, giving the truth conditions of a comparative with standard `d`, and the
maximum standard exactly when the scale of `μ` has one. -/

section Difference
variable {α D : Type*} [LinearOrder D] {μ : α → D} {d : D}

/-- The positive form of a difference function at the minimum standard is the comparative with
standard `d` ([kennedy-mcnally-2005], [kennedy-levin-2008] (24)). -/
theorem preimage_projIci_comp_Ioi_bot : (Set.projIci d ∘ μ) ⁻¹' Set.Ioi ⊥ = μ ⁻¹' Set.Ioi d :=
  Set.ext fun _ ↦ Set.bot_lt_projIci

/-- Unless `d` is the greatest degree, the positive form of a difference function at the maximum
standard is that of `μ` itself ([kennedy-levin-2008] fn. 16). -/
theorem preimage_projIci_comp_Ici_top [OrderTop D] (hd : d ≠ ⊤) :
    (Set.projIci d ∘ μ) ⁻¹' Set.Ici ⊤ = μ ⁻¹' Set.Ici ⊤ := by
  ext x
  simp [Set.projIci_eq_top, hd]

end Difference

namespace Boundedness

/-- Interpretive Economy computes truth conditions from conventional meaning where it can,
allowing a contextual standard only where conventional meaning is insufficient ([kennedy-2007]
(66)). The standards a scale itself fixes are those every automorphism of its degrees fixes, and
the endpoint standards are among them (`isInvariant_Ioi_of_isBot`), so a scale admits an endpoint
standard where it has a standard of that kind, and the contextual standard only where it fixes no
standard but the trivial ones. The lexical necessity and extreme standards it never admits. On the
canonical scales the endpoint standards are the only nontrivial invariant ones
(`isInvariant_degreeShape_iff`). -/
def Admits (b : Boundedness) : PositiveStandard → Prop
  | .contextual  => ∀ U : UpperSet b.DegreeShape, IsInvariant U → U = ⊥ ∨ U = ⊤
  | .minEndpoint => (PositiveStandard.minEndpoint.standards b.DegreeShape).Nonempty
  | .maxEndpoint => (PositiveStandard.maxEndpoint.standards b.DegreeShape).Nonempty
  | .necessity   => False
  | .extreme     => False

/-- The contextual standard is admitted exactly on a totally open scale, since a scale with an
endpoint fixes the endpoint standard ([kennedy-2007] (66)). -/
@[simp] theorem admits_contextual {b : Boundedness} : b.Admits .contextual ↔ b = .open_ := by
  rw [Admits, forall_isInvariant_iff_of_exists_orderIso b.exists_not_isBot_not_isTop
    b.exists_orderIso_degreeShape]
  simp only [← not_exists, exists_isBot_degreeShape, exists_isTop_degreeShape]
  cases b <;> decide

@[simp] theorem admits_minEndpoint {b : Boundedness} : b.Admits .minEndpoint ↔ b.HasMin := by
  rw [← exists_isBot_degreeShape]
  exact ⟨fun ⟨_, m, hm, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨_, m, hm, rfl⟩⟩

@[simp] theorem admits_maxEndpoint {b : Boundedness} : b.Admits .maxEndpoint ↔ b.HasMax := by
  rw [← exists_isTop_degreeShape]
  exact ⟨fun ⟨_, m, hm, _⟩ ↦ ⟨m, hm⟩, fun ⟨m, hm⟩ ↦ ⟨_, m, hm, rfl⟩⟩

@[simp] theorem not_admits_necessity (b : Boundedness) : ¬ b.Admits .necessity := id

@[simp] theorem not_admits_extreme (b : Boundedness) : ¬ b.Admits .extreme := id

instance (b : Boundedness) : (s : PositiveStandard) → Decidable (b.Admits s)
  | .contextual  => decidable_of_iff _ admits_contextual.symm
  | .minEndpoint => decidable_of_iff _ admits_minEndpoint.symm
  | .maxEndpoint => decidable_of_iff _ admits_maxEndpoint.symm
  | .necessity   => isFalse id
  | .extreme     => isFalse id

theorem not_admits_contextual_of_ne_open {b : Boundedness} (h : b ≠ .open_) :
    ¬ b.Admits .contextual :=
  mt admits_contextual.1 h

/-- The default standard of a scale is the one Interpretive Economy forces where it admits only
one, and the maximum on a totally closed scale, since a maximum standard entails a minimum one. -/
def defaultStandard : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerClosed => .minEndpoint
  | .upperClosed => .maxEndpoint
  | .closed       => .maxEndpoint

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

/-- A scale is relative when its default standard needs a comparison class, which is to say when
it is open, as for *tall*, *expensive* and *big*. -/
def IsRelative (b : Boundedness) : Prop := b.defaultStandard.RequiresComparisonClass

instance : DecidablePred IsRelative :=
  fun b ↦ inferInstanceAs (Decidable b.defaultStandard.RequiresComparisonClass)

/-- A scale with a least degree adjoined admits the minimum standard, and the maximum iff the
original scale has one ([kennedy-levin-2008] (23), (25)). -/
theorem admits_withMin_iff {b : Boundedness} {s : PositiveStandard} :
    b.withMin.Admits s ↔ s = .minEndpoint ∨ s = .maxEndpoint ∧ b.HasMax := by
  cases b <;> cases s <;> simp [withMin, HasMin, HasMax]

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
