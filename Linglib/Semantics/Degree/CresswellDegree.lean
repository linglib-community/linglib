module

public import Mathlib.Order.Comparable
public import Mathlib.Order.Concept
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Setoid.Basic
public import Linglib.Core.Order.PreorderLattice

/-!
# Degrees as equivalence classes

Cresswell builds degrees from a comparison instead of assuming them. Let `φ` be a relation on `E`,
with `φ a b` read as *`a` exceeds `b`*. The trace of `φ` is the preorder in which `a` is at most
`b` when `b` exceeds whatever `a` exceeds and whatever exceeds `b` exceeds `a`,
`(∀ c, φ a c → φ b c) ∧ ∀ c, φ c b → φ c a`. Two things are indistinguishable under `φ` when each
is at most the other, that is, when they stand in `φ` to the same things on both sides. The
degrees of `φ` are the classes of indistinguishable things, the antisymmetrization of the trace,
and so they are partially ordered whatever `φ` is. The comparison also induces a relation between
degrees, `⟦a⟧ >[φ] ⟦b⟧` when `φ a b`.

When `φ` is a strict weak order the trace is *does not exceed*, the degrees are linearly ordered,
the induced relation is their strict order, and being indistinguishable is being incomparable. A
relation is a strict weak order exactly when some measure into a linear order represents it; the
trace is then the order of the measure and the degrees are the values of the measure, in their
order.

## Main definitions

* `Preorder.trace φ`: the trace of the comparison `φ`.
* `cresswellSetoid φ`: indistinguishability under `φ`, the equivalence of the trace.
* `CresswellDegree φ`: the degrees of `φ`, with the order of the trace.
* `x >[φ] y`, notation of the scope `CresswellDegree`: the relation `φ` induces between its
  degrees.
* `CresswellDegree.lift`: the order embedding of the degrees of `φ` into a linear order in which
  a measure represents `φ`.
* `CresswellDegree.orderIsoRange`: the degrees of `φ` are the values of a measure that
  represents it.

## Main results

* `Preorder.trace_eq_lift`: the trace is the pullback of inclusion along the two polars of a
  point, what it exceeds and what exceeds it.
* `Preorder.le_trace_iff`: a preorder refines the trace exactly when the comparison is monotone
  for it, so the trace is the coarsest such preorder.
* `cresswellSetoid_iff`: two things are indistinguishable exactly when they stand in `φ` to the
  same things on the left and on the right.
* `le_cresswellSetoid_iff`: an equivalence relation refines indistinguishability exactly when
  the comparison respects it.
* `Preorder.trace_le_iff_not`, `CresswellDegree.lt_iff`: on a strict weak order the trace is
  *does not exceed*, and the induced relation is the strict order of the degrees.
* `CresswellDegree.total_and_forall_mk_lt_mk_iff`: the degrees are linearly ordered with the
  comparison as their strict order exactly when the comparison is a strict weak order.
* `asymm_and_isOrderConnected_iff_exists_measure`: a relation is a strict weak order exactly
  when a measure into a linear order represents it.
* `Preorder.trace_le_iff_of_lt`, `Preorder.trace_le_iff_of_le`: the trace of a comparison read
  off a measure into a linear order, strictly or not, is the order of the measure.
* `Preorder.trace_le_iff_of_isPreorder`: the trace of a preorder is the preorder.

## Implementation notes

Cresswell's relata are pairs of a thing and a possible world; here they are the members of any
type `E`, so a comparison across worlds takes `E` to be such pairs.

Cresswell defines the equivalence and a relation between its classes, `⟦a⟧ > ⟦b⟧` when `φ a b`.
Here the preorder is defined first and the equivalence is its symmetric part, so that the degrees
are mathlib's `Antisymmetrization` and carry its order for every `φ`. Cresswell's relation between
classes is kept beside the order, as `Quotient.lift₂ φ` under the notation `x >[φ] y`, and not as
the `<` of the degrees: the two agree when `φ` is a strict weak order (`CresswellDegree.lt_iff`),
and otherwise the trace can be a linear order of which `φ` is only a part.

`Preorder.trace` is [bouyssou-marchant-2011]'s trace of a relation on a set, the intersection of
its left and right traces, written here with the lower thing on the left. It is a term and not an
instance, since `E` may carry an order of its own, and it is defined by its unfolded condition
and not as `Preorder.lift` along the polars, so that its proofs take the two conjuncts apart; the
two agree by `Preorder.trace_eq_lift`.

A strict weak order is stated as `[Std.Asymm φ] [IsOrderConnected E φ]`, asymmetry and negative
transitivity, and not with `IsStrictWeakOrder`. The two conditions come from different
assumptions in the accounts that supply them, mathlib derives `IsStrictWeakOrder` from them
(`isStrictWeakOrder_of_isOrderConnected`) and not conversely, and `<` on a linear order has both.

A measure `μ` represents `φ` when `φ a b ↔ μ b < μ a`. The hypothesis is a pointwise
equivalence, not an equation between `φ` and a relation pulled back along `μ`, so that a lemma
about `φ` can supply it.

## TODO

* The trace is total exactly when the relation is Ferrers and semitransitive
  ([bouyssou-marchant-2011]), so the degrees of a semiorder are linearly ordered although the
  comparison is not their strict order.

## References

* [cresswell-1976]
* [bale-2008]
* [bouyssou-marchant-2011]
-/

@[expose] public section

open Function

variable {E D : Type*} {φ : E → E → Prop} {a b : E}

/-! ### The trace of a comparison -/

namespace Preorder

/-- The trace of a comparison `φ` ranks `a` at most `b` when `b` exceeds whatever `a` exceeds and
whatever exceeds `b` exceeds `a`. -/
@[reducible] def trace (φ : E → E → Prop) : Preorder E where
  le a b := (∀ c, φ a c → φ b c) ∧ ∀ c, φ c b → φ c a
  le_refl _ := ⟨fun _ ↦ id, fun _ ↦ id⟩
  le_trans _ _ _ h₁ h₂ := ⟨fun c h ↦ h₂.1 c (h₁.1 c h), fun c h ↦ h₁.2 c (h₂.2 c h)⟩

instance : IsPreorder E (trace φ).le := @instIsPreorderLe E (trace φ)

theorem trace_le_iff : (trace φ).le a b ↔ (∀ c, φ a c → φ b c) ∧ ∀ c, φ c b → φ c a :=
  Iff.rfl

/-- The trace is the pullback of inclusion along the two polars of a point, what it exceeds and,
in the reverse order, what exceeds it. -/
theorem trace_eq_lift (φ : E → E → Prop) :
    trace φ = Preorder.lift fun a ↦ (upperPolar φ {a}, OrderDual.toDual (lowerPolar φ {a})) :=
  Preorder.ext fun a b ↦
    ⟨fun h ↦ ⟨fun c hc ↦ by rintro _ rfl; exact h.1 c (hc (Set.mem_singleton a)),
        fun c hc ↦ by rintro _ rfl; exact h.2 c (hc (Set.mem_singleton b))⟩,
      fun h ↦ ⟨fun c hc ↦ h.1 (by rintro _ rfl; exact hc) (Set.mem_singleton b),
        fun c hc ↦ h.2 (by rintro _ rfl; exact hc) (Set.mem_singleton a)⟩⟩

/-- A preorder refines the trace of a comparison exactly when the comparison is monotone for it:
raising the thing that exceeds, or lowering the thing exceeded, preserves the comparison. -/
theorem le_trace_iff {p : Preorder E} :
    p ≤ trace φ ↔ ∀ ⦃a a' b b'⦄, p.le a a' → p.le b' b → φ a b → φ a' b' :=
  ⟨fun h _ a' b _ ha hb hab ↦ (h hb).2 a' ((h ha).1 b hab),
    fun h _ _ hab ↦ ⟨fun c ↦ h hab (p.le_refl c), fun c ↦ h (p.le_refl c) hab⟩⟩

/-- The trace of the converse comparison is the dual of the trace. -/
theorem trace_swap_le_iff : (trace (swap φ)).le a b ↔ (trace φ).le b a :=
  and_comm

/-- The trace of a preorder, read as *at least*, is the preorder. -/
theorem trace_le_iff_of_isPreorder (r : E → E → Prop) [IsPreorder E r] :
    (trace r).le a b ↔ r b a :=
  ⟨fun h ↦ h.1 a (refl a), fun h ↦ ⟨fun _ ↦ _root_.trans h, fun _ ↦ (_root_.trans · h)⟩⟩

section Scale

variable [IsOrderConnected E φ]

/-- On a strict weak order, one thing is at most another exactly when it does not exceed it. -/
theorem trace_le_iff_not [Std.Irrefl φ] : (trace φ).le a b ↔ ¬ φ a b :=
  ⟨fun h hab ↦ irrefl b (h.1 b hab), fun h ↦
    ⟨fun c hac ↦ (IsOrderConnected.conn a b c hac).resolve_left h,
      fun c hcb ↦ (IsOrderConnected.conn c a b hcb).resolve_right h⟩⟩

/-- A strict weak order is the strict part of its trace. -/
theorem trace_lt_iff [Std.Asymm φ] : (trace φ).lt a b ↔ φ b a := by
  rw [(trace φ).lt_iff_le_not_ge, trace_le_iff_not, trace_le_iff_not, not_not]
  exact ⟨And.right, fun h ↦ ⟨asymm h, h⟩⟩

end Scale

section Measure

variable [LinearOrder D] {μ : E → D}

/-- The trace of a comparison that a measure into a linear order represents is the order of the
measure. -/
theorem trace_le_iff_of_lt (h : ∀ a b, φ a b ↔ μ b < μ a) : (trace φ).le a b ↔ μ a ≤ μ b :=
  ⟨fun h' ↦ not_lt.1 fun hlt ↦ lt_irrefl _ ((h b b).1 (h'.1 b ((h a b).2 hlt))), fun hle ↦
    ⟨fun c hac ↦ (h b c).2 (((h a c).1 hac).trans_le hle),
      fun c hcb ↦ (h c a).2 (hle.trans_lt ((h c b).1 hcb))⟩⟩

/-- The non-strict comparison read off a measure has the same trace as the strict one. -/
theorem trace_le_iff_of_le (h : ∀ a b, φ a b ↔ μ b ≤ μ a) : (trace φ).le a b ↔ μ a ≤ μ b :=
  ⟨fun h' ↦ (h b a).1 (h'.1 a ((h a a).2 le_rfl)), fun hle ↦
    ⟨fun c hac ↦ (h b c).2 (((h a c).1 hac).trans hle),
      fun c hcb ↦ (h c a).2 (hle.trans ((h c b).1 hcb))⟩⟩

end Measure

end Preorder

/-! ### Indistinguishability -/

/-- Two things are indistinguishable under a comparison `φ` when each is at most the other in
the trace of `φ`: [cresswell-1976]'s equivalence (4.1), by `cresswellSetoid_iff`. -/
def cresswellSetoid (φ : E → E → Prop) : Setoid E :=
  AntisymmRel.setoid E (Preorder.trace φ).le

/-- Two things are indistinguishable exactly when they stand in the comparison to the same
things on the left and on the right, [cresswell-1976] (4.1). -/
theorem cresswellSetoid_iff :
    cresswellSetoid φ a b ↔ (∀ c, φ a c ↔ φ b c) ∧ ∀ c, φ c a ↔ φ c b :=
  ⟨fun h ↦ ⟨fun c ↦ ⟨h.1.1 c, h.2.1 c⟩, fun c ↦ ⟨h.2.2 c, h.1.2 c⟩⟩,
    fun h ↦ ⟨⟨fun c ↦ (h.1 c).1, fun c ↦ (h.2 c).2⟩, ⟨fun c ↦ (h.1 c).2, fun c ↦ (h.2 c).1⟩⟩⟩

/-- An equivalence relation refines indistinguishability exactly when the comparison respects
it, so indistinguishability is the greatest equivalence relation the comparison respects. -/
theorem le_cresswellSetoid_iff {s : Setoid E} :
    s ≤ cresswellSetoid φ ↔ ∀ ⦃a a' b b'⦄, s a a' → s b b' → (φ a b ↔ φ a' b') :=
  ⟨fun h _ a' b _ ha hb ↦
    ((cresswellSetoid_iff.1 (h ha)).1 b).trans ((cresswellSetoid_iff.1 (h hb)).2 a'),
    fun h _ _ hab ↦ cresswellSetoid_iff.2 ⟨fun c ↦ h hab (s.refl c), fun c ↦ h (s.refl c) hab⟩⟩

/-- A comparison does not tell indistinguishable things apart, [cresswell-1976]'s consistency
proof for (4.2). -/
theorem rel_eq_of_cresswellSetoid (φ : E → E → Prop) (a₁ b₁ a₂ b₂ : E)
    (ha : cresswellSetoid φ a₁ a₂) (hb : cresswellSetoid φ b₁ b₂) : φ a₁ b₁ = φ a₂ b₂ :=
  propext (le_cresswellSetoid_iff.1 le_rfl ha hb)

/-- On a strict weak order, being indistinguishable is being incomparable. -/
theorem cresswellSetoid_iff_incompRel [Std.Irrefl φ] [IsOrderConnected E φ] :
    cresswellSetoid φ a b ↔ IncompRel φ a b :=
  and_congr Preorder.trace_le_iff_not Preorder.trace_le_iff_not

/-- On a preorder, indistinguishability is mutual comparison, the relation mathlib's
`Antisymmetrization` quotients by, as [bale-2008] n. 7 observes. -/
theorem cresswellSetoid_eq_antisymmRel (r : E → E → Prop) [IsPreorder E r] :
    cresswellSetoid r = AntisymmRel.setoid E r :=
  Setoid.ext fun _ _ ↦ (and_congr (Preorder.trace_le_iff_of_isPreorder r)
    (Preorder.trace_le_iff_of_isPreorder r)).trans and_comm

/-- On a connected preorder, a comparison and its strict part give the same degrees. -/
theorem cresswellSetoid_lt_eq_le [Preorder E] [Std.Total (α := E) (· ≤ ·)] :
    cresswellSetoid ((· < ·) : E → E → Prop) = cresswellSetoid (· ≤ ·) := by
  rw [cresswellSetoid_eq_antisymmRel (· ≤ ·)]
  refine Setoid.ext fun a b ↦ cresswellSetoid_iff.trans
    ⟨fun h ↦ ⟨by_contra fun hab ↦ ?_, by_contra fun hba ↦ ?_⟩,
      fun h ↦ ⟨fun _ ↦ h.lt_congr_left, fun _ ↦ h.lt_congr_right⟩⟩
  · exact lt_irrefl b ((h.2 b).1 (lt_of_le_not_ge ((total_of (· ≤ ·) a b).resolve_left hab) hab))
  · exact lt_irrefl b ((h.1 b).1 (lt_of_le_not_ge ((total_of (· ≤ ·) b a).resolve_left hba) hba))

section Measure

variable [LinearOrder D] {μ : E → D}

/-- Under a comparison that a measure into a linear order represents, two things are
indistinguishable exactly when they measure the same. -/
theorem cresswellSetoid_eq_ker_of_lt (h : ∀ a b, φ a b ↔ μ b < μ a) :
    cresswellSetoid φ = Setoid.ker μ :=
  Setoid.ext fun _ _ ↦ (and_congr (Preorder.trace_le_iff_of_lt h)
    (Preorder.trace_le_iff_of_lt h)).trans le_antisymm_iff.symm

/-- The non-strict comparison read off a measure has the same degrees as the strict one. -/
theorem cresswellSetoid_eq_ker_of_le (h : ∀ a b, φ a b ↔ μ b ≤ μ a) :
    cresswellSetoid φ = Setoid.ker μ :=
  Setoid.ext fun _ _ ↦ (and_congr (Preorder.trace_le_iff_of_le h)
    (Preorder.trace_le_iff_of_le h)).trans le_antisymm_iff.symm

end Measure

/-! ### Degrees -/

/-- The degrees of a comparison are the classes of indistinguishable things. -/
abbrev CresswellDegree (φ : E → E → Prop) : Type _ :=
  Quotient (cresswellSetoid φ)

namespace CresswellDegree

/-- The degrees of a comparison are partially ordered by its trace, as the antisymmetrization of
a preorder is. -/
instance : PartialOrder (CresswellDegree φ) :=
  @instPartialOrderAntisymmetrization E (Preorder.trace φ)

theorem mk_le_mk : (⟦a⟧ : CresswellDegree φ) ≤ ⟦b⟧ ↔ (Preorder.trace φ).le a b :=
  Iff.rfl

/-- `x >[φ] y` is the relation a comparison `φ` induces between its degrees, holding of the
degrees of `a` and `b` when `φ a b` ([cresswell-1976] (4.2)). -/
scoped notation:50 x " >[" φ "] " y => Quotient.lift₂ φ (rel_eq_of_cresswellSetoid φ) x y

theorem mk_rel_mk : ((⟦a⟧ : CresswellDegree φ) >[φ] ⟦b⟧) ↔ φ a b :=
  Iff.rfl

/-! ### Scales -/

section Scale

variable [Std.Asymm φ] [IsOrderConnected E φ]

theorem mk_le_mk_iff_not : (⟦a⟧ : CresswellDegree φ) ≤ ⟦b⟧ ↔ ¬ φ a b :=
  Preorder.trace_le_iff_not

@[simp] theorem mk_lt_mk : (⟦b⟧ : CresswellDegree φ) < ⟦a⟧ ↔ φ a b :=
  Preorder.trace_lt_iff

/-- On a strict weak order the relation the comparison induces between its degrees is their
strict order. -/
theorem lt_iff {x y : CresswellDegree φ} : y < x ↔ x >[φ] y :=
  Quotient.inductionOn₂ x y fun _ _ ↦ mk_lt_mk

theorem mk_eq_mk_iff_incompRel : (⟦a⟧ : CresswellDegree φ) = ⟦b⟧ ↔ IncompRel φ a b :=
  Quotient.eq.trans cresswellSetoid_iff_incompRel

instance : Std.Total (α := CresswellDegree φ) (· ≤ ·) :=
  ⟨Quotient.ind₂ fun a b ↦ (em (φ a b)).symm.imp mk_le_mk_iff_not.2
    fun h ↦ mk_le_mk_iff_not.2 (asymm h)⟩

/-- On a strict weak order the degrees are linearly ordered, as mathlib's `Antisymmetrization` is
on a total preorder. -/
instance [DecidableRel φ] : LinearOrder (CresswellDegree φ) where
  le_total := total_of _
  toDecidableLE x y := Quotient.recOnSubsingleton₂ x y fun a b ↦
    decidable_of_iff (¬ φ a b) mk_le_mk_iff_not.symm

end Scale

/-- The degrees of a comparison are linearly ordered with the induced relation as their strict
order exactly when the comparison is a strict weak order. -/
theorem total_and_forall_mk_lt_mk_iff :
    (Std.Total (α := CresswellDegree φ) (· ≤ ·) ∧
        ∀ a b, (⟦b⟧ : CresswellDegree φ) < ⟦a⟧ ↔ φ a b) ↔
      Std.Asymm φ ∧ IsOrderConnected E φ := by
  refine ⟨fun ⟨_, h⟩ ↦ ⟨⟨fun a b hab hba ↦ lt_asymm ((h a b).2 hab) ((h b a).2 hba)⟩,
    ⟨fun a b c hac ↦ ?_⟩⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, fun _ _ ↦ mk_lt_mk⟩⟩
  by_cases hab : (⟦a⟧ : CresswellDegree φ) ≤ ⟦b⟧
  · exact .inr ((h b c).1 (((h a c).2 hac).trans_le hab))
  · exact .inl ((h a b).1 (lt_of_le_not_ge ((total_of (· ≤ ·) _ _).resolve_left hab) hab))

/-! ### Measures -/

section Measure

variable [LinearOrder D]

/-- The degrees of a comparison embed in any linear order in which a measure represents the
comparison, the degree of `a` going to the measure of `a`. -/
def lift (μ : E → D) (h : ∀ a b, φ a b ↔ μ b < μ a) : CresswellDegree φ ↪o D :=
  .ofMapLEIff (Quotient.lift μ fun _ _ hab ↦ (cresswellSetoid_eq_ker_of_lt h).le hab) <|
    Quotient.ind₂ fun _ _ ↦ (Preorder.trace_le_iff_of_lt h).symm

@[simp]
theorem lift_mk (μ : E → D) (h : ∀ a b, φ a b ↔ μ b < μ a) (a : E) : lift μ h ⟦a⟧ = μ a :=
  rfl

/-- The degrees of a comparison that a measure represents are the values of the measure, in
their order. -/
noncomputable def orderIsoRange (μ : E → D) (h : ∀ a b, φ a b ↔ μ b < μ a) :
    CresswellDegree φ ≃o Set.range μ :=
  (lift μ h).orderIso.trans (Set.orderIsoOfEq _ _ (Set.range_quot_lift _))

@[simp]
theorem coe_orderIsoRange_mk (μ : E → D) (h : ∀ a b, φ a b ↔ μ b < μ a) (a : E) :
    (orderIsoRange μ h ⟦a⟧ : D) = μ a :=
  rfl

end Measure

end CresswellDegree

/-- A relation is a strict weak order exactly when some measure into a linear order represents
it, and its degrees are then such a measure. -/
theorem asymm_and_isOrderConnected_iff_exists_measure.{u} {E : Type u} {φ : E → E → Prop} :
    Std.Asymm φ ∧ IsOrderConnected E φ ↔
      ∃ (D : Type u) (_ : LinearOrder D) (μ : E → D), ∀ a b, φ a b ↔ μ b < μ a := by
  classical
  refine ⟨fun ⟨_, _⟩ ↦ ⟨CresswellDegree φ, inferInstance, Quotient.mk _,
    fun _ _ ↦ CresswellDegree.mk_lt_mk.symm⟩, ?_⟩
  rintro ⟨D, _, μ, h⟩
  exact ⟨⟨fun a b hab hba ↦ lt_asymm ((h a b).1 hab) ((h b a).1 hba)⟩,
    ⟨fun a b c hac ↦ (lt_or_ge (μ b) (μ a)).imp (h a b).2 fun hle ↦
      (h b c).2 (((h a c).1 hac).trans_le hle)⟩⟩
