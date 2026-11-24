module

public import Mathlib.Order.Comparable
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Setoid.Basic

/-!
# Degrees as equivalence classes

Cresswell builds degrees from a comparison instead of assuming them. Let `φ` be a relation on `E`,
with `φ a b` read as *`a` exceeds `b`*. Two things are indistinguishable under `φ` when they
stand in `φ` to the same things on both sides,
`(∀ c, φ a c ↔ φ b c) ∧ (∀ c, φ c a ↔ φ c b)`. The degrees of `φ` are the classes of
indistinguishable things, and `φ` induces a comparison on them, `⟦b⟧ < ⟦a⟧ ↔ φ a b`.

Indistinguishability is the greatest equivalence relation that `φ` respects, so the degrees are
the coarsest quotient of `E` on which the comparison is still defined. The degrees form a scale,
a strict total order, exactly when `φ` is a strict weak order, and being indistinguishable is
then being incomparable. A relation is a strict weak order exactly when some measure into a
linear order represents it, and its degrees are then the values of any such measure, in their
order.

## Main definitions

* `cresswellSetoid φ`: indistinguishability under the comparison `φ`.
* `CresswellDegree φ`: the degrees of `φ`, the quotient by indistinguishability, with the
  comparison `φ` induces on them.
* `CresswellDegree.lift`: the order embedding of the degrees of `φ` into a linear order in which
  a measure represents `φ`.
* `CresswellDegree.orderIsoRange`: the degrees of `φ` are the values of a measure that
  represents it.

## Main results

* `le_cresswellSetoid_iff`: an equivalence relation refines indistinguishability exactly when
  the comparison respects it.
* `cresswellSetoid_iff_incompRel`: on a strict weak order, being indistinguishable is being
  incomparable.
* `CresswellDegree.isStrictTotalOrder_lt_iff`: the degrees form a scale exactly when the
  comparison is a strict weak order.
* `asymm_and_isOrderConnected_iff_exists_measure`: a relation is a strict weak order exactly
  when a measure into a linear order represents it.
* `cresswellSetoid_eq_ker_of_lt`, `cresswellSetoid_eq_ker_of_le`: under a comparison read off a
  measure into a linear order, strictly or not, two things are indistinguishable exactly when
  they measure the same.
* `cresswellSetoid_eq_antisymmRel`: on a preorder, indistinguishability is mutual comparison,
  the relation mathlib's `Antisymmetrization` quotients by.
* `cresswellSetoid_lt_eq_le`: a connected preorder and its strict part give the same degrees.

## Implementation notes

Cresswell's relata are pairs of a thing and a possible world; here they are the members of any
type `E`, so a comparison across worlds takes `E` to be such pairs.

A strict weak order is stated as `[Std.Asymm φ] [IsOrderConnected E φ]`, asymmetry and negative
transitivity, and not with `IsStrictWeakOrder`. The two conditions come from different
assumptions in the accounts that supply them, mathlib derives `IsStrictWeakOrder` from them
(`isStrictWeakOrder_of_isOrderConnected`) and not conversely, and `<` on a linear order has both.

The induced comparison is written `<` because the comparatives it serves are strict. It is
defined for every `φ`, as Cresswell's is, and is irreflexive only when `φ` is; `≤` is its
reflexive closure and is defined once `φ` is a strict weak order. A reflexive `φ` is better
served by mathlib's order on `Antisymmetrization`.

A measure `μ` represents `φ` when `φ a b ↔ μ b < μ a`. The hypothesis is a pointwise
equivalence, not an equation between `φ` and a relation pulled back along `μ`, so that a lemma
about `φ` can supply it.

## References

* [cresswell-1976]
* [bale-2008]
-/

@[expose] public section

open Function

variable {E D : Type*} {φ : E → E → Prop} {a b : E}

/-- Two things are indistinguishable under a comparison `φ` when they stand in `φ` to the same
things on the left and on the right, [cresswell-1976] (4.1). -/
def cresswellSetoid (φ : E → E → Prop) : Setoid E where
  r a b := (∀ c, φ a c ↔ φ b c) ∧ (∀ c, φ c a ↔ φ c b)
  iseqv :=
    ⟨fun _ ↦ ⟨fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩,
     fun h ↦ ⟨fun c ↦ (h.1 c).symm, fun c ↦ (h.2 c).symm⟩,
     fun h₁ h₂ ↦ ⟨fun c ↦ (h₁.1 c).trans (h₂.1 c), fun c ↦ (h₁.2 c).trans (h₂.2 c)⟩⟩

/-- An equivalence relation refines indistinguishability exactly when the comparison respects
it, so indistinguishability is the greatest equivalence relation the comparison respects. -/
theorem le_cresswellSetoid_iff {s : Setoid E} :
    s ≤ cresswellSetoid φ ↔ ∀ ⦃a a' b b'⦄, s a a' → s b b' → (φ a b ↔ φ a' b') :=
  ⟨fun h _ a' b _ ha hb ↦ ((h ha).1 b).trans ((h hb).2 a'),
    fun h _ _ hab ↦ ⟨fun c ↦ h hab (s.refl c), fun c ↦ h (s.refl c) hab⟩⟩

theorem cresswellSetoid_swap : cresswellSetoid (swap φ) = cresswellSetoid φ :=
  Setoid.ext fun _ _ ↦ and_comm

/-- Things that a map sends to the same value are indistinguishable under any comparison read
off the map. -/
theorem ker_le_cresswellSetoid {s : D → D → Prop} {μ : E → D} (h : ∀ a b, φ a b ↔ s (μ a) (μ b)) :
    Setoid.ker μ ≤ cresswellSetoid φ :=
  le_cresswellSetoid_iff.2 fun a a' b b' (ha : μ a = μ a') (hb : μ b = μ b') ↦ by
    rw [h, h, ha, hb]

/-- The degrees of a comparison are the classes of indistinguishable things. -/
abbrev CresswellDegree (φ : E → E → Prop) : Type _ :=
  Quotient (cresswellSetoid φ)

namespace CresswellDegree

/-- The comparison a relation induces on its degrees, `⟦b⟧ < ⟦a⟧` iff `φ a b`; well-definedness
is [cresswell-1976]'s own consistency proof for (4.2). -/
instance : LT (CresswellDegree φ) :=
  ⟨Quotient.lift₂ (fun a b ↦ φ b a) fun _ _ _ _ ha hb ↦
    propext (le_cresswellSetoid_iff.1 le_rfl hb ha)⟩

/-- The degree of `a` exceeds that of `b` exactly when `φ a b`, [cresswell-1976] (4.2). -/
@[simp] theorem mk_lt_mk : (⟦b⟧ : CresswellDegree φ) < ⟦a⟧ ↔ φ a b :=
  Iff.rfl

instance [DecidableRel φ] : DecidableRel ((· < ·) : CresswellDegree φ → CresswellDegree φ → Prop) :=
  fun x y ↦ Quotient.recOnSubsingleton₂ x y fun _ _ ↦ inferInstanceAs (Decidable (φ _ _))

end CresswellDegree

/-! ### Scales

A strict weak order is an asymmetric relation that is order connected: whenever `φ a c`, any `b`
has `φ a b` or `φ b c`. -/

section Scale

variable [IsOrderConnected E φ]

/-- On a strict weak order, being indistinguishable is being incomparable. -/
theorem cresswellSetoid_iff_incompRel [Std.Irrefl φ] :
    cresswellSetoid φ a b ↔ IncompRel φ a b :=
  ⟨fun h ↦ ⟨fun hab ↦ irrefl b ((h.1 b).1 hab), fun hba ↦ irrefl b ((h.2 b).1 hba)⟩,
    fun ⟨hab, hba⟩ ↦
      ⟨fun c ↦ ⟨fun h ↦ (IsOrderConnected.conn a b c h).resolve_left hab,
        fun h ↦ (IsOrderConnected.conn b a c h).resolve_left hba⟩,
      fun c ↦ ⟨fun h ↦ (IsOrderConnected.conn c b a h).resolve_right hba,
        fun h ↦ (IsOrderConnected.conn c a b h).resolve_right hab⟩⟩⟩

namespace CresswellDegree

theorem mk_eq_mk [Std.Irrefl φ] : (⟦a⟧ : CresswellDegree φ) = ⟦b⟧ ↔ IncompRel φ a b :=
  Quotient.eq.trans cresswellSetoid_iff_incompRel

variable [Std.Asymm φ]

instance : IsStrictTotalOrder (CresswellDegree φ) (· < ·) where
  irrefl := Quotient.ind fun _ h ↦ asymm (r := φ) h h
  trans x y z := Quotient.inductionOn₃ x y z fun a b c hab hbc ↦
    (IsOrderConnected.conn c a b hbc).resolve_right (asymm (r := φ) hab)
  trichotomous x y := Quotient.inductionOn₂ x y fun _ _ hab hba ↦ mk_eq_mk.2 ⟨hba, hab⟩

/-- The degrees of a strict weak order are partially ordered by the reflexive closure of the
induced comparison. -/
instance : PartialOrder (CresswellDegree φ) :=
  partialOrderOfSO (· < ·)

/-- On a strict weak order the degrees are linearly ordered, as mathlib's `Antisymmetrization` is
on a total preorder. -/
instance [DecidableRel φ] : LinearOrder (CresswellDegree φ) :=
  linearOrderOfSTO (· < ·)

theorem mk_le_mk : (⟦a⟧ : CresswellDegree φ) ≤ ⟦b⟧ ↔ ¬ φ a b :=
  ⟨fun h ↦ h.elim (fun h ↦ (mk_eq_mk.1 h).1) (asymm (r := φ)),
    fun h ↦ or_iff_not_imp_right.2 fun h' ↦ mk_eq_mk.2 ⟨h, h'⟩⟩

end CresswellDegree

end Scale

/-- The degrees of a comparison form a scale exactly when the comparison is a strict weak
order. -/
theorem CresswellDegree.isStrictTotalOrder_lt_iff :
    IsStrictTotalOrder (CresswellDegree φ) (· < ·) ↔ Std.Asymm φ ∧ IsOrderConnected E φ :=
  ⟨fun _ ↦
    ⟨⟨fun a b hab hba ↦ asymm_of (· < ·) (a := (⟦b⟧ : CresswellDegree φ)) (b := ⟦a⟧) hab hba⟩,
      ⟨fun a b c hac ↦ (IsOrderConnected.conn (lt := (· < ·)) (⟦c⟧ : CresswellDegree φ) ⟦b⟧ ⟦a⟧
        hac).symm⟩⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

/-! ### Measures -/

section Measure

variable [LinearOrder D] {μ : E → D}

/-- Under a comparison that a measure into a linear order represents, two things are
indistinguishable exactly when they measure the same. -/
theorem cresswellSetoid_eq_ker_of_lt (h : ∀ a b, φ a b ↔ μ b < μ a) :
    cresswellSetoid φ = Setoid.ker μ :=
  le_antisymm (fun a b hab ↦ le_antisymm
    (not_lt.1 fun hlt ↦ lt_irrefl _ ((h b b).1 ((hab.1 b).1 ((h a b).2 hlt))))
    (not_lt.1 fun hlt ↦ lt_irrefl _ ((h b b).1 ((hab.2 b).1 ((h b a).2 hlt)))))
    (ker_le_cresswellSetoid (s := (· > ·)) h)

/-- The non-strict comparison read off a measure has the same degrees as the strict one. -/
theorem cresswellSetoid_eq_ker_of_le (h : ∀ a b, φ a b ↔ μ b ≤ μ a) :
    cresswellSetoid φ = Setoid.ker μ :=
  le_antisymm (fun a b hab ↦ le_antisymm ((h b a).1 ((hab.2 b).2 ((h b b).2 le_rfl)))
    ((h a b).1 ((hab.1 b).2 ((h b b).2 le_rfl)))) (ker_le_cresswellSetoid (s := (· ≥ ·)) h)

/-- A relation is a strict weak order exactly when some measure into a linear order represents
it, and its degrees are then such a measure. -/
theorem asymm_and_isOrderConnected_iff_exists_measure.{u} {E : Type u} {φ : E → E → Prop} :
    Std.Asymm φ ∧ IsOrderConnected E φ ↔
      ∃ (D : Type u) (_ : LinearOrder D) (μ : E → D), ∀ a b, φ a b ↔ μ b < μ a := by
  classical
  refine ⟨fun ⟨_, _⟩ ↦ ⟨CresswellDegree φ, inferInstance, Quotient.mk _, fun _ _ ↦ .rfl⟩, ?_⟩
  rintro ⟨D, _, μ, h⟩
  exact ⟨⟨fun a b hab hba ↦ lt_asymm ((h a b).1 hab) ((h b a).1 hba)⟩,
    ⟨fun a b c hac ↦ (lt_or_ge (μ b) (μ a)).imp (h a b).2 fun hle ↦
      (h b c).2 (((h a c).1 hac).trans_le hle)⟩⟩

namespace CresswellDegree

variable [Std.Asymm φ] [IsOrderConnected E φ]

/-- The degrees of a comparison embed in any linear order in which a measure represents the
comparison, the degree of `a` going to the measure of `a`. -/
def lift (μ : E → D) (h : ∀ a b, φ a b ↔ μ b < μ a) : CresswellDegree φ ↪o D :=
  .ofMapLEIff (Quotient.lift μ fun _ _ hab ↦ (cresswellSetoid_eq_ker_of_lt h).le hab) <|
    Quotient.ind₂ fun a b ↦ (mk_le_mk.trans ((not_congr (h a b)).trans not_lt)).symm

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

end CresswellDegree

end Measure

/-! ### Preorders -/

/-- On a preorder, indistinguishability is mutual comparison, the relation mathlib's
`Antisymmetrization` quotients by, as [bale-2008] n. 7 observes. -/
theorem cresswellSetoid_eq_antisymmRel (r : E → E → Prop) [IsPreorder E r] :
    cresswellSetoid r = AntisymmRel.setoid E r :=
  Setoid.ext fun a b ↦ ⟨fun h ↦ ⟨(h.1 b).2 (refl b), (h.1 a).1 (refl a)⟩, fun h ↦
    ⟨fun _ ↦ ⟨_root_.trans h.2, _root_.trans h.1⟩,
      fun _ ↦ ⟨(_root_.trans · h.1), (_root_.trans · h.2)⟩⟩⟩

/-- On a connected preorder, a comparison and its strict part give the same degrees. -/
theorem cresswellSetoid_lt_eq_le [Preorder E] [Std.Total (α := E) (· ≤ ·)] :
    cresswellSetoid ((· < ·) : E → E → Prop) = cresswellSetoid (· ≤ ·) := by
  rw [cresswellSetoid_eq_antisymmRel (· ≤ ·)]
  refine Setoid.ext fun a b ↦ ⟨fun h ↦ ⟨by_contra fun hab ↦ ?_, by_contra fun hba ↦ ?_⟩,
    fun h ↦ ⟨fun _ ↦ h.lt_congr_left, fun _ ↦ h.lt_congr_right⟩⟩
  · exact lt_irrefl b ((h.2 b).1 (lt_of_le_not_ge ((total_of (· ≤ ·) a b).resolve_left hab) hab))
  · exact lt_irrefl b ((h.1 b).1 (lt_of_le_not_ge ((total_of (· ≤ ·) b a).resolve_left hba) hba))
