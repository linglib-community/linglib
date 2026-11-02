module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Comparable
public import Mathlib.Order.Setoid.Basic

/-!
# Degrees as equivalence classes

Cresswell builds degrees from a comparison instead of assuming them. Two things are
indistinguishable under a comparison $φ$ when they stand in $φ$ to the same things on both sides,
the degrees are the classes of indistinguishable things, and $φ$ induces a
[well-defined comparison](##Degree.CresswellDegree.mk_lt_mk) that
[tells distinct degrees apart](##Degree.cresswellSetoid_lt_eq_bot). The degrees form a scale, a
strict total order, [exactly when $φ$ is a strict weak order](##Degree.isStrictTotalOrder_lt_iff),
and then being indistinguishable is [being incomparable](##Degree.cresswellSetoid_iff_incompRel).
On a preorder the construction is
[mathlib's antisymmetrization](##Degree.cresswellSetoid_eq_antisymmRel), and a connected preorder
and its strict part [give the same degrees](##Degree.cresswellSetoid_lt_eq_le).

## Implementation notes

Cresswell's relata are pairs of a thing and a possible world; here they are the members of any
type `E`, so a comparison across worlds takes `E` to be such pairs. The induced comparison is
written `<` because the comparatives it serves are strict, but it is irreflexive only when $φ$ is,
and a reflexive $φ$ is better served by mathlib's order on `Antisymmetrization`.

## References

* [cresswell-1976]
* [bale-2008]
-/

@[expose] public section

namespace Degree

variable {E : Type*} {φ : E → E → Prop} {a b : E}

/-- Two things are indistinguishable under a comparison `φ` when they stand in `φ` to the same
things on the left and on the right, [cresswell-1976] (4.1). -/
def cresswellSetoid (φ : E → E → Prop) : Setoid E where
  r a b := (∀ c, φ a c ↔ φ b c) ∧ (∀ c, φ c a ↔ φ c b)
  iseqv :=
    ⟨fun _ ↦ ⟨fun _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩,
     fun h ↦ ⟨fun c ↦ (h.1 c).symm, fun c ↦ (h.2 c).symm⟩,
     fun h₁ h₂ ↦ ⟨fun c ↦ (h₁.1 c).trans (h₂.1 c), fun c ↦ (h₁.2 c).trans (h₂.2 c)⟩⟩

/-- The degrees of a comparison are the classes of indistinguishable things. -/
abbrev CresswellDegree (φ : E → E → Prop) : Type _ :=
  Quotient (cresswellSetoid φ)

/-- The comparison a relation induces on its degrees, `⟦b⟧ < ⟦a⟧` iff `φ a b`; well-definedness
is [cresswell-1976]'s own consistency proof for (4.2). -/
instance : LT (CresswellDegree φ) :=
  ⟨Quotient.lift₂ (fun a b ↦ φ b a) fun a₁ _ _ b₂ hac hbd ↦ propext ((hbd.1 a₁).trans (hac.2 b₂))⟩

/-- The degree of `a` exceeds that of `b` exactly when `φ a b`, [cresswell-1976] (4.2). -/
@[simp] theorem CresswellDegree.mk_lt_mk : (⟦b⟧ : CresswellDegree φ) < ⟦a⟧ ↔ φ a b :=
  Iff.rfl

/-- Indistinguishable things have the same degree. -/
theorem CresswellDegree.mk_eq_mk : (⟦a⟧ : CresswellDegree φ) = ⟦b⟧ ↔ cresswellSetoid φ a b :=
  Quotient.eq

/-- The induced comparison tells distinct degrees apart: quotienting again identifies nothing. -/
theorem cresswellSetoid_lt_eq_bot (φ : E → E → Prop) :
    cresswellSetoid ((· < ·) : CresswellDegree φ → CresswellDegree φ → Prop) = ⊥ :=
  le_bot_iff.1 fun x y ↦ Quotient.inductionOn₂ x y fun _ _ h ↦
    Quotient.sound ⟨fun c ↦ h.2 ⟦c⟧, fun c ↦ h.1 ⟦c⟧⟩

/-! ### Scales -/

/-- On a strict weak order, being indistinguishable is being incomparable. -/
theorem cresswellSetoid_iff_incompRel [IsStrictWeakOrder E φ] :
    cresswellSetoid φ a b ↔ IncompRel φ a b := by
  have neg_trans {x y z : E} (hxy : ¬ φ x y) (hyz : ¬ φ y z) : ¬ φ x z := fun hxz ↦ by
    by_cases hyx : φ y x
    · exact hyz (_root_.trans hyx hxz)
    by_cases hzy : φ z y
    · exact hxy (_root_.trans hxz hzy)
    exact (IsStrictWeakOrder.incomp_trans x y z ⟨hxy, hyx⟩ ⟨hyz, hzy⟩).1 hxz
  refine ⟨fun h ↦ ⟨fun hab ↦ irrefl b ((h.1 b).1 hab), fun hba ↦ irrefl b ((h.2 b).1 hba)⟩,
    fun ⟨hab, hba⟩ ↦ ⟨fun c ↦ ⟨fun hac ↦ by_contra fun hbc ↦ neg_trans hab hbc hac, fun hbc ↦
      by_contra fun hac ↦ neg_trans hba hac hbc⟩, fun c ↦ ⟨fun hca ↦ by_contra fun hcb ↦
      neg_trans hcb hba hca, fun hcb ↦ by_contra fun hca ↦ neg_trans hca hab hcb⟩⟩⟩

/-- The degrees of a comparison form a scale exactly when the comparison is a strict weak order. -/
theorem isStrictTotalOrder_lt_iff :
    IsStrictTotalOrder (CresswellDegree φ) (· < ·) ↔ IsStrictWeakOrder E φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hirr (x : E) : ¬ φ x x := irrefl (r := ((· < ·) : CresswellDegree φ → _ → Prop)) ⟦x⟧
    have heq {x y : E} (hxy : ¬ φ x y ∧ ¬ φ y x) : (⟦x⟧ : CresswellDegree φ) = ⟦y⟧ :=
      Std.Trichotomous.trichotomous (r := ((· < ·) : CresswellDegree φ → _ → Prop)) _ _ hxy.2 hxy.1
    exact
      { irrefl := hirr
        trans := fun x y z hxy hyz ↦
          _root_.trans (r := ((· < ·) : CresswellDegree φ → _ → Prop)) (a := ⟦z⟧) (b := ⟦y⟧)
            (c := ⟦x⟧) hyz hxy
        incomp_trans := fun x y z h₁ h₂ ↦
          have hxz := CresswellDegree.mk_eq_mk.1 ((heq h₁).trans (heq h₂))
          ⟨fun h ↦ hirr z ((hxz.1 z).1 h), fun h ↦ hirr z ((hxz.2 z).1 h)⟩ }
  · exact
      { trichotomous := fun x y ↦ Quotient.inductionOn₂ x y fun _ _ hab hba ↦
          Quotient.sound (cresswellSetoid_iff_incompRel.2 ⟨hba, hab⟩)
        irrefl := fun x ↦ Quotient.inductionOn x (irrefl (r := φ))
        trans := fun x y z ↦ Quotient.inductionOn₃ x y z fun _ _ _ hab hbc ↦
          _root_.trans (r := φ) hbc hab }

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

/-! ### Measures -/

section Measure

variable {D : Type*}

private theorem ker_le_cresswellSetoid (R : D → D → Prop) (μ : E → D) :
    Setoid.ker μ ≤ cresswellSetoid fun a b ↦ R (μ a) (μ b) := fun _ _ (h : μ _ = μ _) ↦
  ⟨fun _ ↦ by simp only [h], fun _ ↦ by simp only [h]⟩

variable [LinearOrder D]

/-- A comparison read off a measure into a linear order has the values of the measure as its
degrees. -/
theorem cresswellSetoid_lt_measure (μ : E → D) :
    cresswellSetoid (fun a b ↦ μ b < μ a) = Setoid.ker μ :=
  le_antisymm (fun _ b h ↦ le_antisymm (not_lt.1 fun hlt ↦ lt_irrefl _ ((h.1 b).1 hlt))
    (not_lt.1 fun hlt ↦ lt_irrefl _ ((h.2 b).1 hlt))) (ker_le_cresswellSetoid (· > ·) μ)

/-- The non-strict comparison read off a measure has the same degrees as the strict one. -/
theorem cresswellSetoid_le_measure (μ : E → D) :
    cresswellSetoid (fun a b ↦ μ b ≤ μ a) = Setoid.ker μ :=
  le_antisymm (fun a b h ↦ le_antisymm ((h.2 b).2 le_rfl) ((h.2 a).1 le_rfl))
    (ker_le_cresswellSetoid (· ≥ ·) μ)

end Measure

end Degree
