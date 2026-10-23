module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Setoid.Basic

/-!
# Degrees as equivalence classes

Cresswell builds degrees from a comparison instead of assuming them. Two entities are
indistinguishable under a comparison `φ` when they stand in `φ` to the same entities on both
sides, the degrees are the classes of indistinguishable entities, and `φ` induces a well-defined
comparison on them. On a preorder the construction is mathlib's `Antisymmetrization`, and on an
equivalence relation it returns the cells of the partition.

## Main definitions

* `Degree.cresswellSetoid`: indistinguishability under a comparison.
* `Degree.CresswellDegree`: the degrees of a comparison.

## Main statements

* `Degree.cresswellSetoid_le_iff`: on a preorder the construction is `Antisymmetrization`.
* `Degree.cresswellSetoid_setoid`: on an equivalence relation the construction returns the
  relation itself.

## References

* [cresswell-1976]
-/

@[expose] public section

namespace Degree

/-- Two pairs are indistinguishable under a comparison `φ` when they have the same φ-profile on the
left and on the right, [cresswell-1976] (4.1). -/
def cresswellSetoid {E : Type*} (φ : E → E → Prop) : Setoid E where
  r a b := (∀ c, φ a c ↔ φ b c) ∧ (∀ c, φ c a ↔ φ c b)
  iseqv :=
    ⟨fun _ => ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩,
     fun h => ⟨fun c => (h.1 c).symm, fun c => (h.2 c).symm⟩,
     fun h₁ h₂ => ⟨fun c => (h₁.1 c).trans (h₂.1 c),
                   fun c => (h₁.2 c).trans (h₂.2 c)⟩⟩

/-- Degrees of comparison as φ-equivalence classes ([cresswell-1976] (4.1)). -/
abbrev CresswellDegree {E : Type*} (φ : E → E → Prop) : Type _ :=
  Quotient (cresswellSetoid φ)

/-- The comparison a relation induces on its degrees, `⟦a⟧ < ⟦b⟧` iff `φ b a`, strict exactly
when `φ` is; well-definedness is [cresswell-1976]'s own consistency proof for (4.2). -/
instance {E : Type*} {φ : E → E → Prop} : LT (CresswellDegree φ) :=
  ⟨Quotient.lift₂ (fun a b ↦ φ b a) fun a₁ _ _ b₂ hac hbd ↦ propext ((hbd.1 a₁).trans (hac.2 b₂))⟩

/-- The degree of `a` exceeds that of `b` exactly when `φ(a, b)`, [cresswell-1976] (4.2). -/
@[simp] theorem CresswellDegree.mk_lt_mk {E : Type*} {φ : E → E → Prop} {a b : E} :
    (⟦a⟧ : CresswellDegree φ) < ⟦b⟧ ↔ φ b a :=
  Iff.rfl

theorem cresswellSetoid_le_iff {E : Type*} [Preorder E] (a b : E) :
    (cresswellSetoid (· ≤ ·)).r a b ↔ AntisymmRel (· ≤ ·) a b := by
  constructor
  · intro ⟨h₁, h₂⟩
    exact ⟨(h₁ b).mpr le_rfl, (h₁ a).mp le_rfl⟩
  · intro ⟨hab, hba⟩
    exact ⟨fun c => ⟨hba.trans, hab.trans⟩,
           fun c => ⟨(le_trans · hab), (le_trans · hba)⟩⟩

theorem cresswellSetoid_setoid {E : Type*} (s : Setoid E) : cresswellSetoid s = s :=
  Setoid.ext fun _ b ↦ ⟨fun h ↦ (h.1 b).2 (s.refl' b), fun h ↦
    ⟨fun _ ↦ ⟨s.trans' (s.symm' h), s.trans' h⟩,
      fun _ ↦ ⟨(s.trans' · h), (s.trans' · (s.symm' h))⟩⟩⟩

end Degree
