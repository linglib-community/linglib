module

public import Linglib.Core.Basic.Sign
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Indexical fields

An indexical field, in Eckert's sense, assigns each variant of a linguistic variable the meanings
a use of it may activate, stances, qualities or persona traits, as a function
`Variant → Finset Meaning`. An association field grades the assignment, giving each variant a
signed strength toward each trait, positive when the variant indexes the trait and negative when
it indexes away from it, and the traits a variant indexes toward form its indexical field.

## Main definitions

* `AssociationField`: the signed strength with which each variant indexes each trait, a matrix
  over an ordered ring.
* `AssociationField.Indexes`: a variant indexes a trait, the strength being positive.
* `AssociationField.Antipodal`: two variants index every trait in opposite directions.
* `AssociationField.support`: the indexical field of the traits a variant indexes.
* `AssociationField.contrast`: each variant's strengths less those of a reference variant.
* `AssociationField.signs`: the sign field of a field.

## Main results

* `AssociationField.Antipodal.disjoint_support`: an antipodal pair index no trait in common.
* `AssociationField.antipodal_signs_contrast_iff`: two variants are antipodal in the signs of
  their contrasts with a reference exactly when the reference lies strictly between them, or
  ties with both, on every trait.

## Implementation notes

An association field is a `Matrix`, so composing associations through a mediating domain, Ochs's
indirect indexicality, is matrix multiplication, and inheriting a field along a map of variant
spaces is `Matrix.submatrix`. The carrier is any type with a zero and an order, `SignType` for the
sign-valued fields of Beltrama, Solt and Burnett, an ordered semiring for strengths that compose;
Burnett's grounded fields are indexical fields over the Stereotype Content Model properties.

## References

* [eckert-2008]
* [ochs-1992]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

@[expose] public section

namespace SocialMeaning

/-- An association field assigns each variant of a variable a signed strength toward each
trait, positive when the variant indexes the trait and negative when it indexes away. -/
abbrev AssociationField (Variant Trait R : Type*) := Matrix Variant Trait R

namespace AssociationField

variable {Variant Trait R : Type*} {v v₁ v₂ w : Variant} {t : Trait}

section Indexes

variable [Zero R] [LT R] (M : AssociationField Variant Trait R)

/-- A variant indexes a trait when its association with the trait is positive. -/
def Indexes (v : Variant) (t : Trait) : Prop := 0 < M v t

instance [DecidableLT R] : DecidableRel M.Indexes := fun _ _ ↦ inferInstanceAs (Decidable (_ < _))

variable [Fintype Trait] [DecidableLT R]

/-- The support of a variant is the indexical field of the traits it indexes. -/
def support (v : Variant) : Finset Trait := Finset.univ.filter (M.Indexes v)

@[simp] theorem mem_support : t ∈ M.support v ↔ M.Indexes v t := by simp [support]

end Indexes

section Antipodal

variable [InvolutiveNeg R] (M : AssociationField Variant Trait R)

/-- Two variants are antipodal when they index every trait in opposite directions. -/
def Antipodal (v₁ v₂ : Variant) : Prop := M v₁ = -M v₂

instance [Fintype Trait] [DecidableEq R] (v₁ v₂ : Variant) : Decidable (M.Antipodal v₁ v₂) :=
  inferInstanceAs (Decidable (M v₁ = -M v₂))

variable {M}

theorem Antipodal.symm (h : M.Antipodal v₁ v₂) : M.Antipodal v₂ v₁ := (neg_eq_iff_eq_neg.2 h).symm

theorem antipodal_comm : M.Antipodal v₁ v₂ ↔ M.Antipodal v₂ v₁ := ⟨Antipodal.symm, Antipodal.symm⟩

end Antipodal

section AddGroup

variable [AddGroup R] [Preorder R] [AddLeftStrictMono R] {M : AssociationField Variant Trait R}

theorem Antipodal.indexes_iff (h : M.Antipodal v₁ v₂) : M.Indexes v₁ t ↔ M v₂ t < 0 := by
  rw [Indexes, h, Pi.neg_apply, neg_pos]

theorem Antipodal.disjoint_support [Fintype Trait] [DecidableLT R] (h : M.Antipodal v₁ v₂) :
    Disjoint (M.support v₁) (M.support v₂) :=
  Finset.disjoint_left.2 fun _ h₁ h₂ ↦
    lt_asymm (M.mem_support.1 h₂) (h.indexes_iff.1 (M.mem_support.1 h₁))

end AddGroup

section Contrast

/-- The contrast of a field with a reference variant takes each variant's strengths less those of
the reference. -/
def contrast [Sub R] (M : AssociationField Variant Trait R) (v₀ : Variant) :
    AssociationField Variant Trait R :=
  .of fun v t ↦ M v t - M v₀ t

@[simp] theorem contrast_apply [Sub R] (M : AssociationField Variant Trait R) (v₀ v : Variant)
    (t : Trait) : M.contrast v₀ v t = M v t - M v₀ t := rfl

/-- The sign field of a field. -/
def signs [Zero R] [Preorder R] [DecidableLT R] (M : AssociationField Variant Trait R) :
    AssociationField Variant Trait SignType :=
  M.map SignType.sign

@[simp] theorem signs_apply [Zero R] [Preorder R] [DecidableLT R]
    (M : AssociationField Variant Trait R) (v : Variant) (t : Trait) :
    M.signs v t = SignType.sign (M v t) := rfl

variable [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
  {M : AssociationField Variant Trait R} {v₀ : Variant}

theorem lt_of_signs_contrast_lt (h : (M.contrast v₀).signs v t < (M.contrast v₀).signs w t) :
    M v t < M w t :=
  lt_of_not_ge fun hwv ↦ h.not_ge (SignType.sign.monotone (sub_le_sub_right hwv _))

theorem antipodal_signs_contrast_iff :
    (M.contrast v₀).signs.Antipodal v₁ v₂ ↔
      ∀ t, M v₀ t ∈ Set.uIoo (M v₁ t) (M v₂ t) ∨ M v₁ t = M v₀ t ∧ M v₂ t = M v₀ t := by
  simp only [Antipodal, funext_iff, Pi.neg_apply, signs_apply, contrast_apply,
    sign_sub_eq_neg_sign_sub_iff]

end Contrast

end AssociationField

end SocialMeaning
