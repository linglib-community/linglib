module

public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.Persona
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Association fields

An association field gives each variant of a variable a signed strength toward each trait,
positive when the variant indexes the trait and negative when it indexes away from it. Two variants
are [antipodal](##SocialMeaning.AssociationField.Antipodal) when they index every trait in
opposite directions. Over the dimensions of social evaluation a field grounds each variant in the
poles its signs point to, its Eckert field in Burnett's sense. The field of a variant is a persona
exactly when its association with
[every dimension is nonzero](##SocialMeaning.AssociationField.ground_indexes_mem_maximalIndepSets_iff),
and two antipodal variants of a sign field whose associations are all nonzero ground in
[complementary personae](##SocialMeaning.AssociationField.Antipodal.complementary).

## Implementation notes

An association field is a `Matrix`, so composing associations through a mediating domain, as in
Ochs's indirect indexicality, is matrix multiplication. The carrier is `SignType` for fields that
record only the direction of an association, and an ordered semiring for strengths that compose.

## References

* [eckert-2008]
* [burnett-2019]
* [ochs-1992]
* [beltrama-solt-burnett-2023]
-/

@[expose] public section

namespace SocialMeaning

/-- An association field gives each variant of a variable a signed strength toward each trait,
positive when the variant indexes the trait and negative when it indexes away from it. -/
abbrev AssociationField (Variant Trait R : Type*) := Matrix Variant Trait R

namespace AssociationField

variable {Variant Trait R : Type*} {v v₁ v₂ : Variant}

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

section Ground

/-- An association field over the dimensions grounds each variant in the poles whose polarity is
the sign of its association with their dimension. -/
def ground [Zero R] [Preorder R] [DecidableLT R] (M : AssociationField Variant Dimension R) :
    GroundedField Variant (dimensionalIncompatibility Pole.dimension) where
  indexes v := Finset.univ.filter fun p ↦ SignType.sign (M v p.dimension) = p.polarity
  isIndepSet v p hp q hq hne hadj := hne <| Pole.eq_iff.2 ⟨hadj.2, by
    rw [← (Finset.mem_filter.1 hp).2, ← (Finset.mem_filter.1 hq).2, hadj.2]⟩

@[simp] theorem mem_ground_indexes [Zero R] [Preorder R] [DecidableLT R]
    {M : AssociationField Variant Dimension R} {p : Pole} :
    p ∈ M.ground.indexes v ↔ SignType.sign (M v p.dimension) = p.polarity := by
  simp [ground]

private theorem card_filter_dimension_polarity (d : Dimension) (s : SignType) :
    (Finset.univ.filter fun p : Pole ↦ p.dimension = d ∧ s = p.polarity).card =
      if s = 0 then 0 else 1 := by
  revert d s; decide

theorem ground_indexes_mem_maximalIndepSets_iff [Zero R] [LinearOrder R]
    {M : AssociationField Variant Dimension R} :
    M.ground.indexes v ∈ (dimensionalIncompatibility Pole.dimension).maximalIndepSets ↔
      ∀ d, M v d ≠ 0 := by
  rw [Pole.mem_maximalIndepSets_iff]
  refine forall_congr' fun d ↦ ?_
  have : (M.ground.indexes v).filter (·.dimension = d) =
      Finset.univ.filter fun p : Pole ↦ p.dimension = d ∧ SignType.sign (M v d) = p.polarity := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, mem_ground_indexes, true_and]
    exact ⟨fun ⟨h, hp⟩ ↦ ⟨hp, hp ▸ h⟩, fun ⟨hp, h⟩ ↦ ⟨hp ▸ h, hp⟩⟩
  rw [this, card_filter_dimension_polarity]
  split_ifs with h <;> simp_all [sign_eq_zero_iff]

variable {M : AssociationField Variant Dimension SignType}

/-- Of an antipodal pair of sign fields, the second grounds in the opposites of the poles the
first grounds in. -/
theorem Antipodal.ground_indexes (h : M.Antipodal v₁ v₂) :
    M.ground.indexes v₂ = (M.ground.indexes v₁).map Pole.oppositeEquiv.toEmbedding := by
  ext p
  have hs (s : SignType) : SignType.sign s = s := by cases s <;> rfl
  rw [Finset.mem_map_equiv, mem_ground_indexes, mem_ground_indexes, h.symm]
  simp only [Pole.oppositeEquiv_symm, Pole.oppositeEquiv_apply, Pole.dimension_opposite,
    Pole.polarity_opposite, Pi.neg_apply, hs]
  exact neg_eq_iff_eq_neg

/-- An antipodal pair of sign fields that index every dimension ground in complementary
personae. -/
theorem Antipodal.complementary (h : M.Antipodal v₁ v₂) (hv : ∀ d, M v₁ d ≠ 0) :
    M.ground.Complementary v₁ v₂ := by
  have h₂ (d : Dimension) : M v₂ d = -M v₁ d := by rw [congrFun h d, Pi.neg_apply, neg_neg]
  refine ⟨ground_indexes_mem_maximalIndepSets_iff.2 hv,
    ground_indexes_mem_maximalIndepSets_iff.2 fun d ↦ h₂ d ▸ (hv d <| SignType.neg_eq_zero_iff.1 ·),
    ?_⟩
  ext p
  rw [Finset.mem_compl, mem_ground_indexes, mem_ground_indexes, h₂]
  have := hv p.dimension
  revert this
  generalize M v₁ p.dimension = s
  cases p <;> revert s <;> decide

end Ground

end AssociationField

end SocialMeaning
