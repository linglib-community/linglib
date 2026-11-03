module

public import Linglib.Core.Basic.Sign
public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.Persona

/-!
# Association fields

An association field gives each variant of a variable a signed strength toward each trait,
positive when the variant indexes the trait and negative when it indexes away from it. Two variants
are [antipodal](##SocialMeaning.AssociationField.Antipodal) when they index every trait in
opposite directions. Over the dimensions of social evaluation a field grounds each variant in the
poles its signs point to, its Eckert field in Burnett's sense. The field of a variant is a persona
exactly when its association with
[every dimension is nonzero](##SocialMeaning.AssociationField.ground_indexes_mem_maximalIndepSets_iff),
a variant with $z$ null associations is compatible with
[$2^z$ personae](##SocialMeaning.AssociationField.card_compatiblePersonae_ground), and two variants
ground in [complementary personae](##SocialMeaning.AssociationField.complementary_ground_iff)
exactly when the first is associated with every dimension and the second's signs negate it.

## Implementation notes

The carrier is `SignType` for a field that records only the direction of an association, and a
linear order for one that records ratings.

## References

* [eckert-2008]
* [burnett-2019]
* [beltrama-solt-burnett-2023]
-/

@[expose] public section

namespace SocialMeaning

/-- An association field gives each variant of a variable a signed strength toward each trait,
positive when the variant indexes the trait and negative when it indexes away from it. -/
abbrev AssociationField (Variant Trait R : Type*) := Variant → Trait → R

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

/-- An association field over the dimensions grounds each variant in the poles its signs point
to. -/
def ground [Zero R] [Preorder R] [DecidableLT R] (M : AssociationField Variant Dimension R) :
    GroundedField Variant (dimensionalIncompatibility Pole.dimension) where
  indexes v := poles Pole.dimension Pole.polarity fun d ↦ SignType.sign (M v d)
  isIndepSet _ := isIndepSet_poles Pole.bijOn _

@[simp] theorem mem_ground_indexes [Zero R] [Preorder R] [DecidableLT R]
    {M : AssociationField Variant Dimension R} {p : Pole} :
    p ∈ M.ground.indexes v ↔ SignType.sign (M v p.dimension) = p.polarity :=
  mem_poles

section LinearOrder

variable [Zero R] [LinearOrder R] {M : AssociationField Variant Dimension R}

theorem ground_indexes_mem_maximalIndepSets_iff :
    M.ground.indexes v ∈ (dimensionalIncompatibility Pole.dimension).maximalIndepSets ↔
      ∀ d, M v d ≠ 0 :=
  (poles_mem_maximalIndepSets_iff Pole.bijOn).trans (forall_congr' fun _ ↦ sign_ne_zero)

/-- Two variants ground in complementary personae exactly when the first is associated with every
dimension and the second's signs are the negations of the first's. -/
theorem complementary_ground_iff :
    M.ground.Complementary v₁ v₂ ↔
      (∀ d, M v₁ d ≠ 0) ∧ ∀ d, SignType.sign (M v₂ d) = -SignType.sign (M v₁ d) := by
  have key := poles_eq_compl_poles_iff Pole.bijOn (σ := fun d ↦ SignType.sign (M v₂ d))
    (τ := fun d ↦ SignType.sign (M v₁ d))
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ⟨ground_indexes_mem_maximalIndepSets_iff.2 h₁,
    ground_indexes_mem_maximalIndepSets_iff.2 fun d ↦ ?_, key.2 ⟨fun d ↦ ?_, funext fun d ↦ ?_⟩⟩⟩
  · obtain ⟨-, h₂⟩ := key.1 h.indexes_eq_compl
    refine ⟨ground_indexes_mem_maximalIndepSets_iff.1 h.left_mem, fun d ↦ ?_⟩
    rw [congrFun h₂ d, Pi.neg_apply, neg_neg]
  · rw [← sign_ne_zero, h₂, Ne, SignType.neg_eq_zero_iff, sign_eq_zero_iff]
    exact h₁ d
  · rw [h₂, Ne, SignType.neg_eq_zero_iff, sign_eq_zero_iff]
    exact h₁ d
  · rw [Pi.neg_apply, h₂, neg_neg]

/-- The personae compatible with a variant number two to the power of the dimensions it is not
associated with. -/
theorem card_compatiblePersonae_ground :
    (M.ground.compatiblePersonae v).card = 2 ^ (Finset.univ.filter (M v · = 0)).card := by
  rw [GroundedField.card_compatiblePersonae]
  refine (card_filter_poles_subset Pole.bijOn _).trans ?_
  simp only [sign_eq_zero_iff]

end LinearOrder

variable {M : AssociationField Variant Dimension SignType}

/-- Of an antipodal pair of sign fields, the second grounds in the opposites of the poles the
first grounds in. -/
theorem Antipodal.ground_indexes (h : M.Antipodal v₁ v₂) :
    M.ground.indexes v₂ = (M.ground.indexes v₁).map Pole.oppositeEquiv.toEmbedding := by
  ext p
  rw [Finset.mem_map_equiv, mem_ground_indexes, mem_ground_indexes, h.symm]
  simp only [Pole.oppositeEquiv_symm, Pole.oppositeEquiv_apply, Pole.dimension_opposite,
    Pole.polarity_opposite, Pi.neg_apply, SignType.sign_self]
  exact neg_eq_iff_eq_neg

/-- An antipodal pair of sign fields that index every dimension ground in complementary
personae. -/
theorem Antipodal.complementary (h : M.Antipodal v₁ v₂) (hv : ∀ d, M v₁ d ≠ 0) :
    M.ground.Complementary v₁ v₂ :=
  complementary_ground_iff.2 ⟨hv, fun d ↦ by rw [SignType.sign_self, SignType.sign_self, h.symm,
    Pi.neg_apply]⟩

end Ground

end AssociationField

end SocialMeaning
