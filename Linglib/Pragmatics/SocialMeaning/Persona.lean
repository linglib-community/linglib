module

public import Linglib.Pragmatics.SocialMeaning.Dimension
public import Linglib.Pragmatics.SocialMeaning.IndexicalField

/-!
# Personae and grounded fields

This file defines the personae and grounded indexical fields of Burnett's social meaning games
and the Eckert–Montague lift of a field to persona compatibility. A property space is a graph of
incompatibility on social properties, a persona is a maximal independent set of it, and a
grounded field indexes each variant to an independent set of properties. The lift sends a
variant to the personae compatible with it, those with every property it indexes, or on the
Montagovian-individual reading those sharing some property with it, as an entity lifts to the
generalized quantifier of the properties it has. An association field over the dimensions of
social evaluation grounds as the poles whose polarity is the sign of the association. A social
meaning game runs the RSA pipeline on the personae, its literal listener conditioning a prior on
the personae a variant meets; Burnett's 2023 book keeps these definitions, and her 2026 review
takes the game as the current formalization of social meaning as reasoning.

## Main definitions

* `GroundedField`: an indexical field whose values are independent sets of an incompatibility
  graph.
* `GroundedField.Compatible`, `GroundedField.Meets`: a persona has every property a variant
  indexes, or shares one with it.
* `GroundedField.lift`, `GroundedField.liftMI`: the personae compatible with a variant on each
  reading.
* `Persona`: a maximal independent set of the incompatibility graph, and
  `GroundedField.personae`, the personae that meet a variant.
* `AssociationField.ground`: the grounded field of an association field over the dimensions.
* `GroundedField.Complementary`: two variants indexing complementary personae.

## Main results

* `GroundedField.lift_subset_lift`, `GroundedField.liftMI_subset_liftMI`: the lift is antitone
  and the Montagovian-individual lift monotone in the indexed properties.
* `GroundedField.lift_eq_singleton`: a variant that indexes a whole persona lifts to it alone.
* `AssociationField.Antipodal.ground_indexes`: of an antipodal pair, the second grounds as the
  opposites of the poles the first grounds as.
* `GroundedField.Complementary.personae_eq_compl`: of two complementary variants, each meets every
  persona but the one the other indexes.
* `AssociationField.Antipodal.complementary`: an antipodal pair indexing every dimension grounds
  as complementary personae.

## References

* [burnett-2019]
* [burnett-2023]
* [burnett-2026]
* [eckert-2008]
-/

@[expose] public section

namespace SocialMeaning

/-- A grounded field indexes each variant to an independent set of the incompatibility graph
on properties. -/
structure GroundedField (Variant : Type*) {P : Type*} (G : SimpleGraph P) where
  /-- The properties each variant indexes. -/
  indexes : Variant → Finset P
  isIndepSet : ∀ v, G.IsIndepSet (indexes v : Set P)

namespace GroundedField

variable {Variant P : Type*} {G : SimpleGraph P} (F : GroundedField Variant G) (v : Variant)
  (π : Finset P) {v₁ v₂ : Variant}

/-- A persona is compatible with a variant when it has every property the variant indexes. -/
def Compatible : Prop := F.indexes v ⊆ π

/-- On the Montagovian-individual reading, a persona meets a variant when it shares a property
with it. -/
def Meets : Prop := ¬ Disjoint (F.indexes v) π

instance [DecidableEq P] : Decidable (F.Compatible v π) :=
  inferInstanceAs (Decidable (F.indexes v ⊆ π))

instance [DecidableEq P] : Decidable (F.Meets v π) :=
  inferInstanceAs (Decidable (¬ Disjoint _ _))

variable [Fintype P] [DecidableEq P] [DecidableRel G.Adj]

/-- The Eckert–Montague lift sends a variant to the personae compatible with it. -/
def lift : Finset (Finset P) := G.maximalIndepSets.filter (F.Compatible v)

/-- The Montagovian-individual lift sends a variant to the personae that meet it. -/
def liftMI : Finset (Finset P) := G.maximalIndepSets.filter (F.Meets v)

/-- The more a variant indexes, the fewer personae are compatible with it. -/
theorem lift_subset_lift (h : F.indexes v₁ ⊆ F.indexes v₂) : F.lift v₂ ⊆ F.lift v₁ :=
  Finset.monotone_filter_right _ fun _ _ hπ ↦ h.trans hπ

/-- The more a variant indexes, the more personae meet it. -/
theorem liftMI_subset_liftMI (h : F.indexes v₁ ⊆ F.indexes v₂) : F.liftMI v₁ ⊆ F.liftMI v₂ :=
  Finset.monotone_filter_right _ fun _ _ hπ hd ↦ hπ (hd.mono_left h)

/-- A variant that indexes a whole persona is compatible with that persona alone. -/
theorem lift_eq_singleton (h : F.indexes v ∈ G.maximalIndepSets) : F.lift v = {F.indexes v} := by
  ext π
  simp only [lift, Finset.mem_filter, Finset.mem_singleton, Compatible]
  refine ⟨fun ⟨hπ, hsub⟩ ↦ ?_, by rintro rfl; exact ⟨h, subset_rfl⟩⟩
  rw [SimpleGraph.mem_maximalIndepSets] at h hπ
  exact (Finset.coe_injective (h.eq_of_subset hπ.prop (Finset.coe_subset.2 hsub))).symm

end GroundedField

/-- A persona is a maximal independent set of the incompatibility graph, a maximal consistent
set of properties. -/
abbrev Persona {P : Type*} (G : SimpleGraph P) [Fintype P] [DecidableEq P] [DecidableRel G.Adj] :
    Type _ :=
  {π : Finset P // π ∈ G.maximalIndepSets}

/-- The personae that meet a variant. -/
def GroundedField.personae {Variant P : Type*} {G : SimpleGraph P} [Fintype P] [DecidableEq P]
    [DecidableRel G.Adj] (F : GroundedField Variant G) (v : Variant) : Finset (Persona G) :=
  Finset.univ.filter fun π ↦ F.Meets v π.1

@[simp] theorem GroundedField.mem_personae {Variant P : Type*} {G : SimpleGraph P} [Fintype P]
    [DecidableEq P] [DecidableRel G.Adj] {F : GroundedField Variant G} {v : Variant}
    {π : Persona G} : π ∈ F.personae v ↔ F.Meets v π.1 := by
  simp [GroundedField.personae]

namespace GroundedField

variable {Variant P : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph P} [DecidableRel G.Adj]

/-- Two variants are complementary when each indexes a persona and each indexes the properties
the other does not. -/
structure Complementary (F : GroundedField Variant G) (v w : Variant) : Prop where
  left_mem : F.indexes v ∈ G.maximalIndepSets
  right_mem : F.indexes w ∈ G.maximalIndepSets
  indexes_eq_compl : F.indexes v = (F.indexes w)ᶜ

namespace Complementary

variable {F : GroundedField Variant G} {v w : Variant} (h : F.Complementary v w)
include h

theorem symm : F.Complementary w v :=
  ⟨h.right_mem, h.left_mem, by rw [h.indexes_eq_compl, compl_compl]⟩

/-- The persona the first variant indexes, the second's being `h.symm.persona`. -/
def persona : Persona G := ⟨F.indexes v, h.left_mem⟩

theorem persona_ne [Nonempty P] : h.persona ≠ h.symm.persona := by
  intro he
  obtain ⟨p⟩ := ‹Nonempty P›
  have := congrArg (p ∈ ·.1) he
  simp [persona, h.indexes_eq_compl] at this

theorem ne [Nonempty P] : v ≠ w := by
  rintro rfl
  exact h.persona_ne rfl

/-- The first variant meets every persona but the one the second indexes, the persona with none
of its properties. -/
theorem personae_eq_compl : F.personae v = {h.symm.persona}ᶜ := by
  ext π
  rw [mem_personae, Finset.mem_compl, Finset.mem_singleton, Meets, h.indexes_eq_compl,
    disjoint_compl_left_iff, not_iff_not, Subtype.ext_iff]
  refine ⟨fun hsub ↦ ?_, fun he ↦ he ▸ le_rfl⟩
  have hπ := π.2
  rw [SimpleGraph.mem_maximalIndepSets] at hπ
  exact Finset.coe_injective (hπ.eq_of_subset (F.isIndepSet w) (Finset.coe_subset.2 hsub))

theorem symm_persona_notMem_personae : h.symm.persona ∉ F.personae v := by
  rw [h.personae_eq_compl, Finset.mem_compl, Finset.mem_singleton, not_not]

theorem persona_mem_personae [Nonempty P] : h.persona ∈ F.personae v := by
  rw [h.personae_eq_compl, Finset.mem_compl, Finset.mem_singleton]
  exact h.persona_ne

theorem mem_personae_of_ne {p : Persona G} (hp : p ≠ h.persona) (hp' : p ≠ h.symm.persona)
    {u : Variant} (hu : u = v ∨ u = w) : p ∈ F.personae u := by
  rcases hu with rfl | rfl
  · rw [h.personae_eq_compl, Finset.mem_compl, Finset.mem_singleton]
    exact hp'
  · rw [h.symm.personae_eq_compl, Finset.mem_compl, Finset.mem_singleton]
    exact hp

/-- The first variant is compatible with the persona it indexes alone. -/
theorem lift_eq_singleton : F.lift v = {F.indexes v} :=
  F.lift_eq_singleton v h.left_mem

end Complementary

end GroundedField

/-- An association field over the dimensions grounds as the poles whose polarity is the sign
of the variant's association with their dimension. -/
def AssociationField.ground {Variant R : Type*} [Zero R] [Preorder R] [DecidableLT R]
    (M : AssociationField Variant Dimension R) :
    GroundedField Variant (dimensionalIncompatibility Pole.dimension) where
  indexes v := Finset.univ.filter fun p ↦ SignType.sign (M v p.dimension) = p.polarity
  isIndepSet v p hp q hq hne hadj := hne <| Pole.eq_iff.2 ⟨hadj.2, by
    rw [← (Finset.mem_filter.1 hp).2, ← (Finset.mem_filter.1 hq).2, hadj.2]⟩

@[simp] theorem AssociationField.mem_ground_indexes {Variant R : Type*} [Zero R] [Preorder R]
    [DecidableLT R] {M : AssociationField Variant Dimension R} {v : Variant} {p : Pole} :
    p ∈ M.ground.indexes v ↔ SignType.sign (M v p.dimension) = p.polarity := by
  simp [AssociationField.ground]

namespace AssociationField

variable {Variant R : Type*} {v v₁ v₂ : Variant}

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

/-- Of an antipodal pair of sign fields, the second grounds as the opposites of the poles the
first grounds as. -/
theorem Antipodal.ground_indexes {M : AssociationField Variant Dimension SignType}
    (h : M.Antipodal v₁ v₂) :
    M.ground.indexes v₂ = (M.ground.indexes v₁).map Pole.oppositeEquiv.toEmbedding := by
  ext p
  have hs (s : SignType) : SignType.sign s = s := by cases s <;> rfl
  rw [Finset.mem_map_equiv, mem_ground_indexes, mem_ground_indexes, h.symm]
  simp only [Pole.oppositeEquiv_symm, Pole.oppositeEquiv_apply, Pole.dimension_opposite,
    Pole.polarity_opposite, Pi.neg_apply, hs]
  exact neg_eq_iff_eq_neg

/-- An antipodal pair of sign fields that index every dimension ground as complementary
personae. -/
theorem Antipodal.complementary {M : AssociationField Variant Dimension SignType}
    (h : M.Antipodal v₁ v₂) (hv : ∀ d, M v₁ d ≠ 0) : M.ground.Complementary v₁ v₂ := by
  have h₂ (d : Dimension) : M v₂ d = -M v₁ d := by rw [congrFun h d, Pi.neg_apply, neg_neg]
  refine ⟨ground_indexes_mem_maximalIndepSets_iff.2 hv,
    ground_indexes_mem_maximalIndepSets_iff.2 fun d ↦ by
      have := hv d
      rw [h₂]
      revert this
      generalize M v₁ d = s
      revert s
      decide, ?_⟩
  ext p
  rw [Finset.mem_compl, mem_ground_indexes, mem_ground_indexes, h₂]
  have := hv p.dimension
  revert this
  generalize M v₁ p.dimension = s
  cases p <;> revert s <;> decide

end AssociationField

end SocialMeaning
