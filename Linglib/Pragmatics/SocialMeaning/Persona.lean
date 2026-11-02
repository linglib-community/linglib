module

public import Linglib.Core.Combinatorics.SimpleGraph.MaximalIndepSet

/-!
# Personae and grounded fields

A persona of Burnett's social meaning games is a maximal independent set of a graph of
incompatibility on social properties, and a grounded field indexes each variant to an
independent set, its Eckert field, whose Eckert–Montague field is the set of personae sharing
some property with it. A persona with every property a variant indexes
[meets it](##SocialMeaning.GroundedField.compatiblePersonae_subset_personae) when the variant
indexes any, and a variant that indexes nothing
[meets none](##SocialMeaning.GroundedField.personae_eq_empty).

## Main definitions

* `GroundedField`: an indexical field whose values are independent sets of an incompatibility
  graph.
* `Persona`: a maximal independent set of the incompatibility graph.
* `GroundedField.Meets`, `GroundedField.Compatible`: a persona shares a property with a variant,
  or has every property it indexes.
* `GroundedField.personae`: the Eckert–Montague field of a variant, the personae that meet it.
* `GroundedField.compatiblePersonae`: the personae compatible with a variant.
* `GroundedField.Complementary`: two variants indexing complementary personae.

## Implementation notes

A social meaning game's literal listener conditions a prior over the personae on the
Eckert–Montague field of the variant it hears, so a variant that indexes nothing leaves it
conditioning on the empty set (`GroundedField.personae_eq_empty`).

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

/-- A persona is a maximal independent set of the incompatibility graph, a maximal consistent
set of properties. -/
abbrev Persona {P : Type*} (G : SimpleGraph P) [Fintype P] [DecidableEq P] [DecidableRel G.Adj] :
    Type _ :=
  {π : Finset P // π ∈ G.maximalIndepSets}

namespace GroundedField

section Personae

variable {Variant P : Type*} {G : SimpleGraph P} (F : GroundedField Variant G) (v : Variant)
  (π : Finset P) {v₁ v₂ : Variant}

/-- A persona meets a variant when it shares a property with it. -/
def Meets : Prop := ¬ Disjoint (F.indexes v) π

/-- A persona is compatible with a variant when it has every property the variant indexes. -/
def Compatible : Prop := F.indexes v ⊆ π

instance [DecidableEq P] : Decidable (F.Meets v π) :=
  inferInstanceAs (Decidable (¬ Disjoint _ _))

instance [DecidableEq P] : Decidable (F.Compatible v π) :=
  inferInstanceAs (Decidable (F.indexes v ⊆ π))

variable [Fintype P] [DecidableEq P] [DecidableRel G.Adj]

/-- The Eckert–Montague field of a variant is the set of personae that meet it, the type-lift of
its Eckert field: the field on *competent* and *friendly* consists of the personae that are
competent or friendly ([burnett-2019] p. 433). -/
def personae : Finset (Persona G) := Finset.univ.filter fun π ↦ F.Meets v π.1

/-- The personae compatible with a variant, those with every property it indexes. -/
def compatiblePersonae : Finset (Persona G) := Finset.univ.filter fun π ↦ F.Compatible v π.1

variable {F v}

@[simp] theorem mem_personae {π : Persona G} : π ∈ F.personae v ↔ F.Meets v π.1 := by
  simp [personae]

@[simp] theorem mem_compatiblePersonae {π : Persona G} :
    π ∈ F.compatiblePersonae v ↔ F.Compatible v π.1 := by
  simp [compatiblePersonae]

variable (F)

theorem card_compatiblePersonae :
    (F.compatiblePersonae v).card = (G.maximalIndepSets.filter (F.indexes v ⊆ ·)).card := by
  rw [← Finset.card_map (.subtype _)]
  congr 1
  ext s
  simp [Compatible, and_comm]

theorem personae_mono (h : F.indexes v₁ ⊆ F.indexes v₂) : F.personae v₁ ⊆ F.personae v₂ :=
  Finset.monotone_filter_right _ fun _ _ hπ hd ↦ hπ (hd.mono_left h)

theorem compatiblePersonae_anti (h : F.indexes v₁ ⊆ F.indexes v₂) :
    F.compatiblePersonae v₂ ⊆ F.compatiblePersonae v₁ :=
  Finset.monotone_filter_right _ fun _ _ hπ ↦ h.trans hπ

/-- A persona with every property a variant indexes meets it, unless the variant indexes
nothing. -/
theorem compatiblePersonae_subset_personae (h : (F.indexes v).Nonempty) :
    F.compatiblePersonae v ⊆ F.personae v := fun _ hπ ↦
  mem_personae.2 fun hd ↦ h.ne_empty
    ((Finset.disjoint_self_iff_empty _).1 (hd.mono_right (mem_compatiblePersonae.1 hπ)))

theorem personae_eq_empty (h : F.indexes v = ∅) : F.personae v = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hπ ↦ mem_personae.1 hπ (by simp [h])

theorem compatiblePersonae_eq_univ (h : F.indexes v = ∅) : F.compatiblePersonae v = .univ :=
  Finset.eq_univ_of_forall fun π ↦ mem_compatiblePersonae.2 (by simp [Compatible, h])

/-- A variant that indexes a whole persona is compatible with that persona alone, so that
conditioning on the personae compatible with an Eckert field would leave only the persona the field
itself is, the reason [burnett-2019] (p. 434) conditions on the Eckert–Montague field instead. -/
theorem compatiblePersonae_eq_singleton (h : F.indexes v ∈ G.maximalIndepSets) :
    F.compatiblePersonae v = {⟨F.indexes v, h⟩} := by
  ext π
  rw [mem_compatiblePersonae, Finset.mem_singleton, Compatible, Subtype.ext_iff]
  refine ⟨fun hsub ↦ ?_, fun he ↦ he ▸ subset_rfl⟩
  exact (Finset.coe_injective ((G.mem_maximalIndepSets.1 h).eq_of_subset
    (G.mem_maximalIndepSets.1 π.2).prop (Finset.coe_subset.2 hsub))).symm

end Personae

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
theorem compatiblePersonae_eq_singleton : F.compatiblePersonae v = {h.persona} :=
  F.compatiblePersonae_eq_singleton h.left_mem

end Complementary

end GroundedField

end SocialMeaning
