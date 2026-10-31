module

public import Linglib.Logic.ComparativeProbability.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.RelClasses

/-!
# Basic API for qualitative probabilities

On any Boolean algebra the axioms let a disjoint common context cancel and let disjoint
comparisons merge. On sets, a qualitative probability pulls back along preimages
(`Set.preimage f ⁻¹'o r`) and, when the range is not null, along images of an injection.

## Main statements

* `rel_sup_sup_right_iff`, `rel_sup_sup_right`, `rel_sup_sup`: context cancellation and
  merging.
* `isQualitativeAdditive_iff`: qualitative additivity is context cancellation.
* `isQualitativeProbability_image`: pulling back along the image of an injection.
* `not_isQualitativeProbability_of_isEmpty`: an empty carrier has no qualitative probability.
* `exists_not_rel_empty_singleton`: a finite carrier has a non-null atom.

## References

* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace ComparativeProbability

section Context

variable {α : Type*} [BooleanAlgebra α] {r : α → α → Prop}

/-- A common context `c` disjoint from both sides cancels, so `a ⊔ c ≿ b ⊔ c ↔ a ≿ b`. -/
theorem rel_sup_sup_right_iff [IsQualitativeAdditive r] {a b c : α} (hca : Disjoint c a)
    (hcb : Disjoint c b) : r (a ⊔ c) (b ⊔ c) ↔ r a b := by
  rw [qadd (r := r) a b, qadd (r := r) (a ⊔ c) (b ⊔ c), sup_comm b c, ← sdiff_sdiff_left,
    sup_sdiff_right_self, sdiff_eq_left.mpr hca.symm, sup_comm a c, ← sdiff_sdiff_left,
    sup_sdiff_left_self, sdiff_eq_left.mpr hcb.symm]

theorem rel_sup_sup_right [IsQualitativeAdditive r] {a b c : α} (h : r a b)
    (hca : Disjoint c a) (hcb : Disjoint c b) : r (a ⊔ c) (b ⊔ c) :=
  (rel_sup_sup_right_iff hca hcb).mpr h

/-- A relation is qualitatively additive iff every common context disjoint from both sides
    cancels, Kraft, Pratt and Seidenberg's additivity axiom (A) (p. 408). -/
theorem isQualitativeAdditive_iff : IsQualitativeAdditive r ↔
    ∀ a b c : α, Disjoint c a → Disjoint c b → (r (a ⊔ c) (b ⊔ c) ↔ r a b) := by
  refine ⟨fun _ _ _ _ ↦ rel_sup_sup_right_iff, fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  have := h (a \ b) (b \ a) (a ⊓ b) disjoint_inf_sdiff (inf_comm b a ▸ disjoint_inf_sdiff)
  rwa [sup_sdiff_inf, inf_comm, sup_sdiff_inf] at this

/-- Two comparisons with disjoint left parts and disjoint right parts merge into their joins,
    even with cross overlaps. The proof adds context to each side, passes through `b₁ ⊔ a₂`,
    and restores the pivot `a₂ ⊓ b₁` by additivity. -/
theorem rel_sup_sup [IsQualitativeAdditive r] [IsTrans α r] {a₁ b₁ a₂ b₂ : α} (h₁ : r a₁ b₁)
    (h₂ : r a₂ b₂) (ha : Disjoint a₁ a₂) (hb : Disjoint b₁ b₂) : r (a₁ ⊔ a₂) (b₁ ⊔ b₂) := by
  have e₁ : (a₂ ⊔ a₁ \ b₂) ⊔ a₁ ⊓ b₂ = a₁ ⊔ a₂ := by
    rw [sup_assoc, sup_comm (a₁ \ b₂), sup_inf_sdiff, sup_comm]
  have e₂ : (b₁ ⊔ b₂ \ a₁) ⊔ a₁ ⊓ b₂ = b₁ ⊔ b₂ := by
    rw [sup_assoc, inf_comm a₁, sup_comm (b₂ \ a₁), sup_inf_sdiff]
  rw [← e₁, ← e₂]
  refine rel_sup_sup_right (trans_of r (b := b₂ ⊔ a₁) ?_ ?_)
    ((ha.mono_left inf_le_left).sup_right (disjoint_sdiff_self_right.mono_left inf_le_right))
    ((hb.symm.mono_left inf_le_right).sup_right (disjoint_sdiff_self_right.mono_left inf_le_left))
  · have h := rel_sup_sup_right h₂ (ha.mono_left sdiff_le) disjoint_sdiff_self_left
    rwa [sup_sdiff_self_right] at h
  · have h := rel_sup_sup_right h₁ disjoint_sdiff_self_left (hb.symm.mono_left sdiff_le)
    rwa [sup_sdiff_self_right, sup_comm a₁ b₂] at h

end Context

/-! ### Qualitative probabilities on sets -/

variable {α W : Type*} {r : Set W → Set W → Prop}

theorem rel_empty [IsLikelihoodMono r] (A : Set W) : r A ∅ := rel_bot (r := r) A

theorem not_rel_empty_univ [IsNontrivial r] : ¬r ∅ Set.univ :=
  IsNontrivial.bot_not_ge_top (r := r)

/-- A qualitative probability pulls back along preimages, comparing sets by their preimages. -/
instance [IsQualitativeProbability r] (f : W → α) :
    IsQualitativeProbability (Set.preimage f ⁻¹'o r) where
  mono _ _ h := mono (r := r) _ _ (Set.preimage_mono h)
  qadd A B := by
    show r _ _ ↔ r _ _
    rw [Set.preimage_sdiff, Set.preimage_sdiff]; exact qadd (r := r) _ _
  bot_not_ge_top := not_rel_empty_univ (r := r)

/-- A qualitative probability pulls back along the image of an injection `f`, comparing sets by
    their images, when the range of `f` is not null. -/
theorem isQualitativeProbability_image [IsQualitativeProbability r] {f : α → W}
    (hf : Function.Injective f) (hnt : ¬r ∅ (Set.range f)) :
    IsQualitativeProbability (Set.image f ⁻¹'o r) where
  mono _ _ h := mono (r := r) _ _ (Set.image_mono h)
  qadd A B := by
    show r _ _ ↔ r _ _
    rw [Set.image_sdiff hf, Set.image_sdiff hf]; exact qadd (r := r) _ _
  bot_not_ge_top := by
    show ¬r (f '' ∅) (f '' Set.univ)
    rwa [Set.image_empty, Set.image_univ]

/-- An empty carrier has no qualitative probability, since there `∅ = Set.univ`. -/
theorem not_isQualitativeProbability_of_isEmpty [IsEmpty W] (r : Set W → Set W → Prop) :
    ¬IsQualitativeProbability r := fun _ ↦
  not_rel_empty_univ (by rw [Set.eq_empty_of_isEmpty (Set.univ : Set W)]; exact refl_of r ∅)

/-- On a finite carrier some atom is not null, since were every singleton at most as likely
    as `∅`, so would be `Set.univ`. -/
theorem exists_not_rel_empty_singleton [Fintype W] (r : Set W → Set W → Prop)
    [IsQualitativeProbability r] : ∃ i, ¬r ∅ {i} := by
  by_contra hall
  push Not at hall
  suffices h : ∀ S : Finset W, r ∅ ↑S from
    not_rel_empty_univ (by simpa using h Finset.univ)
  intro S
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.coe_empty]; exact refl_of r _
  | insert a S ha ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    simpa using rel_sup_sup (hall a) ih disjoint_bot_left (by simpa using ha)

end ComparativeProbability
