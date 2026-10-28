module

public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete lattice homomorphisms between powersets

Mathlib packages the preimage map of a function `f : α → β` as a complete lattice homomorphism
`CompleteLatticeHom.setPreimage f : CompleteLatticeHom (Set β) (Set α)`. This file proves that
every complete lattice homomorphism `Set β → Set α` arises this way from exactly one function.
Such a homomorphism sends each point `a : α` into the image of exactly one singleton `{b}`, and
the function is `a ↦ b`.

## Main results

* `CompleteLatticeHom.existsUnique_mem_map_singleton`: each point lies in the image of exactly
  one singleton.
* `CompleteLatticeHom.setPreimage_surjective`, `CompleteLatticeHom.setPreimage_injective`: every
  complete lattice homomorphism between powersets is the preimage map of a unique function.
* `Equiv.toOrderIsoSet_surjective`: every order isomorphism between powersets is the image map of
  a bijection.
-/

@[expose] public section

namespace CompleteLatticeHom

variable {α β : Type*}

/-- A complete lattice homomorphism `φ : Set β → Set α` places each point of `α` in the image of
exactly one singleton. -/
theorem existsUnique_mem_map_singleton (φ : CompleteLatticeHom (Set β) (Set α)) (a : α) :
    ∃! b, a ∈ φ {b} := by
  have ha : a ∈ φ (⨆ b : β, {b}) := by
    rw [Set.iSup_eq_iUnion, Set.iUnion_of_singleton, ← Set.top_eq_univ, map_top]; trivial
  rw [map_iSup, Set.iSup_eq_iUnion, Set.mem_iUnion] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨b, hb, fun c hc ↦ by_contra fun hcb ↦ ?_⟩
  have h : ({c} ⊓ {b} : Set β) = ⊥ := Set.singleton_inter_eq_empty.2 hcb
  have : a ∈ φ ({c} ⊓ {b}) := by rw [map_inf]; exact ⟨hc, hb⟩
  rwa [h, map_bot] at this

/-- Every complete lattice homomorphism `Set β → Set α` is the preimage map of a function. -/
theorem setPreimage_surjective :
    Function.Surjective (setPreimage : (α → β) → CompleteLatticeHom (Set β) (Set α)) := by
  intro φ
  choose f hf hu using existsUnique_mem_map_singleton φ
  refine ⟨f, ext fun s ↦ Set.ext fun a ↦ ?_⟩
  rw [setPreimage_apply, Set.mem_preimage]
  conv_rhs => rw [← Set.biUnion_of_singleton s]
  simp only [← Set.iSup_eq_iUnion, map_iSup₂]
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, exists_prop]
  exact ⟨fun h ↦ ⟨f a, h, hf a⟩, fun ⟨b, hb, hab⟩ ↦ hu a b hab ▸ hb⟩

/-- Distinct functions have distinct preimage maps. -/
theorem setPreimage_injective :
    Function.Injective (setPreimage : (α → β) → CompleteLatticeHom (Set β) (Set α)) := by
  intro f g h
  funext a
  simpa using congrArg (fun φ : CompleteLatticeHom (Set β) (Set α) ↦ a ∈ φ {g a}) h

end CompleteLatticeHom

namespace Equiv

variable {α β : Type*}

/-- Every order isomorphism between powersets is the image map of a bijection. -/
theorem toOrderIsoSet_surjective :
    Function.Surjective (toOrderIsoSet : α ≃ β → Set α ≃o Set β) := by
  intro γ
  obtain ⟨f, hf⟩ := CompleteLatticeHom.setPreimage_surjective
    (CompleteLatticeHom.OrderIso.toCompleteLatticeHom γ)
  obtain ⟨g, hg⟩ := CompleteLatticeHom.setPreimage_surjective
    (CompleteLatticeHom.OrderIso.toCompleteLatticeHom γ.symm)
  have hγ (s) : γ s = f ⁻¹' s := (DFunLike.congr_fun hf s).symm
  have hγ' (s) : γ.symm s = g ⁻¹' s := (DFunLike.congr_fun hg s).symm
  have hfg : f ∘ g = id := CompleteLatticeHom.setPreimage_injective <|
    CompleteLatticeHom.ext fun s ↦ by simp [Set.preimage_comp, ← hγ, ← hγ']
  have hgf : g ∘ f = id := CompleteLatticeHom.setPreimage_injective <|
    CompleteLatticeHom.ext fun s ↦ by simp [Set.preimage_comp, ← hγ, ← hγ']
  refine ⟨⟨g, f, congrFun hfg, congrFun hgf⟩, OrderIso.ext <| funext fun s ↦ ?_⟩
  rw [toOrderIsoSet_apply, image_eq_preimage_symm]
  exact (hγ s).symm

end Equiv
