/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Language
public import Linglib.Core.Computability.SyntacticMonoid
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Tier-based extensions of classes of languages

A tier is a set of salient symbols, and a language holds *on a tier* of a word when it contains
the word's projection, what is left after erasing the symbols off the tier. Reading a language on
a tier is a homomorphism `Language.onTier T` of Boolean algebras, and the *tier-based extension*
`Language.tierBased 𝒞` of a class `𝒞` of languages collects the members of `𝒞` read on some tier.
Heinz, Rawal and Tanner introduce the construction for the strictly local languages and Lambert
extends it to every class.

A symbol is *neutral* for a language when inserting or deleting it never changes membership, which
is to say that its syntactic class is the identity. The symbols off the tier are neutral for a
language read on it, and [a language is its own reading on a tier exactly when the symbols off the
tier are neutral](##Language.onTier_eq_self_iff). So a language read on a tier is the same base
language [read on the symbols that are not neutral](##Language.onTier_salient), which lie on every
tier it can be read on: every tier-based language has a least tier.

## Implementation notes

A tier is a predicate `T : α → Prop` together with its decidability, as for `FreeMonoid.filter`:
`tierBased` quantifies over both, `∃ T, ∃ _ : DecidablePred T, …`, in the manner of mathlib's
`ComputablePred`. The base language of a tier-based language ranges over the whole alphabet.
Lambert takes it over the symbols of the tier, which gives the same extension for a class whose
members over the tier's symbols are the restrictions of its members over the alphabet.

## References

* [heinz-rawal-tanner-2011]
* [lambert-2023]
-/

@[expose] public section

namespace Language

variable {α : Type*} {𝒞 𝒟 : Set (Language α)} {L L' : Language α} {w : List α}

/-! ### Reading a language on a tier -/

section OnTier

variable (T T' : α → Prop) [DecidablePred T] [DecidablePred T']

/-- The language `L` read on the tier `T`, Lambert's `[L]_T`: the words whose projection to `T`
lies in `L`. It is the inverse image of `L` under `FreeMonoid.filter T`, as a homomorphism of
Boolean algebras. -/
def onTier : BoundedLatticeHom (Language α) (Language α) where
  toFun L := {w | w.filter T ∈ L}
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

variable {T} in
@[simp] theorem mem_onTier : w ∈ onTier T L ↔ w.filter T ∈ L := Iff.rfl

/-- On the tier of the whole alphabet a language reads as itself. -/
@[simp] theorem onTier_true : onTier (fun _ : α ↦ True) L = L := Language.ext fun _ ↦ by simp

theorem onTier_onTier : onTier T (onTier T' L) = onTier (fun a ↦ T' a ∧ T a) L :=
  Language.ext fun w ↦ by simp [List.filter_filter]

/-- Reading on a tier commutes with reversal. -/
theorem reverse_onTier : (onTier T L).reverse = onTier T L.reverse :=
  Language.ext fun w ↦ by simp [mem_reverse, List.filter_reverse]

end OnTier

/-! ### The tier-based extension -/

/-- The *tier-based extension* of a class `𝒞` consists of the members of `𝒞` read on a tier. -/
def tierBased (𝒞 : Set (Language α)) : Set (Language α) :=
  {L | ∃ (T : α → Prop) (_ : DecidablePred T), ∃ L' ∈ 𝒞, onTier T L' = L}

theorem onTier_mem_tierBased (T : α → Prop) [DecidablePred T] (h : L ∈ 𝒞) :
    onTier T L ∈ tierBased 𝒞 :=
  ⟨T, _, L, h, rfl⟩

theorem subset_tierBased : 𝒞 ⊆ tierBased 𝒞 := fun L h ↦ ⟨fun _ ↦ True, inferInstance, L, h, by simp⟩

theorem tierBased_mono (h : 𝒞 ⊆ 𝒟) : tierBased 𝒞 ⊆ tierBased 𝒟 := by
  rintro _ ⟨T, _, L, hL, rfl⟩
  exact onTier_mem_tierBased T (h hL)

/-! ### Neutral symbols and the least tier -/

section Neutral

variable {T : α → Prop} [DecidablePred T]

/-- A symbol off the tier is neutral for a language read on the tier: its syntactic class is the
identity. -/
theorem syntacticClass_onTier_eq_one {a : α} (ha : ¬ T a) :
    (onTier T L).syntacticClass [a] = 1 :=
  syntacticClass_eq_one_iff.2 fun u v ↦ by simp [List.filter_append, ha]

/-- A symbol that is not neutral for a language read on a tier is on the tier. -/
theorem of_syntacticClass_onTier_ne_one {a : α} (h : (onTier T L).syntacticClass [a] ≠ 1) :
    T a :=
  Decidable.by_contra fun ha ↦ h (syntacticClass_onTier_eq_one ha)

/-- A language is its own reading on a tier exactly when the symbols off the tier are neutral. -/
theorem onTier_eq_self_iff : onTier T L = L ↔ ∀ a, ¬ T a → L.syntacticClass [a] = 1 :=
  ⟨fun h _ ha ↦ h ▸ syntacticClass_onTier_eq_one ha,
    fun h ↦ Language.ext fun w ↦ mem_iff_of_syntacticClass_eq (syntacticClass_filter h w)⟩

/-- A language read on a tier is the same base language read on the symbols that are not
neutral for it. These lie on the tier by `of_syntacticClass_onTier_ne_one`, so they form the least
tier the language can be read on. -/
theorem onTier_salient [DecidablePred fun a ↦ L.syntacticClass [a] ≠ 1] (h : onTier T L' = L) :
    onTier (fun a ↦ L.syntacticClass [a] ≠ 1) L' = L := by
  have hS : onTier (fun a ↦ L.syntacticClass [a] ≠ 1) L = L :=
    onTier_eq_self_iff.2 fun _ ha ↦ not_not.1 ha
  ext w
  have hT : (w.filter fun a ↦ L.syntacticClass [a] ≠ 1).filter T =
      w.filter fun a ↦ L.syntacticClass [a] ≠ 1 :=
    List.filter_eq_self.2 fun a ha ↦ decide_eq_true <| of_syntacticClass_onTier_ne_one <| by
      rw [h]
      exact of_decide_eq_true (List.mem_filter.1 ha).2
  have h₁ := Set.ext_iff.1 h (w.filter fun a ↦ L.syntacticClass [a] ≠ 1)
  rw [mem_onTier, hT] at h₁
  exact h₁.trans (Set.ext_iff.1 hS w)

/-- Every tier-based language is a member of the base class read on its symbols that are not
neutral. -/
theorem exists_onTier_salient_eq_of_mem_tierBased
    [DecidablePred fun a ↦ L.syntacticClass [a] ≠ 1] (h : L ∈ tierBased 𝒞) :
    ∃ L' ∈ 𝒞, onTier (fun a ↦ L.syntacticClass [a] ≠ 1) L' = L := by
  obtain ⟨T, _, L', hL', h⟩ := h
  exact ⟨L', hL', onTier_salient h⟩

end Neutral

end Language
