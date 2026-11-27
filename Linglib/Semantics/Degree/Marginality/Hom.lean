/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Marginality.Constructions

/-!
# Homomorphisms of marginal scales

A homomorphism of marginal scales is a map that preserves and reflects smaller than and marginally
smaller than; it then preserves and reflects largely smaller than and at most marginal
difference. These are the representations of the measurement theory of Dinis and Jacinto.

## Main definitions

* `MarginalScale.IsHom`: the homomorphisms of marginal scales.

## Main results

* `MarginalScale.isHom_iff_atMostMarginal`: a map is a homomorphism exactly when it is strictly
  monotone and preserves and reflects at most marginal difference.
* `MarginalScale.isHom_lex_iff`: a map into lexicographic pairs is a homomorphism exactly when its
  block coordinate pulls back largely smaller than and its location coordinate grows along
  marginal steps.
* `MarginalScale.isHom_toLex`: an embedding of the blocks together with an embedding of the
  degrees of each block is a homomorphism into lexicographic pairs.

## References

* [dinis-jacinto-2025]
-/

@[expose] public section

namespace MarginalScale

variable {α : Type*} [LinearOrder α] {ml : MarginalScale α} {x y z : α}

/-- A homomorphism of marginal scales preserves and reflects smaller than and marginally smaller
than. -/
structure IsHom {β : Type*} [LinearOrder β] (ml : MarginalScale α) (ml' : MarginalScale β)
    (f : α → β) : Prop where
  /-- The map preserves and reflects smaller than. -/
  strictMono : StrictMono f
  /-- The map preserves and reflects marginally smaller than. -/
  marginallyLT_iff : ∀ x y, ml'.MarginallyLT (f x) (f y) ↔ ml.MarginallyLT x y

section IsHom

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] {ml' : MarginalScale β}
  {ml'' : MarginalScale γ} {f : α → β} {g : β → γ}

theorem IsHom.largelyLT_iff (hf : ml.IsHom ml' f) : ml'.LargelyLT (f x) (f y) ↔ ml.LargelyLT x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.marginallyLT_iff x y))

theorem IsHom.atMostMarginal_iff (hf : ml.IsHom ml' f) :
    ml'.AtMostMarginal (f x) (f y) ↔ ml.AtMostMarginal x y := by
  simp only [atMostMarginal_iff_incompRel, IncompRel, hf.largelyLT_iff]

/-- A map is a homomorphism exactly when it is strictly monotone and preserves and reflects at
most marginal difference. -/
theorem isHom_iff_atMostMarginal : ml.IsHom ml' f ↔
    StrictMono f ∧ ∀ x y, ml'.AtMostMarginal (f x) (f y) ↔ ml.AtMostMarginal x y :=
  ⟨fun hf ↦ ⟨hf.strictMono, fun _ _ ↦ hf.atMostMarginal_iff⟩, fun ⟨hf, h⟩ ↦ ⟨hf, fun x y ↦ by
    rw [marginallyLT_iff_lt_and_atMostMarginal, marginallyLT_iff_lt_and_atMostMarginal,
      hf.lt_iff_lt, h]⟩⟩

variable (ml) in
protected theorem IsHom.id : ml.IsHom ml id := ⟨strictMono_id, fun _ _ ↦ Iff.rfl⟩

theorem IsHom.comp (hg : ml'.IsHom ml'' g) (hf : ml.IsHom ml' f) : ml.IsHom ml'' (g ∘ f) :=
  ⟨hg.strictMono.comp hf.strictMono,
    fun x y ↦ (hg.marginallyLT_iff _ _).trans (hf.marginallyLT_iff x y)⟩

end IsHom

section Lex

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] {f : α → β ×ₗ γ}

/-- A map into a lexicographic marginal scale is a homomorphism exactly when its block coordinate
pulls back largely smaller than and its location coordinate grows along marginal steps. -/
theorem isHom_lex_iff :
    ml.IsHom (lex β γ) f ↔ (∀ x y, ml.LargelyLT x y ↔ (ofLex (f x)).1 < (ofLex (f y)).1) ∧
      ∀ ⦃x y⦄, ml.MarginallyLT x y → (ofLex (f x)).2 < (ofLex (f y)).2 := by
  refine ⟨fun hf ↦ ⟨fun x y ↦ hf.largelyLT_iff.symm.trans lex_largelyLT_iff,
    fun x y h ↦ (lex_marginallyLT_iff.1 ((hf.marginallyLT_iff x y).2 h)).2⟩, fun ⟨hL, hM⟩ ↦ ?_⟩
  have hfst (x y : α) : (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y := by
    rw [atMostMarginal_iff_incompRel, IncompRel, hL, hL]
    grind
  refine ⟨fun x y hxy ↦ ?_, fun x y ↦ ?_⟩
  · rw [Prod.Lex.lt_iff, hfst]
    grind [marginallyLT_or_largelyLT_of_lt]
  · rw [lex_marginallyLT_iff, hfst]
    grind

theorem IsHom.fst_eq_fst_iff (hf : ml.IsHom (lex β γ) f) :
    (ofLex (f x)).1 = (ofLex (f y)).1 ↔ ml.AtMostMarginal x y :=
  lex_atMostMarginal_iff.symm.trans hf.atMostMarginal_iff

/-- An embedding of the blocks together with an embedding of the degrees of each block is a
homomorphism into lexicographic pairs. -/
theorem isHom_toLex (e : ml.Block ↪o β) (g : ∀ q, {x // ml.toBlock x = q} ↪o γ) :
    ml.IsHom (lex β γ) fun x ↦ toLex (e (ml.toBlock x), g (ml.toBlock x) ⟨x, rfl⟩) := by
  refine isHom_lex_iff.2 ⟨fun x y ↦ by simp, fun x y h ↦ ?_⟩
  have hg (q) (hq : ml.toBlock x = q) : g (ml.toBlock x) ⟨x, rfl⟩ = g q ⟨x, hq⟩ := by
    subst hq; rfl
  rw [ofLex_toLex, ofLex_toLex, hg _ (toBlock_eq_toBlock.2 h.atMostMarginal)]
  exact (g _).strictMono h.lt

end Lex

end MarginalScale
