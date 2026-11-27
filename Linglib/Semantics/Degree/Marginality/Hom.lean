/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Marginality.Constructions

/-!
# Homomorphisms of marginal scales

A [homomorphism](##MarginalScale.IsHom) of marginal scales preserves and reflects smaller than and
marginally smaller than, the representations of the measurement theory of [dinis-jacinto-2025]. It
[embeds the blocks of one scale in those of the other](##MarginalScale.IsHom.mapBlock), and a
homomorphism into lexicographic pairs is [an embedding of the blocks and of the degrees of each
block](##MarginalScale.isHomLexEquiv).

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
  strictMono : StrictMono f
  marginallyLT_iff : ∀ x y, ml'.MarginallyLT (f x) (f y) ↔ ml.MarginallyLT x y

section IsHom

variable {β γ : Type*} [LinearOrder β] [LinearOrder γ] {ml' : MarginalScale β}
  {ml'' : MarginalScale γ} {f : α → β} {g : β → γ}

theorem IsHom.largelyLT_iff (hf : ml.IsHom ml' f) : ml'.LargelyLT (f x) (f y) ↔ ml.LargelyLT x y :=
  and_congr hf.strictMono.lt_iff_lt (not_congr (hf.marginallyLT_iff x y))

theorem IsHom.atMostMarginal_iff (hf : ml.IsHom ml' f) :
    ml'.AtMostMarginal (f x) (f y) ↔ ml.AtMostMarginal x y := by
  simp only [atMostMarginal_iff_incompRel, IncompRel, hf.largelyLT_iff]

theorem IsHom.injective (hf : ml.IsHom ml' f) : Function.Injective f := hf.strictMono.injective

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

/-- A homomorphism of marginal scales embeds the blocks of one in the blocks of the other. -/
noncomputable def IsHom.mapBlock (hf : ml.IsHom ml' f) : ml.Block ↪o ml'.Block :=
  OrderEmbedding.ofStrictMono
    (Quotient.lift (fun x ↦ ml'.toBlock (f x)) fun _ _ h ↦
      toBlock_eq_toBlock.2 (hf.atMostMarginal_iff.2 (toBlock_eq_toBlock.1 (Quotient.sound h))))
    fun a b ↦ Quotient.inductionOn₂ a b fun _ _ h ↦
      toBlock_lt_toBlock.2 (hf.largelyLT_iff.2 (toBlock_lt_toBlock.1 h))

@[simp]
theorem IsHom.mapBlock_toBlock (hf : ml.IsHom ml' f) (x : α) :
    hf.mapBlock (ml.toBlock x) = ml'.toBlock (f x) :=
  rfl

variable (ml) in
@[simp]
theorem IsHom.mapBlock_id : (IsHom.id ml).mapBlock = RelEmbedding.refl _ :=
  DFunLike.ext _ _ <| Block.ind fun _ ↦ rfl

theorem IsHom.mapBlock_comp (hg : ml'.IsHom ml'' g) (hf : ml.IsHom ml' f) :
    (hg.comp hf).mapBlock = hf.mapBlock.trans hg.mapBlock :=
  DFunLike.ext _ _ <| Block.ind fun _ ↦ rfl

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

/-- The block coordinate of a homomorphism into lexicographic pairs embeds the blocks. -/
noncomputable def IsHom.fstOrderEmbedding [Nonempty γ] (hf : ml.IsHom (lex β γ) f) :
    ml.Block ↪o β :=
  hf.mapBlock.trans (lexBlockOrderIso β γ).toOrderEmbedding

@[simp]
theorem IsHom.fstOrderEmbedding_toBlock [Nonempty γ] (hf : ml.IsHom (lex β γ) f) (x : α) :
    hf.fstOrderEmbedding (ml.toBlock x) = (ofLex (f x)).1 :=
  rfl

/-- The location coordinate of a homomorphism into lexicographic pairs embeds the degrees of each
block. -/
def IsHom.sndOrderEmbedding (hf : ml.IsHom (lex β γ) f) (q : ml.Block) :
    {x // ml.toBlock x = q} ↪o γ :=
  OrderEmbedding.ofStrictMono (fun x ↦ (ofLex (f x)).2) fun a b hab ↦
    (isHom_lex_iff.1 hf).2 <| marginallyLT_iff_lt_and_atMostMarginal.2
      ⟨hab, toBlock_eq_toBlock.1 (a.2.trans b.2.symm)⟩

@[simp]
theorem IsHom.sndOrderEmbedding_apply (hf : ml.IsHom (lex β γ) f) (q : ml.Block)
    (x : {x // ml.toBlock x = q}) : hf.sndOrderEmbedding q x = (ofLex (f x)).2 :=
  rfl

variable (ml β γ) in
/-- A homomorphism into lexicographic pairs is an embedding of the blocks together with an
embedding of the degrees of each block. -/
noncomputable def isHomLexEquiv [Nonempty γ] : {f : α → β ×ₗ γ // ml.IsHom (lex β γ) f} ≃
    (ml.Block ↪o β) × ∀ q, {x // ml.toBlock x = q} ↪o γ where
  toFun f := (f.2.fstOrderEmbedding, f.2.sndOrderEmbedding)
  invFun p := ⟨_, isHom_toLex p.1 p.2⟩
  left_inv _ := rfl
  right_inv p := Prod.ext (DFunLike.ext _ _ <| Block.ind fun _ ↦ rfl) <| funext fun q ↦
    DFunLike.ext _ _ fun ⟨x, hx⟩ ↦ by subst hx; rfl

end Lex

end MarginalScale
