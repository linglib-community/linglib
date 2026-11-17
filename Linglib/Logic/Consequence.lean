/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Concept

/-!
# Mixed consequence

A notion of satisfaction is a relation between models and formulas. A sequent `Γ ⇒ Δ` between sets
of formulas is a *mixed consequence* for two such notions `p` and `q` when every model that
`p`-satisfies all of `Γ` `q`-satisfies some member of `Δ` ([cobreros-etal-2012]); with `p = q` this
is ordinary multiple-conclusion consequence. Equivalently [no model is a
counterexample](##Consequence.mixedConsequence_iff_disjoint), and the single conclusions of `Γ` are
[the `q`-theory of its `p`-models](##Consequence.mixedConsequence_singleton_iff_mem_upperPolar),
which for `p = q` is [a closure
operator](##Consequence.mixedConsequence_singleton_iff_mem_intentClosure).

How `p` and `q` compare in the pointwise order fixes the structural rules. The relation is
[reflexive exactly when `p ≤ q`](##Consequence.stdRefl_mixedConsequence_iff), it is
[transitive](##Consequence.MixedConsequence.trans) and admits
[cut](##Consequence.MixedConsequence.cut) when `q ≤ p`, and it [grows as `p` strengthens and `q`
weakens](##Consequence.MixedConsequence.mono). Negation [dualizes
it](##Consequence.mixedConsequence_iff_dual), and a premise [moves into the antecedent of a
conditional](##Consequence.mixedConsequence_insert_insert_iff) read at `q` with its antecedent at
`p`.

## Implementation notes

Satisfaction notions are relations `Model → Formula → Prop`, ordered pointwise, so `p ≤ q` says
that whatever a model `p`-satisfies it also `q`-satisfies. The models of a set of formulas and the
theory of a class of models are the polars `lowerPolar p Γ` and `upperPolar p K` of
`Mathlib.Order.Concept`, and are not given names of their own. Premises and conclusions are sets,
as theories are in `Mathlib.ModelTheory`; a finite sequent is a set built with `insert`.

## References

* [P. Cobreros, P. Égré, D. Ripley and R. van Rooij, *Tolerant, Classical, Strict*
  (2012)][cobreros-etal-2012]
-/

@[expose] public section

namespace Consequence

variable {Model Formula : Type*}

/-- The model `M` satisfies the sequent `Γ ⇒ Δ` with premises read by `p` and conclusions by `q`:
if it `p`-satisfies every premise, it `q`-satisfies some conclusion. -/
def Satisfies (p q : Model → Formula → Prop) (M : Model) (Γ Δ : Set Formula) : Prop :=
  (∀ γ ∈ Γ, p M γ) → ∃ δ ∈ Δ, q M δ

/-- Mixed consequence ([cobreros-etal-2012], Definition 17): every model that `p`-satisfies all
the premises `q`-satisfies some conclusion. -/
def MixedConsequence (p q : Model → Formula → Prop) (Γ Δ : Set Formula) : Prop :=
  ∀ M, Satisfies p q M Γ Δ

/-- `p'` is the dual of `p` along `neg` ([cobreros-etal-2012], Definition 20): a model
`p'`-satisfies `neg φ` exactly when it does not `p`-satisfy `φ`. -/
def IsDual (neg : Formula → Formula) (p' p : Model → Formula → Prop) : Prop :=
  ∀ M φ, p' M (neg φ) ↔ ¬ p M φ

variable {p p' q q' : Model → Formula → Prop} {M : Model} {Γ Γ' Δ Δ' Θ : Set Formula}
  {φ ψ : Formula}

/-! ### Satisfaction at a model -/

/-- A model fails a sequent exactly when it is a counterexample: it `p`-satisfies every premise
and `q`-satisfies no conclusion. -/
theorem not_satisfies_iff :
    ¬ Satisfies p q M Γ Δ ↔ M ∈ lowerPolar p Γ ∩ lowerPolar qᶜ Δ := by
  simp [Satisfies, mem_lowerPolar_iff]

theorem Satisfies.weaken (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') (h : Satisfies p q M Γ Δ) :
    Satisfies p q M Γ' Δ' := fun hΓ' ↦
  (h fun γ hγ ↦ hΓ' γ (hΓ hγ)).imp fun _ ↦ .imp_left (@hΔ _)

/-- Cut at a single model: if `M` satisfies `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ`, it satisfies `Γ ⇒ Δ`,
provided `q`-satisfying the cut formula implies `p`-satisfying it. -/
theorem Satisfies.cut (hqp : q M φ → p M φ) (h₁ : Satisfies p q M (insert φ Γ) Δ)
    (h₂ : Satisfies p q M Γ (insert φ Δ)) : Satisfies p q M Γ Δ := fun hΓ ↦ by
  obtain ⟨δ, rfl | hδ, hq⟩ := h₂ hΓ
  · exact h₁ (Set.forall_mem_insert.2 ⟨hqp hq, hΓ⟩)
  · exact ⟨δ, hδ, hq⟩

/-! ### Polars -/

/-- A sequent is valid exactly when it has no counterexample: the models `p`-satisfying every
premise are disjoint from those `q`-satisfying no conclusion. -/
theorem mixedConsequence_iff_disjoint :
    MixedConsequence p q Γ Δ ↔ Disjoint (lowerPolar p Γ) (lowerPolar qᶜ Δ) := by
  simp only [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem, ← not_satisfies_iff,
    not_not, MixedConsequence]

@[simp] theorem mixedConsequence_singleton_right :
    MixedConsequence p q Γ {φ} ↔ ∀ M, (∀ γ ∈ Γ, p M γ) → q M φ := by
  simp [MixedConsequence, Satisfies]

/-- The single conclusions of `Γ` are the formulas `q`-satisfied by every model that
`p`-satisfies `Γ`. -/
theorem mixedConsequence_singleton_iff_mem_upperPolar :
    MixedConsequence p q Γ {φ} ↔ φ ∈ upperPolar q (lowerPolar p Γ) :=
  mixedConsequence_singleton_right

/-- With one notion of satisfaction, the single conclusions of `Γ` are its closure under the
closure operator of the satisfaction relation. -/
theorem mixedConsequence_singleton_iff_mem_intentClosure :
    MixedConsequence p p Γ {φ} ↔ φ ∈ intentClosure p Γ :=
  mixedConsequence_singleton_right

@[simp] theorem mixedConsequence_singleton_singleton :
    MixedConsequence p q {φ} {ψ} ↔ ∀ M, p M φ → q M ψ := by
  simp

/-- Definition 18 of [cobreros-etal-2012]: validity with no premises is `q`-validity. -/
theorem mixedConsequence_empty_singleton : MixedConsequence p q ∅ {φ} ↔ ∀ M, q M φ := by
  simp

/-- Definition 18 of [cobreros-etal-2012]: validity with no conclusions is `p`-unsatisfiability. -/
theorem mixedConsequence_singleton_empty : MixedConsequence p q {φ} ∅ ↔ ∀ M, ¬ p M φ := by
  simp [MixedConsequence, Satisfies]

/-! ### Structural rules -/

namespace MixedConsequence

/-- Validity transfers along a map of models preserving premise satisfaction and reflecting
conclusion satisfaction ([cobreros-etal-2012], §2.2.2). -/
theorem comap {Model' : Type*} {p' q' : Model' → Formula → Prop} (f : Model' → Model)
    (hp : ∀ M, ∀ γ ∈ Γ, p' M γ → p (f M) γ) (hq : ∀ M, ∀ δ ∈ Δ, q (f M) δ → q' M δ)
    (h : MixedConsequence p q Γ Δ) : MixedConsequence p' q' Γ Δ := fun M hΓ ↦
  (h (f M) fun γ hγ ↦ hp M γ hγ (hΓ γ hγ)).imp fun δ ⟨hδ, hqδ⟩ ↦ ⟨hδ, hq M δ hδ hqδ⟩

/-- Lemma 7 of [cobreros-etal-2012]: holding premises to a stronger standard, or conclusions to a
weaker one, preserves validity. -/
theorem mono (hp : p' ≤ p) (hq : q ≤ q') (h : MixedConsequence p q Γ Δ) :
    MixedConsequence p' q' Γ Δ :=
  h.comap id (fun M γ _ ↦ hp M γ) fun M δ _ ↦ hq M δ

theorem weaken (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') (h : MixedConsequence p q Γ Δ) :
    MixedConsequence p q Γ' Δ' := fun M ↦ (h M).weaken hΓ hΔ

theorem of_mem (hpq : p ≤ q) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) : MixedConsequence p q Γ Δ :=
  fun M h ↦ ⟨φ, hΔ, hpq M φ (h φ hΓ)⟩

/-- From `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ` infer `Γ ⇒ Δ` when `q ≤ p` ([cobreros-etal-2012], §3.3.2). -/
theorem cut (hqp : q ≤ p) (h₁ : MixedConsequence p q (insert φ Γ) Δ)
    (h₂ : MixedConsequence p q Γ (insert φ Δ)) : MixedConsequence p q Γ Δ :=
  fun M ↦ (h₁ M).cut (hqp M φ) (h₂ M)

/-- When `q ≤ p`, whatever follows from consequences of `Γ` follows from `Γ`. -/
theorem trans (hqp : q ≤ p) (h₁ : ∀ θ ∈ Θ, MixedConsequence p q Γ {θ})
    (h₂ : MixedConsequence p q Θ Δ) : MixedConsequence p q Γ Δ := fun M hΓ ↦
  h₂ M fun θ hθ ↦ hqp M θ (mixedConsequence_singleton_right.1 (h₁ θ hθ) M hΓ)

end MixedConsequence

/-- The single-premise, single-conclusion relation is reflexive exactly when `p ≤ q`. -/
theorem stdRefl_mixedConsequence_iff :
    Std.Refl (fun φ ψ ↦ MixedConsequence p q {φ} {ψ}) ↔ p ≤ q :=
  ⟨fun ⟨h⟩ M φ ↦ mixedConsequence_singleton_singleton.1 (h φ) M,
    fun hpq ↦ ⟨fun _ ↦ .of_mem hpq rfl rfl⟩⟩

/-- The single-premise, single-conclusion relation is transitive when `q ≤ p`. -/
theorem isTrans_mixedConsequence (hqp : q ≤ p) :
    IsTrans Formula fun φ ψ ↦ MixedConsequence p q {φ} {ψ} :=
  ⟨fun _ _ _ h₁ h₂ ↦ h₂.trans hqp (Set.forall_mem_singleton.2 h₁)⟩

/-! ### Connectives -/

/-- `Γ ⇒ Δ` is valid for `p, q` iff `¬Δ ⇒ ¬Γ` is valid for their duals `q', p'` (Lemma 6 of
[cobreros-etal-2012]). -/
theorem mixedConsequence_iff_dual {neg : Formula → Formula} (hp : IsDual neg p' p)
    (hq : IsDual neg q' q) :
    MixedConsequence p q Γ Δ ↔ MixedConsequence q' p' (neg '' Δ) (neg '' Γ) := by
  refine forall_congr' fun M ↦ ?_
  simp only [Satisfies, Set.forall_mem_image, Set.exists_mem_image, hp M, hq M]
  grind

/-- A premise moves into the antecedent of a conclusion when the conditional is `q`-satisfied iff
`p`-satisfaction of its antecedent implies `q`-satisfaction of its consequent (Lemma 10 of
[cobreros-etal-2012]). -/
theorem mixedConsequence_insert_insert_iff {imp : Formula → Formula → Formula}
    (himp : ∀ M, q M (imp φ ψ) ↔ (p M φ → q M ψ)) :
    MixedConsequence p q (insert φ Γ) (insert ψ Δ) ↔
      MixedConsequence p q Γ (insert (imp φ ψ) Δ) := by
  refine forall_congr' fun M ↦ ?_
  simp only [Satisfies, Set.forall_mem_insert, Set.exists_mem_insert, himp]
  grind

end Consequence
