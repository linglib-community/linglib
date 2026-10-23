/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic

/-!
# Mixed consequence

A mixed consequence relation ([cobreros-etal-2012], Definition 17) reads the premises of a
sequent `Γ ⇒ Δ` by one notion of satisfaction and its conclusions by another: `Γ ⇒ Δ` is valid
when every model that `p`-satisfies all of `Γ` `q`-satisfies some member of `Δ`. With `p = q` this
is ordinary multiple-conclusion consequence. The strict, classical and tolerant satisfaction of
[cobreros-etal-2012] give nine such relations, among them the non-transitive `st`.

The structural behaviour of a mixed relation is fixed by how its two notions compare, in the
pointwise order on satisfaction relations. The relation is reflexive iff `p ≤ q`, closed under cut
when `q ≤ p`, and grows as `p` strengthens and `q` weakens (Lemma 7). Negation dualizes it
(Lemma 6), and the deduction theorem holds when the conditional is read at `q` with its
antecedent at `p` (Lemma 10).

## Main definitions

* `Consequence.Satisfies p q M Γ Δ`: the model `M` satisfies the sequent `Γ ⇒ Δ`.
* `Consequence.MixedConsequence p q Γ Δ`: every model satisfies it (Definition 17).
* `Consequence.IsDual neg p' p`: `p'` is the dual of `p` along `neg` (Definition 20).

## Main results

* `MixedConsequence.comap`: validity transfers along model correspondences (§2.2.2).
* `MixedConsequence.mono`: strength monotonicity (Lemma 7).
* `stdRefl_mixedConsequence_iff`: reflexivity holds iff `p ≤ q`.
* `MixedConsequence.cut`, `isTrans_mixedConsequence`: cut, and hence transitivity, when
  `q ≤ p`.
* `mixedConsequence_iff_dual`: `Γ ⇒ Δ` is valid iff `¬Δ ⇒ ¬Γ` is valid for the dual standards
  (Lemma 6).
* `mixedConsequence_cons_cons_iff`: the deduction theorem in sequent form (Lemma 10).

## Implementation notes

Satisfaction notions are relations `Model → Formula → Prop`, ordered pointwise, so `p ≤ q` says
that whatever a model `p`-satisfies it also `q`-satisfies. A family of notions indexed by modes,
like the three of [cobreros-etal-2012], enters by fixing the mode. Premises and conclusions are
lists: sequents are finite, as the deduction theorem requires.

## References

* [P. Cobreros, P. Égré, D. Ripley and R. van Rooij, *Tolerant, Classical, Strict*
  (2012)][cobreros-etal-2012]
-/

@[expose] public section

namespace Consequence

variable {Model Formula : Type*}

/-- The model `M` satisfies the sequent `Γ ⇒ Δ` with premises read by `p` and conclusions by `q`:
if it `p`-satisfies every premise, it `q`-satisfies some conclusion. -/
def Satisfies (p q : Model → Formula → Prop) (M : Model) (Γ Δ : List Formula) : Prop :=
  (∀ γ ∈ Γ, p M γ) → ∃ δ ∈ Δ, q M δ

/-- Mixed consequence ([cobreros-etal-2012], Definition 17): every model that `p`-satisfies all
the premises `q`-satisfies some conclusion. -/
def MixedConsequence (p q : Model → Formula → Prop) (Γ Δ : List Formula) : Prop :=
  ∀ M, Satisfies p q M Γ Δ

/-- `p'` is the dual of `p` along `neg` ([cobreros-etal-2012], Definition 20): a model
`p'`-satisfies `neg φ` exactly when it does not `p`-satisfy `φ`. -/
def IsDual (neg : Formula → Formula) (p' p : Model → Formula → Prop) : Prop :=
  ∀ M φ, p' M (neg φ) ↔ ¬ p M φ

variable {p p' q q' : Model → Formula → Prop} {M : Model} {Γ Γ' Δ Δ' : List Formula}
  {φ ψ : Formula}

/-- Cut at a single model: if `M` satisfies `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ`, it satisfies `Γ ⇒ Δ`,
provided `q`-satisfying the cut formula implies `p`-satisfying it. -/
theorem Satisfies.cut (hqp : q M φ → p M φ) (h₁ : Satisfies p q M (φ :: Γ) Δ)
    (h₂ : Satisfies p q M Γ (φ :: Δ)) : Satisfies p q M Γ Δ := fun hΓ ↦ by
  obtain ⟨δ, hδ, hq⟩ := h₂ hΓ
  rcases List.mem_cons.1 hδ with rfl | hδ
  · exact h₁ (List.forall_mem_cons.2 ⟨hqp hq, hΓ⟩)
  · exact ⟨δ, hδ, hq⟩

namespace MixedConsequence

/-- Validity transfers along a map of models that preserves the satisfaction of the premises and
reflects that of the conclusions: the model correspondences of [cobreros-etal-2012], §2.2.2. -/
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
    MixedConsequence p q Γ' Δ' := fun M hΓ' ↦
  (h M fun γ hγ ↦ hΓ' γ (hΓ hγ)).imp fun _ ↦ .imp_left (@hΔ _)

theorem of_mem (hpq : p ≤ q) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) : MixedConsequence p q Γ Δ :=
  fun M h ↦ ⟨φ, hΔ, hpq M φ (h φ hΓ)⟩

/-- Cut: from `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ` infer `Γ ⇒ Δ`, when `q ≤ p` (the form of transitivity in
[cobreros-etal-2012], §3.3.2). -/
theorem cut (hqp : q ≤ p) (h₁ : MixedConsequence p q (φ :: Γ) Δ)
    (h₂ : MixedConsequence p q Γ (φ :: Δ)) : MixedConsequence p q Γ Δ :=
  fun M ↦ (h₁ M).cut (hqp M φ) (h₂ M)

end MixedConsequence

@[simp] theorem mixedConsequence_singleton_right :
    MixedConsequence p q Γ [φ] ↔ ∀ M, (∀ γ ∈ Γ, p M γ) → q M φ := by
  simp [MixedConsequence, Satisfies]

/-- Definition 18 of [cobreros-etal-2012]: validity with no premises is `q`-validity. -/
theorem mixedConsequence_nil_singleton : MixedConsequence p q [] [φ] ↔ ∀ M, q M φ := by
  simp

/-- Definition 18 of [cobreros-etal-2012]: validity with no conclusions is `p`-unsatisfiability. -/
theorem mixedConsequence_singleton_nil : MixedConsequence p q [φ] [] ↔ ∀ M, ¬ p M φ := by
  simp [MixedConsequence, Satisfies]

theorem stdRefl_mixedConsequence_iff :
    Std.Refl (fun φ ψ ↦ MixedConsequence p q [φ] [ψ]) ↔ p ≤ q :=
  ⟨fun ⟨h⟩ M φ hp ↦ by simpa using h φ M (by simpa using hp),
    fun hpq ↦ ⟨fun _ ↦ .of_mem hpq (List.mem_singleton_self _) (List.mem_singleton_self _)⟩⟩

theorem isTrans_mixedConsequence (hqp : q ≤ p) :
    IsTrans Formula fun φ ψ ↦ MixedConsequence p q [φ] [ψ] :=
  ⟨fun _ ψ _ h₁ h₂ ↦ .cut (φ := ψ) hqp (h₂.weaken (by simp) (by simp))
    (h₁.weaken (by simp) (by simp))⟩

/-- Lemma 6 of [cobreros-etal-2012]: `Γ ⇒ Δ` is valid for `p, q` iff the negated sequent
`¬Δ ⇒ ¬Γ` is valid for their duals `q', p'`. -/
theorem mixedConsequence_iff_dual {neg : Formula → Formula} (hp : IsDual neg p' p)
    (hq : IsDual neg q' q) :
    MixedConsequence p q Γ Δ ↔ MixedConsequence q' p' (Δ.map neg) (Γ.map neg) := by
  refine forall_congr' fun M ↦ ?_
  simp only [Satisfies, List.forall_mem_map, hq M]
  simp only [List.mem_map, exists_exists_and_eq_and, hp M]
  grind

/-- Lemma 10 of [cobreros-etal-2012] in sequent form: a premise moves into the antecedent of a
conclusion when the conditional is `q`-satisfied just if its antecedent's `p`-satisfaction brings
its consequent's `q`-satisfaction. -/
theorem mixedConsequence_cons_cons_iff {imp : Formula → Formula → Formula}
    (himp : ∀ M, q M (imp φ ψ) ↔ (p M φ → q M ψ)) :
    MixedConsequence p q (φ :: Γ) (ψ :: Δ) ↔ MixedConsequence p q Γ (imp φ ψ :: Δ) := by
  refine forall_congr' fun M ↦ ?_
  simp only [Satisfies, List.mem_cons, exists_eq_or_imp, himp]
  grind

end Consequence
