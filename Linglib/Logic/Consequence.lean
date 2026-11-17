/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Concept

/-!
# Consequence

The semantics of a logic is a relation of satisfaction between models and formulas. A formula
$\varphi$ is a [consequence](##Entails) of a set $\Gamma$ of formulas when every model satisfying
$\Gamma$ satisfies $\varphi$, and taking consequences is [a closure
operator](##entails_iff_mem_intentClosure) on sets of formulas. With two notions of satisfaction
$p$ and $q$, a sequent $\Gamma \Rightarrow \Delta$ is a [mixed consequence](##MixedConsequence)
when every model that $p$-satisfies all of $\Gamma$ $q$-satisfies some member of $\Delta$, that
is, when [it has no countermodel](##mixedConsequence_iff_disjoint).

Mixed consequence is always monotone. It is [reflexive exactly when $p \le
q$](##stdRefl_mixedConsequence_iff) and [admits cut when $q \le
p$](##isTransitive_mixedConsequence). These rules characterize it: [every monotone relation
between sets of formulas is a mixed consequence](##monotone_iff_exists_mixedConsequence), and one
that is also reflexive and transitive is [the consequence relation of a single notion of
satisfaction](##stdRefl_and_monotone_and_isTransitive_iff_exists_mixedConsequence).

## Implementation notes

* A notion of satisfaction is a relation `Model → Formula → Prop`, and notions are ordered
  pointwise: `p ≤ q` says that whatever a model `p`-satisfies it also `q`-satisfies.
* The models of a set of formulas and the theory of a class of models are the polars
  `lowerPolar p Γ` and `upperPolar p K` of `Mathlib.Order.Concept`, without names of their own.
* Premises and conclusions are sets, as theories are in `Mathlib.ModelTheory`; a finite sequent
  is a set built with `insert`.
* For a relation `r` between sets of formulas, monotonicity is `Monotone (Function.uncurry r)`
  and reflexivity is `Std.Refl fun φ ψ ↦ r {φ} {ψ}`. Transitivity is cut for sets, which
  quantifies over the partitions of a set `Z` of cut formulas; a partition is given by its first
  block `Z₁ ⊆ Z`, the second being `Z \ Z₁`.

## References

* [cobreros-etal-2012]
* [chemla-egre-2019]
* [scott-1974]
* [shoesmith-smiley-1978]
* [tarski-1956]
-/

@[expose] public section

namespace Consequence

universe u v

variable {Model : Type v} {Formula : Type u}

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

/-- A sequent is valid exactly when the models `p`-satisfying every premise lie among those
`q`-satisfying some conclusion. -/
theorem mixedConsequence_iff_iInter_subset_iUnion :
    MixedConsequence p q Γ Δ ↔ ⋂ γ ∈ Γ, {M | p M γ} ⊆ ⋃ δ ∈ Δ, {M | q M δ} := by
  simp [MixedConsequence, Satisfies, Set.subset_def]

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

/-! ### Consequence under one notion of satisfaction -/

/-- `Γ ⊨[p] φ`: the formula `φ` is a consequence of `Γ` when every model satisfying all of `Γ`
satisfies `φ`. -/
def Entails (p : Model → Formula → Prop) (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ M, (∀ γ ∈ Γ, p M γ) → p M φ

@[inherit_doc] scoped notation:50 Γ " ⊨[" p "] " φ:51 => Entails p Γ φ

theorem entails_iff_mixedConsequence : Γ ⊨[p] φ ↔ MixedConsequence p p Γ {φ} :=
  mixedConsequence_singleton_right.symm

/-- The consequences of `Γ` are its closure under the closure operator of the satisfaction
relation, so consequence is extensive, monotone and idempotent ([tarski-1956], Axioms 2 and 3 of
*On some fundamental concepts of metamathematics*). -/
theorem entails_iff_mem_intentClosure : Γ ⊨[p] φ ↔ φ ∈ intentClosure p Γ :=
  .rfl

namespace Entails

theorem of_mem (h : φ ∈ Γ) : Γ ⊨[p] φ := fun _ hΓ ↦ hΓ φ h

theorem mono (hΓ : Γ ⊆ Γ') (h : Γ ⊨[p] φ) : Γ' ⊨[p] φ := fun M hM ↦ h M fun γ hγ ↦ hM γ (hΓ hγ)

/-- Whatever follows from consequences of `Γ` follows from `Γ`. -/
theorem trans (h₁ : ∀ θ ∈ Θ, Γ ⊨[p] θ) (h₂ : Θ ⊨[p] φ) : Γ ⊨[p] φ := fun M hM ↦
  h₂ M fun θ hθ ↦ h₁ θ hθ M hM

/-- Consequence transfers along a map of models that preserves and reflects satisfaction. -/
theorem comap {Model' : Type*} {p' : Model' → Formula → Prop} (f : Model' → Model)
    (hf : ∀ M ψ, p' M ψ ↔ p (f M) ψ) (h : Γ ⊨[p] φ) : Γ ⊨[p'] φ := fun M hM ↦
  (hf M φ).2 (h (f M) fun γ hγ ↦ (hf M γ).1 (hM γ hγ))

end Entails

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

/-! ### Relations between sets of formulas -/

section Representation

variable {r : Set Formula → Set Formula → Prop}

/-- A relation between sets of formulas is transitive when it is closed under cut for sets
([shoesmith-smiley-1978], §2.1): `Γ ⇒ Δ` holds if `Γ, Z₁ ⇒ Z₂, Δ` holds for every partition
`Z₁, Z₂` of a set `Z` of cut formulas. -/
def IsTransitive (r : Set Formula → Set Formula → Prop) : Prop :=
  ∀ ⦃Γ Δ : Set Formula⦄ (Z : Set Formula), (∀ Z₁ ⊆ Z, r (Γ ∪ Z₁) (Z \ Z₁ ∪ Δ)) → r Γ Δ

/-- Cut for one formula, rule (T) of [scott-1974]. -/
theorem IsTransitive.cut (h : IsTransitive r) (h₁ : r (insert φ Γ) Δ) (h₂ : r Γ (insert φ Δ)) :
    r Γ Δ :=
  h {φ} fun Z₁ hZ ↦ by
    rcases Set.subset_singleton_iff_eq.1 hZ with rfl | rfl
    · simpa using h₂
    · simpa using h₁

/-- A monotone relation that holds between each formula and itself holds between overlapping
sets, rule (R) of [scott-1974]. -/
theorem of_inter_nonempty (hm : Monotone (Function.uncurry r))
    (hr : Std.Refl fun φ ψ ↦ r {φ} {ψ}) (h : (Γ ∩ Δ).Nonempty) : r Γ Δ :=
  let ⟨φ, hΓ, hΔ⟩ := h
  hm (show (({φ}, {φ}) : Set Formula × Set Formula) ≤ (Γ, Δ) from
    ⟨Set.singleton_subset_iff.2 hΓ, Set.singleton_subset_iff.2 hΔ⟩) (hr.refl φ)

theorem monotone_uncurry_mixedConsequence :
    Monotone (Function.uncurry (MixedConsequence p q)) :=
  fun _ _ h ↦ MixedConsequence.weaken h.1 h.2

theorem isTransitive_mixedConsequence (hqp : q ≤ p) : IsTransitive (MixedConsequence p q) := by
  intro Γ Δ Z h M hΓ
  by_contra hΔ
  obtain ⟨δ, ⟨hZ, hn⟩ | hδ, hq⟩ := h {z ∈ Z | p M z} (Set.sep_subset _ _) M
    fun γ hγ ↦ hγ.elim (hΓ γ) fun h ↦ h.2
  · exact hn ⟨hZ, hqp M δ hq⟩
  · exact hΔ ⟨δ, hδ, hq⟩

/-- A monotone relation is the mixed consequence of any family of its non-instances `T i ⇏ U i`
that every non-instance extends to, with `i` satisfying a premise in `T i` and a conclusion
outside `U i`. -/
private theorem eq_mixedConsequence (hm : Monotone (Function.uncurry r)) {ι : Type u}
    (T U : ι → Set Formula) (hI : ∀ i, ¬ r (T i) (U i))
    (hc : ∀ Γ Δ, ¬ r Γ Δ → ∃ i, Γ ⊆ T i ∧ Δ ⊆ U i) :
    r = MixedConsequence (fun i φ ↦ φ ∈ T i) fun i φ ↦ φ ∉ U i := by
  ext Γ Δ
  refine ⟨fun h i hΓ ↦ ?_, fun h ↦ ?_⟩
  · by_contra hΔ
    exact hI i (hm (show (Γ, Δ) ≤ (T i, U i) from
      ⟨fun γ hγ ↦ hΓ γ hγ, fun δ hδ ↦ by_contra fun hn ↦ hΔ ⟨δ, hδ, hn⟩⟩) h)
  · by_contra hn
    obtain ⟨i, hΓ, hΔ⟩ := hc Γ Δ hn
    obtain ⟨δ, hδ, hq⟩ := h i fun γ hγ ↦ hΓ hγ
    exact hq (hΔ hδ)

/-- A relation between sets of formulas is monotone exactly when it is the mixed consequence of
two notions of satisfaction ([chemla-egre-2019], §3). -/
theorem monotone_iff_exists_mixedConsequence :
    Monotone (Function.uncurry r) ↔
      ∃ (Model : Type u) (p q : Model → Formula → Prop), r = MixedConsequence p q := by
  refine ⟨fun hm ↦ ⟨_, _, _, eq_mixedConsequence hm
    (ι := {x : Set Formula × Set Formula // ¬ r x.1 x.2}) (fun x ↦ x.1.1) (fun x ↦ x.1.2)
    (fun x ↦ x.2) fun Γ Δ h ↦ ⟨⟨(Γ, Δ), h⟩, subset_rfl, subset_rfl⟩⟩, ?_⟩
  rintro ⟨_, p, q, rfl⟩
  exact monotone_uncurry_mixedConsequence

/-- A relation between sets of formulas is reflexive and monotone exactly when it is a mixed
consequence whose premise standard is at least as strong as its conclusion standard
([chemla-egre-2019], §3). -/
theorem stdRefl_and_monotone_iff_exists_mixedConsequence :
    (Std.Refl fun φ ψ ↦ r {φ} {ψ}) ∧ Monotone (Function.uncurry r) ↔
      ∃ (Model : Type u) (p q : Model → Formula → Prop), p ≤ q ∧ r = MixedConsequence p q := by
  constructor
  · rintro ⟨hr, hm⟩
    obtain ⟨Model, p, q, rfl⟩ := monotone_iff_exists_mixedConsequence.1 hm
    exact ⟨Model, p, q, stdRefl_mixedConsequence_iff.1 hr, rfl⟩
  · rintro ⟨_, p, q, hpq, rfl⟩
    exact ⟨stdRefl_mixedConsequence_iff.2 hpq, monotone_uncurry_mixedConsequence⟩

/-- A relation between sets of formulas is monotone and transitive exactly when it is a mixed
consequence whose conclusion standard is at least as strong as its premise standard
([chemla-egre-2019], §3). -/
theorem monotone_and_isTransitive_iff_exists_mixedConsequence :
    Monotone (Function.uncurry r) ∧ IsTransitive r ↔
      ∃ (Model : Type u) (p q : Model → Formula → Prop), q ≤ p ∧ r = MixedConsequence p q := by
  constructor
  · rintro ⟨hm, ht⟩
    refine ⟨_, _, _, ?_, eq_mixedConsequence hm
      (ι := {x : Set Formula × Set Formula // ¬ r x.1 x.2 ∧ x.1 ∪ x.2 = Set.univ})
      (fun x ↦ x.1.1) (fun x ↦ x.1.2) (fun x ↦ x.2.1) fun Γ Δ h ↦ ?_⟩
    · intro x φ hq
      exact (Set.eq_univ_iff_forall.1 x.2.2 φ).resolve_right hq
    · obtain ⟨Z₁, -, hZ⟩ := not_forall₂.1 (mt (ht (Γ := Γ) (Δ := Δ) Set.univ) h)
      exact ⟨⟨(Γ ∪ Z₁, Set.univ \ Z₁ ∪ Δ), hZ, Set.eq_univ_of_forall fun φ ↦ by
        by_cases h : φ ∈ Z₁ <;> simp [h]⟩, Set.subset_union_left, Set.subset_union_right⟩
  · rintro ⟨_, p, q, hqp, rfl⟩
    exact ⟨monotone_uncurry_mixedConsequence, isTransitive_mixedConsequence hqp⟩

/-- A relation between sets of formulas is reflexive, monotone and transitive exactly when it is
the consequence relation of one notion of satisfaction ([scott-1974];
[shoesmith-smiley-1978], Theorem 2.1). -/
theorem stdRefl_and_monotone_and_isTransitive_iff_exists_mixedConsequence :
    (Std.Refl fun φ ψ ↦ r {φ} {ψ}) ∧ Monotone (Function.uncurry r) ∧ IsTransitive r ↔
      ∃ (Model : Type u) (p : Model → Formula → Prop), r = MixedConsequence p p := by
  constructor
  · rintro ⟨hr, hm, ht⟩
    obtain ⟨Model, p, q, hqp, rfl⟩ :=
      monotone_and_isTransitive_iff_exists_mixedConsequence.1 ⟨hm, ht⟩
    obtain rfl := le_antisymm (stdRefl_mixedConsequence_iff.1 hr) hqp
    exact ⟨Model, p, rfl⟩
  · rintro ⟨_, p, rfl⟩
    exact ⟨stdRefl_mixedConsequence_iff.2 le_rfl, monotone_uncurry_mixedConsequence,
      isTransitive_mixedConsequence le_rfl⟩

end Representation

end Consequence
