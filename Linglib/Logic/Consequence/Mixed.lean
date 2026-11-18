/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Consequence.Basic
public import Linglib.Logic.Consequence.Structural

/-!
# Mixed consequence

With two notions of satisfaction $p$ and $q$, a sequent $\Gamma \Rightarrow \Delta$ between sets
of formulas is a [mixed consequence](##MixedConsequence) when every model that $p$-satisfies all
of $\Gamma$ $q$-satisfies some member of $\Delta$ ([cobreros-etal-2012]), that is, when [it has no
countermodel](##mixedConsequence_iff_disjoint). With $p = q$ and a single conclusion this is
[ordinary consequence](##entails_iff_mixedConsequence).

Mixed consequence is [monotone](##monotone_uncurry_mixedConsequence). It is [reflexive exactly
when $p \le q$](##stdRefl_mixedConsequence_iff) and [transitive when $q \le
p$](##isTransitive_mixedConsequence). These rules characterize it: [every monotone relation
between sets of formulas is a mixed consequence](##monotone_iff_exists_mixedConsequence), with [$p
\le q$ if it is reflexive](##monotone_stdRefl_iff_exists_mixedConsequence) and [$q \le p$ if it
is transitive](##monotone_isTransitive_iff_exists_mixedConsequence) ([chemla-egre-2019]), and one
with all three rules is [the consequence relation of a single notion of
satisfaction](##monotone_stdRefl_isTransitive_iff_exists_mixedConsequence) ([scott-1974],
[shoesmith-smiley-1978]). Negation [dualizes](##mixedConsequence_iff_dual) mixed consequence, and
a premise [moves into the antecedent](##mixedConsequence_insert_insert_iff) of a conditional read
at $q$ with its antecedent at $p$.

## Implementation notes

Notions of satisfaction are ordered pointwise: `p ≤ q` says that whatever a model `p`-satisfies
it also `q`-satisfies. `MixedConsequence.mono` varies the two notions and
`MixedConsequence.weaken` the two sets of formulas. A finite sequent is a set built with `insert`.

## References

* [cobreros-etal-2012]
* [chemla-egre-2019]
* [scott-1974]
* [shoesmith-smiley-1978]
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

variable {p p' q q' : Model → Formula → Prop} {M : Model} {Γ Γ' Δ Δ' Θ : Set Formula}
  {φ ψ : Formula}

/-! ### Countermodels -/

/-- A model fails a sequent exactly when it is a countermodel: it `p`-satisfies every premise
and `q`-satisfies no conclusion. -/
theorem not_satisfies_iff :
    ¬ Satisfies p q M Γ Δ ↔ M ∈ lowerPolar p Γ ∩ lowerPolar qᶜ Δ := by
  simp [Satisfies, mem_lowerPolar_iff]

/-- A sequent is valid exactly when it has no countermodel: the models `p`-satisfying every
premise are disjoint from those `q`-satisfying no conclusion. -/
theorem mixedConsequence_iff_disjoint :
    MixedConsequence p q Γ Δ ↔ Disjoint (lowerPolar p Γ) (lowerPolar qᶜ Δ) := by
  simp only [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem, ← not_satisfies_iff,
    not_not, MixedConsequence]

/-- A sequent is valid exactly when the models `p`-satisfying every premise lie among those
`q`-satisfying some conclusion. -/
theorem mixedConsequence_iff_iInter_subset_iUnion :
    MixedConsequence p q Γ Δ ↔ ⋂ γ ∈ Γ, {M | p M γ} ⊆ ⋃ δ ∈ Δ, {M | q M δ} := by
  simp [MixedConsequence, Satisfies, Set.subset_def]

/-! ### Small sequents -/

@[simp] theorem mixedConsequence_singleton_right :
    MixedConsequence p q Γ {φ} ↔ ∀ M, (∀ γ ∈ Γ, p M γ) → q M φ := by
  simp [MixedConsequence, Satisfies]

/-- The single conclusions of `Γ` are the formulas `q`-satisfied by every model that
`p`-satisfies `Γ`. -/
theorem mixedConsequence_singleton_iff_mem_upperPolar :
    MixedConsequence p q Γ {φ} ↔ φ ∈ upperPolar q (lowerPolar p Γ) :=
  mixedConsequence_singleton_right

/-- With one notion of satisfaction and one conclusion, mixed consequence is consequence. -/
theorem entails_iff_mixedConsequence : Γ ⊨[p] φ ↔ MixedConsequence p p Γ {φ} :=
  mixedConsequence_singleton_right.symm

@[simp] theorem mixedConsequence_singleton_singleton :
    MixedConsequence p q {φ} {ψ} ↔ ∀ M, p M φ → q M ψ := by
  simp

/-- Definition 18 of [cobreros-etal-2012]: validity with no premises is `q`-validity. -/
theorem mixedConsequence_empty_singleton : MixedConsequence p q ∅ {φ} ↔ ∀ M, q M φ := by
  simp

/-- Definition 18 of [cobreros-etal-2012]: validity with no conclusions is `p`-unsatisfiability. -/
theorem mixedConsequence_singleton_empty : MixedConsequence p q {φ} ∅ ↔ ∀ M, ¬ p M φ := by
  simp [MixedConsequence, Satisfies]

/-! ### Changing the models and the notions of satisfaction -/

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

end MixedConsequence

/-! ### Structural rules -/

/-- Mixed consequence survives added premises and conclusions. -/
theorem monotone_uncurry_mixedConsequence :
    Monotone (Function.uncurry (MixedConsequence p q)) :=
  fun _ _ hle h M hΓ ↦ (h M fun γ hγ ↦ hΓ γ (hle.1 hγ)).imp fun _ ↦ .imp_left (@hle.2 _)

/-- Mixed consequence is reflexive exactly when `p ≤ q`. -/
theorem stdRefl_mixedConsequence_iff :
    Std.Refl (fun φ ψ ↦ MixedConsequence p q {φ} {ψ}) ↔ p ≤ q :=
  ⟨fun ⟨h⟩ M φ ↦ mixedConsequence_singleton_singleton.1 (h φ) M,
    fun hpq ↦ ⟨fun φ ↦ mixedConsequence_singleton_singleton.2 fun M ↦ hpq M φ⟩⟩

/-- Mixed consequence is closed under cut for sets when `q ≤ p`. -/
theorem isTransitive_mixedConsequence (hqp : q ≤ p) : IsTransitive (MixedConsequence p q) := by
  intro Γ Δ Z h M hΓ
  by_contra hΔ
  obtain ⟨δ, ⟨hZ, hn⟩ | hδ, hq⟩ := h {z ∈ Z | p M z} (Set.sep_subset _ _) M
    fun γ hγ ↦ hγ.elim (hΓ γ) fun h ↦ h.2
  · exact hn ⟨hZ, hqp M δ hq⟩
  · exact hΔ ⟨δ, hδ, hq⟩

namespace MixedConsequence

theorem weaken (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') (h : MixedConsequence p q Γ Δ) :
    MixedConsequence p q Γ' Δ' :=
  monotone_uncurry_mixedConsequence (show (Γ, Δ) ≤ (Γ', Δ') from ⟨hΓ, hΔ⟩) h

theorem of_mem (hpq : p ≤ q) (hΓ : φ ∈ Γ) (hΔ : φ ∈ Δ) : MixedConsequence p q Γ Δ :=
  overlap monotone_uncurry_mixedConsequence (stdRefl_mixedConsequence_iff.2 hpq) ⟨φ, hΓ, hΔ⟩

/-- From `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ` infer `Γ ⇒ Δ` when `q ≤ p` ([cobreros-etal-2012], §3.3.2). -/
theorem cut (hqp : q ≤ p) (h₁ : MixedConsequence p q (insert φ Γ) Δ)
    (h₂ : MixedConsequence p q Γ (insert φ Δ)) : MixedConsequence p q Γ Δ :=
  (isTransitive_mixedConsequence hqp).cut h₁ h₂

/-- When `q ≤ p`, whatever follows from single conclusions of `Γ` follows from `Γ`. -/
theorem trans (hqp : q ≤ p) (h₁ : ∀ θ ∈ Θ, MixedConsequence p q Γ {θ})
    (h₂ : MixedConsequence p q Θ Δ) : MixedConsequence p q Γ Δ :=
  (isTransitive_mixedConsequence hqp).trans monotone_uncurry_mixedConsequence h₁ h₂

end MixedConsequence

/-- The single-premise, single-conclusion relation is transitive when `q ≤ p`. -/
theorem isTrans_mixedConsequence (hqp : q ≤ p) :
    IsTrans Formula fun φ ψ ↦ MixedConsequence p q {φ} {ψ} :=
  (isTransitive_mixedConsequence hqp).isTrans monotone_uncurry_mixedConsequence

/-- Cut at a single model: if `M` satisfies `φ, Γ ⇒ Δ` and `Γ ⇒ φ, Δ`, it satisfies `Γ ⇒ Δ`,
provided `q`-satisfying the cut formula implies `p`-satisfying it. -/
theorem Satisfies.cut (hqp : q M φ → p M φ) (h₁ : Satisfies p q M (insert φ Γ) Δ)
    (h₂ : Satisfies p q M Γ (insert φ Δ)) : Satisfies p q M Γ Δ := fun hΓ ↦ by
  obtain ⟨δ, rfl | hδ, hq⟩ := h₂ hΓ
  · exact h₁ (Set.forall_mem_insert.2 ⟨hqp hq, hΓ⟩)
  · exact ⟨δ, hδ, hq⟩

/-! ### Representation -/

section Representation

variable {r : Set Formula → Set Formula → Prop}

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

/-- A relation between sets of formulas is monotone and reflexive exactly when it is a mixed
consequence whose premise standard is at least as strong as its conclusion standard
([chemla-egre-2019], §3). -/
theorem monotone_stdRefl_iff_exists_mixedConsequence :
    Monotone (Function.uncurry r) ∧ (Std.Refl fun φ ψ ↦ r {φ} {ψ}) ↔
      ∃ (Model : Type u) (p q : Model → Formula → Prop), p ≤ q ∧ r = MixedConsequence p q := by
  constructor
  · rintro ⟨hm, hr⟩
    obtain ⟨Model, p, q, rfl⟩ := monotone_iff_exists_mixedConsequence.1 hm
    exact ⟨Model, p, q, stdRefl_mixedConsequence_iff.1 hr, rfl⟩
  · rintro ⟨_, p, q, hpq, rfl⟩
    exact ⟨monotone_uncurry_mixedConsequence, stdRefl_mixedConsequence_iff.2 hpq⟩

/-- A relation between sets of formulas is monotone and transitive exactly when it is a mixed
consequence whose conclusion standard is at least as strong as its premise standard
([chemla-egre-2019], §3). -/
theorem monotone_isTransitive_iff_exists_mixedConsequence :
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

/-- A relation between sets of formulas is monotone, reflexive and transitive exactly when it is
the consequence relation of one notion of satisfaction ([scott-1974];
[shoesmith-smiley-1978], Theorem 2.1). -/
theorem monotone_stdRefl_isTransitive_iff_exists_mixedConsequence :
    Monotone (Function.uncurry r) ∧ (Std.Refl fun φ ψ ↦ r {φ} {ψ}) ∧ IsTransitive r ↔
      ∃ (Model : Type u) (p : Model → Formula → Prop), r = MixedConsequence p p := by
  constructor
  · rintro ⟨hm, hr, ht⟩
    obtain ⟨Model, p, q, hqp, rfl⟩ :=
      monotone_isTransitive_iff_exists_mixedConsequence.1 ⟨hm, ht⟩
    obtain rfl := le_antisymm (stdRefl_mixedConsequence_iff.1 hr) hqp
    exact ⟨Model, p, rfl⟩
  · rintro ⟨_, p, rfl⟩
    exact ⟨monotone_uncurry_mixedConsequence, stdRefl_mixedConsequence_iff.2 le_rfl,
      isTransitive_mixedConsequence le_rfl⟩

end Representation

/-! ### Connectives -/

/-- `p'` is the dual of `p` along `neg` ([cobreros-etal-2012], Definition 20): a model
`p'`-satisfies `neg φ` exactly when it does not `p`-satisfy `φ`. -/
def IsDual (neg : Formula → Formula) (p' p : Model → Formula → Prop) : Prop :=
  ∀ M φ, p' M (neg φ) ↔ ¬ p M φ

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
