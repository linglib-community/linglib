/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.CarcassiSteinertThrelkeldSzymanik2021

/-!
# Steinert-Threlkeld (2021): Quantifiers in Natural Language

[steinert-threlkeld-2021] grades two universals of determiner meanings over models, the pairs of
a restrictor and a scope. A submodel has the same restrictor and a smaller scope, and the degrees
of monotonicity are those of [carcassi-steinert-threlkeld-szymanik-2021] for that order. The
degree of conservativity is the uncertainty coefficient ([theil-1970]) of the truth value given
the truth value at the scope cut down to the restrictor. A determiner that is true at some model
and false at another has [upward degree `1` exactly when it is scope
monotone](##mon_eq_one_iff) and [degree of conservativity `1` exactly when it is
conservative](##cons_eq_one_iff).

## Implementation notes

* The universe is fixed. A submodel and a restriction share their universe with the model, so the
  conditions on the conditional entropies hold universe by universe; the paper's complexity
  measure ranges over models up to a fixed size.
* The degrees are those of the scope: upward and downward monotonicity and right conservativity.
  The paper also takes the restrictor variants and combines them by maximum and average.
* The paper's two experiments are not formalized. In the second it finds only very weak
  correlations between either degree and closeness to the estimated Pareto frontier of complexity
  and communicative cost in a random sample of languages, few of which come near the frontier.

## References

* [steinert-threlkeld-2021]
* [carcassi-steinert-threlkeld-szymanik-2021]
* [theil-1970]
-/

@[expose] public section

namespace SteinertThrelkeld2021

open MeasureTheory InformationTheory Quantifier Function CarcassiSteinertThrelkeldSzymanik2021

variable {α : Type*}

/-- A model is a restrictor with a scope. -/
structure Model (α : Type*) where
  /-- The restrictor of the model. -/
  restrictor : Set α
  /-- The scope of the model. -/
  scope : Set α

namespace Model

instance : MeasurableSpace (Model α) := ⊤

instance : DiscreteMeasurableSpace (Model α) := ⟨fun _ ↦ trivial⟩

/-- A submodel has the same restrictor and a smaller scope. -/
instance : Preorder (Model α) where
  le M N := M.restrictor = N.restrictor ∧ M.scope ⊆ N.scope
  le_refl _ := ⟨rfl, subset_rfl⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- The restriction of a model cuts its scope down to its restrictor. -/
def restrict (M : Model α) : Model α := ⟨M.restrictor, M.restrictor ∩ M.scope⟩

end Model

/-- A model verifies a determiner when the determiner holds of its restrictor and scope. -/
abbrev verifies (d : Det α) (M : Model α) : Prop := d M.restrictor M.scope

variable {d : Det α}

theorem monotone_verifies_iff : Monotone (verifies d) ↔ d.ScopeMonotone :=
  ⟨fun h A B B' hB hd ↦ h (a := ⟨A, B⟩) (b := ⟨A, B'⟩) ⟨rfl, hB⟩ hd,
    fun h M N hMN hd ↦ by
      obtain ⟨A, B⟩ := M
      obtain ⟨A', B'⟩ := N
      obtain ⟨rfl, hB⟩ := hMN
      exact h A hB hd⟩

theorem antitone_verifies_iff : Antitone (verifies d) ↔ d.ScopeAntitone :=
  ⟨fun h A B B' hB hd ↦ h (a := ⟨A, B⟩) (b := ⟨A, B'⟩) ⟨rfl, hB⟩ hd,
    fun h M N hMN hd ↦ by
      obtain ⟨A, B⟩ := M
      obtain ⟨A', B'⟩ := N
      obtain ⟨rfl, hB⟩ := hMN
      exact h A hB hd⟩

variable {μ : Measure (Model α)} [IsProbabilityMeasure μ]

/-- The degree of conservativity of a determiner: the share of the uncertainty about its truth
value at a model that is removed by knowing its truth value at the restriction of the model. -/
noncomputable def cons (d : Det α) (μ : Measure (Model α)) : ℝ :=
  uncertaintyCoeff (verifies d) (verifies d ∘ Model.restrict) μ

theorem condEntropy_restrict_eq_zero_iff (hμ : ∀ M, μ {M} ≠ 0) :
    H[verifies d | verifies d ∘ Model.restrict ; μ] = 0 ↔ d.Conservative := by
  refine (condEntropy_self_comp_eq_zero_iff hμ .of_discrete .of_discrete fun M ↦ by
    simp [Model.restrict]).trans ⟨fun h A B ↦ ?_, fun h ↦ ?_⟩
  · exact (congrFun h ⟨A, B⟩).symm.to_iff
  · exact funext fun M ↦ propext (h M.restrictor M.scope).symm

private theorem exists_verifies (h : ∃ A B, d A B) : ∃ M, verifies d M :=
  let ⟨A, B, hd⟩ := h; ⟨⟨A, B⟩, hd⟩

private theorem exists_not_verifies (h : ∃ A B, ¬ d A B) : ∃ M, ¬ verifies d M :=
  let ⟨A, B, hd⟩ := h; ⟨⟨A, B⟩, hd⟩

/-- A determiner true at some model and false at another has upward degree of monotonicity `1`
exactly when it is upward monotone in its scope. -/
theorem mon_eq_one_iff (hμ : ∀ M, μ {M} ≠ 0) (h₁ : ∃ A B, d A B) (h₀ : ∃ A B, ¬ d A B) :
    mon (verifies d) μ = 1 ↔ d.ScopeMonotone :=
  (CarcassiSteinertThrelkeldSzymanik2021.mon_eq_one_iff hμ (exists_verifies h₁)
    (exists_not_verifies h₀)).trans monotone_verifies_iff

/-- A determiner true at some model and false at another has downward degree of monotonicity `1`
exactly when it is downward monotone in its scope. -/
theorem monDown_eq_one_iff (hμ : ∀ M, μ {M} ≠ 0) (h₁ : ∃ A B, d A B) (h₀ : ∃ A B, ¬ d A B) :
    monDown (verifies d) μ = 1 ↔ d.ScopeAntitone :=
  (CarcassiSteinertThrelkeldSzymanik2021.monDown_eq_one_iff hμ (exists_verifies h₁)
    (exists_not_verifies h₀)).trans antitone_verifies_iff

/-- A determiner true at some model and false at another has degree of conservativity `1` exactly
when it is conservative. -/
theorem cons_eq_one_iff (hμ : ∀ M, μ {M} ≠ 0) (h₁ : ∃ A B, d A B) (h₀ : ∃ A B, ¬ d A B) :
    cons d μ = 1 ↔ d.Conservative := by
  obtain ⟨M, hM⟩ := exists_verifies h₁
  obtain ⟨N, hN⟩ := exists_not_verifies h₀
  rw [cons, uncertaintyCoeff_eq_one_iff μ .of_discrete .of_discrete
    (entropy_ne_zero_of_ne (X := verifies d) (a := M) (b := N) hμ .of_discrete
      fun h ↦ hN (h ▸ hM)),
    condEntropy_restrict_eq_zero_iff hμ]

/-! ### Two determiners -/

section examples

variable [Nonempty α]

/-- *Every* has upward degree of monotonicity `1` and degree of conservativity `1`. -/
example (hμ : ∀ M, μ {M} ≠ 0) :
    mon (verifies (Det.every : Det α)) μ = 1 ∧ cons (Det.every : Det α) μ = 1 :=
  have h₁ : ∃ A B : Set α, Det.every A B := ⟨∅, ∅, subset_rfl⟩
  have h₀ : ∃ A B : Set α, ¬ Det.every A B :=
    ⟨Set.univ, ∅, fun h ↦ h (Set.mem_univ (Classical.arbitrary α))⟩
  ⟨(mon_eq_one_iff hμ h₁ h₀).2 Det.scopeMonotone_every,
    (cons_eq_one_iff hμ h₁ h₀).2 Det.conservative_every⟩

/-- The relation of *only*, that the scope lies inside the restrictor, falls short of degree of
conservativity `1`. -/
example (hμ : ∀ M, μ {M} ≠ 0) : cons (fun A B : Set α ↦ B ⊆ A) μ ≠ 1 := fun h ↦
  have h₀ : ¬ (Set.univ : Set α) ⊆ ∅ := fun h ↦ h (Set.mem_univ (Classical.arbitrary α))
  h₀ (((cons_eq_one_iff (d := fun A B : Set α ↦ B ⊆ A) hμ ⟨∅, ∅, subset_rfl⟩
    ⟨∅, Set.univ, h₀⟩).1 h ∅ Set.univ).2 Set.inter_subset_left)

end examples

end SteinertThrelkeld2021
