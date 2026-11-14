/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.CarcassiSteinertThrelkeldSzymanik2021
public import Studies.ZaslavskyKempRegierTishby2018

/-!
# Steinert-Threlkeld and Szymanik (2026): Computational Explanations of Semantic Universals

[steinert-threlkeld-szymanik-2026] survey explanations of lexical universals by ease of learning
and by efficient communication, grading each universal by a degree. For monotonicity they propose
comparing the degree of [carcassi-steinert-threlkeld-szymanik-2021] with one that finds the
closest monotone function. *All or none* separates the two: it [differs from a monotone
quantifier at a single structure](##exists_monotone_ne_allOrNone), in either direction, and has
[degree `0` in both](##mon_allOrNone). On efficient communication they observe that the
complexity of a lexicon naming each meaning by one word [depends only on how often each word is
used](##complexity_deterministic_congr), not on the shape of its categories.

## Implementation notes

* Closeness to a monotone quantifier is measured by the structures at which the two disagree, the
  distance to monotonicity of [goldreich-etal-2000]. The source fixes no distance.

## TODO

* The degree of a function between ordered sets, measured against its least monotone majorant,
  is `1` exactly for monotone functions when the values are linearly ordered.

## References

* [steinert-threlkeld-szymanik-2026]
* [carcassi-steinert-threlkeld-szymanik-2021]
* [goldreich-etal-2000]
* [zaslavsky-kemp-regier-tishby-2018]
-/

@[expose] public section

namespace SteinertThrelkeldSzymanik2026

open MeasureTheory ProbabilityTheory InformationTheory Quantifier

/-! ### A quantifier one structure from monotone with degree zero -/

section monotonicity

open CarcassiSteinertThrelkeldSzymanik2021

variable {α : Type*}

/-- *All or none*: the scope holds of every individual or of none. -/
def allOrNone : Quantifier α := (Det.every ⊔ Det.no) Set.univ

theorem allOrNone_iff {B : Set α} : allOrNone B ↔ B = Set.univ ∨ B = ∅ := by
  simp [allOrNone, Det.every, Det.no, Set.univ_subset_iff]

/-- *All or none* differs from the upward monotone *every* at the empty scope alone, and from the
downward monotone *no* at the full scope alone. -/
theorem exists_monotone_ne_allOrNone [Nonempty α] :
    (∃ g : Quantifier α, Monotone g ∧ {B | allOrNone B ≠ g B} = {∅}) ∧
      ∃ g : Quantifier α, Antitone g ∧ {B | allOrNone B ≠ g B} = {Set.univ} := by
  refine ⟨⟨Det.every Set.univ, Det.scopeMonotone_every _, Set.ext fun B ↦ ?_⟩,
    Det.no Set.univ, Det.scopeAntitone_no _, Set.ext fun B ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, ne_eq, eq_iff_iff, allOrNone_iff, Det.every,
      Set.univ_subset_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by_contra fun hB ↦ h ⟨fun h' ↦ h'.resolve_right hB, .inl⟩,
      fun hB h ↦ Set.empty_ne_univ (hB ▸ h.1 (.inr hB))⟩
  · simp only [Set.mem_ofPred_eq, ne_eq, eq_iff_iff, allOrNone_iff, Det.no,
      Set.univ_subset_iff, Set.compl_univ_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by_contra fun hB ↦ h ⟨fun h' ↦ h'.resolve_left hB, .inr⟩,
      fun hB h ↦ Set.empty_ne_univ (hB ▸ h.1 (.inl hB)).symm⟩

/-- On a restrictor of at least two individuals, *all or none* has upward and downward degree of
monotonicity `0`. -/
theorem mon_allOrNone [Finite α] [Nontrivial α] {μ : Measure (Set α)} [IsProbabilityMeasure μ]
    (hμ : ∀ B, μ {B} ≠ 0) :
    mon (allOrNone (α := α)) μ = 0 ∧ monDown (allOrNone (α := α)) μ = 0 := by
  have h₁ : ∃ B : Set α, allOrNone B := ⟨∅, allOrNone_iff.2 (.inr rfl)⟩
  have h₀ : ∃ B : Set α, ¬ allOrNone B := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    refine ⟨{a}, fun h ↦ (allOrNone_iff.1 h).elim (fun h ↦ hab ?_) (Set.singleton_ne_empty a)⟩
    exact (Set.mem_singleton_iff.1 (h.ge (Set.mem_univ b))).symm
  exact ⟨(mon_eq_zero_iff hμ h₁ h₀).2 (allOrNone_iff.2 (.inr rfl)),
    (monDown_eq_zero_iff hμ h₁ h₀).2 (allOrNone_iff.2 (.inl rfl))⟩

end monotonicity

/-! ### The complexity of a lexicon with one word for each meaning -/

section complexity

open ZaslavskyKempRegierTishby2018

variable {M W : Type*} [MeasurableSpace M] [MeasurableSpace W] [Fintype M] [Fintype W]
  [MeasurableSingletonClass M] [MeasurableSingletonClass W] (source : Measure M)
  [IsProbabilityMeasure source] {f g : M → W}

/-- Two lexicons that each name every meaning by one word, and use each word equally often, are
equally complex, whatever the shapes of their categories. -/
theorem complexity_deterministic_congr (hf : Measurable f) (hg : Measurable g)
    (h : source.map f = source.map g) :
    complexity source (Kernel.deterministic f hf) =
      complexity source (Kernel.deterministic g hg) := by
  rw [complexity_deterministic, complexity_deterministic, entropy_def, entropy_def, h]

end complexity

end SteinertThrelkeldSzymanik2026
