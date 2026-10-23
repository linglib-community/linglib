module

public import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
public import Studies.McKayVanInwagen1977
public import Mathlib.Data.List.Sublists

/-!
# Santorio (2018): Alternatives and Truthmakers in Conditional Semantics

This file formalizes the paper's truthmaker semantics for conditionals. The paper starts from
a trilemma: counterfactuals invalidate Antecedent Strengthening, validate Simplification of
Disjunctive Antecedents, and validate Substitution of Logical Equivalents in the antecedent,
yet with Boolean disjunction the last two entail the first. It keeps the first and gives up
the other two by letting an *if*-clause denote the set of truthmakers of its antecedent: the
conjunctive closures of the minimal stable subsets of the antecedent's alternatives that
entail it, where a subset is stable when it is consistent with the negation of every
alternative outside it (`Stable`, `MinimalStable`, `truthmakers`). The conditional is a
description of that set: with the optional distributivity operator it holds of each
truthmaker, which is Simplification (`distributiveConditional`), and without it the modal
*would* extracts the disjunctive closure, which is not (`collectiveConditional`); the operator
carries the all-or-nothing homogeneity presupposition (`homogeneityPresup`). The readings are
those of `Semantics/Conditionals/Counterfactual/Alternatives.lean` over the truthmakers.

On *Otto or Anna went to the party* (44) the truthmakers are *Otto went* and *Anna went*
(`party_truthmakers`). On (35) *every student read War and Peace or Anna Karenina* the
global algorithm finds the mixed truthmaker *some read Anna Karenina and some read War and
Peace* that Alonso-Ovalle's disjunct alternatives cannot (`karenina_truthmakers`,
`karenina_mixed_not_alonsoOvalle`), predicting the infelicity of (39). On
McKay and van Inwagen's Spain case (8) the collective parsing is true and the distributive
one is not, so Antecedent Strengthening fails and Simplification is not validated
(`spain_collective`, `spain_not_distributive`, `spain_homogeneity`); and on (57)–(58),
logically equivalent antecedents whose *if*-clauses denote different sets receive different
distributive verdicts (`substitution_fails`).

## Implementation notes

The formalization is checked against the author's revised draft, whose example numbering the
labels follow; the draft's definition of a truthmaker once says "maximal stable" where its
text and its examples require minimal stability. The empty set of alternatives, stable
whenever some world falsifies every alternative, is excluded from the minimal stable sets, as
the paper's examples presuppose. Alternatives are given as propositions over a finite world
type rather than generated from syntactic substitution sources.

## References

* [santorio-2018]
* [alonso-ovalle-2009]
* [mckay-vaninwagen-1977]
-/

@[expose] public section

namespace Santorio2018

open Conditional

variable {W : Type*} [DecidableEq W] [Fintype W]

/-! ### The stability algorithm (§5) -/

/-- `σ` is stable with respect to the alternatives `alts` when some world verifies every member
of `σ` and falsifies every other alternative. -/
def Stable (alts σ : List (Finset W)) : Prop :=
  ∃ w, (∀ A ∈ σ, w ∈ A) ∧ ∀ A ∈ alts, A ∉ σ → w ∉ A

instance (alts σ : List (Finset W)) : Decidable (Stable alts σ) :=
  inferInstanceAs
    (Decidable (∃ w, (∀ A ∈ σ, w ∈ A) ∧ ∀ A ∈ alts, A ∉ σ → w ∉ A))

/-- A nonempty stable sublist of `alts` none of whose nonempty proper sublists is stable.
(The empty set, stable whenever some world falsifies every alternative, is excluded.) -/
def MinimalStable (alts σ : List (Finset W)) : Prop :=
  σ ≠ [] ∧ σ.Sublist alts ∧ Stable alts σ ∧
    ∀ τ ∈ σ.sublists, τ ≠ [] → τ ≠ σ → ¬ Stable alts τ

instance (alts σ : List (Finset W)) : Decidable (MinimalStable alts σ) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ ∧ ∀ τ ∈ σ.sublists, _ → _ → ¬ Stable alts τ))

/-- `⋀σ`. -/
def conjunctiveClosure (σ : List (Finset W)) : Finset W := σ.foldr (· ∩ ·) Finset.univ

/-- The truthmakers of `S` relative to `alts` are the conjunctive closures of the minimal stable
subsets of `alts` that entail `S`, the denotation of the *if*-clause. -/
def truthmakers (alts : List (Finset W)) (S : Finset W) : List (Finset W) :=
  ((alts.sublists.filter fun σ ↦ decide (MinimalStable alts σ)).map conjunctiveClosure).filter
    fun p ↦ decide (p ⊆ S)

theorem subset_of_mem_truthmakers {alts : List (Finset W)} {S p : Finset W}
    (h : p ∈ truthmakers alts S) : p ⊆ S := by
  simpa using (List.mem_filter.1 h).2

theorem sup_truthmakers_subset (alts : List (Finset W)) (S : Finset W) :
    (truthmakers alts S).toFinset.sup id ⊆ S :=
  Finset.sup_le fun _ hp ↦ subset_of_mem_truthmakers (List.mem_toFinset.1 hp)

/-! ### Conditionals as descriptions (§6) -/

variable (ord : W → Preorder W) [∀ w, DecidableRel (ord w).le] (alts : List (Finset W))
  (S : Finset W) (C : Set W) [DecidablePred (· ∈ C)] (w : W)

/-- `[if φ] DIST_π [would ψ]` holds when the counterfactual holds of every truthmaker of `φ`. -/
def distributiveConditional : Prop := w ∈ distributiveImp ord (truthmakers alts S).toFinset C

/-- The homogeneity presupposition of `DIST_π` is that every truthmaker's counterfactual holds,
or none does. -/
def homogeneityPresup : SignType := homogeneousImp ord (truthmakers alts S).toFinset C w

/-- `[if φ] would ψ` without `DIST_π` holds when the modal extracts the disjunctive closure of
the truthmakers. -/
def collectiveConditional : Prop := w ∈ disjunctiveImp ord (truthmakers alts S).toFinset C

instance : Decidable (distributiveConditional ord alts S C w) :=
  inferInstanceAs (Decidable (w ∈ distributiveImp ord _ C))

instance : Decidable (collectiveConditional ord alts S C w) :=
  inferInstanceAs (Decidable (w ∈ disjunctiveImp ord _ C))

/-! ### Otto and Anna (44) -/

/-- Who went to the party. -/
inductive Party where
  | ottoOnly
  | annaOnly
  | both
  | neither
  deriving DecidableEq, Fintype

abbrev otto : Finset Party := {.ottoOnly, .both}
abbrev anna : Finset Party := {.annaOnly, .both}

/-- The alternatives to *Otto or Anna went to the party*, (45). -/
def partyAlts : List (Finset Party) := [otto ∪ anna, otto, anna, otto ∩ anna]

/-- The truthmakers of (44) are *Otto went* and *Anna went*, since the minimal stable subsets
are `{O ∨ A, O}` and `{O ∨ A, A}`. -/
theorem party_truthmakers : (truthmakers partyAlts (otto ∪ anna)).toFinset = {otto, anna} := by
  decide

/-! ### Every student read War and Peace or Anna Karenina (35) -/

/-- Which of the two books the students read. -/
inductive Reading where
  | none
  | everyAK
  | everyWP
  | mixed
  | everyBoth
  deriving DecidableEq, Fintype

abbrev everyA : Finset Reading := {.everyAK, .everyBoth}
abbrev everyW : Finset Reading := {.everyWP, .everyBoth}
abbrev everyAorW : Finset Reading := {.everyAK, .everyWP, .mixed, .everyBoth}
abbrev someA : Finset Reading := {.everyAK, .mixed, .everyBoth}
abbrev someW : Finset Reading := {.everyWP, .mixed, .everyBoth}
/-- `∃(A ∨ W)`, which coincides with `∀(A ∨ W)` on these five worlds. -/
abbrev someAorW : Finset Reading := everyAorW

/-- The alternatives to (35) are the universal and existential claims over `A ∧ W`, `A`, `W`,
`A ∨ W`. -/
def readingAlts : List (Finset Reading) :=
  [everyA ∩ everyW, everyA, everyW, everyAorW, someA ∩ someW, someA, someW, someAorW]

/-- (35) has three truthmakers, *every student read AK*, *every student read W&P*, and the
mixed *some read AK and some read W&P*. -/
theorem karenina_truthmakers :
    (truthmakers readingAlts everyAorW).toFinset = {everyA, everyW, someA ∩ someW} := by
  decide

/-- The mixed truthmaker realizes neither universal alternative, so [alonso-ovalle-2009]'s
alternatives miss the way (35) is true that makes (39) infelicitous. -/
theorem karenina_mixed_not_alonsoOvalle :
    Reading.mixed ∈ someA ∩ someW ∧ Reading.mixed ∉ everyA ∧
      Reading.mixed ∉ everyW := by
  decide

/-! ### Spain (8), on [mckay-vaninwagen-1977] -/

section Spain

open McKayVanInwagen1977 (SpainWorld spainSim foughtAxis foughtAllies)

abbrev axis : Finset SpainWorld := Finset.univ.filter (· ∈ foughtAxis)
abbrev allies : Finset SpainWorld := Finset.univ.filter (· ∈ foughtAllies)

/-- The alternatives to *Spain fought with the Axis or the Allies*. -/
def spainAlts : List (Finset SpainWorld) := [axis ∪ allies, axis, allies, axis ∩ allies]

/-- Collectively (8) is true while its strengthening to *the Allies* is false, so Antecedent
Strengthening fails. -/
theorem spain_collective :
    collectiveConditional spainSim spainAlts (axis ∪ allies) foughtAxis .actual ∧
      .actual ∉ closestImp spainSim ↑allies foughtAxis := by
  decide

/-- Distributively, (8) is false, since the Allies truthmaker's counterfactual fails, so
Simplification is not validated by the collective parsing. -/
theorem spain_not_distributive :
    ¬ distributiveConditional spainSim spainAlts (axis ∪ allies) foughtAxis .actual := by
  decide

/-- The homogeneity presupposition of the distributive parsing fails on (8). -/
theorem spain_homogeneity :
    homogeneityPresup spainSim spainAlts (axis ∪ allies) foughtAxis .actual = 0 := by
  decide

end Spain

/-! ### Substitution of Logical Equivalents (57)–(58) -/

/-- Closeness for the party puts the Anna-only world closest to the actual world, then the
world where both came, then Otto's. -/
abbrev partySim (_ : Party) : Preorder Party := Preorder.ofLE
  (fun w₁ w₂ ↦ w₁ = w₂ ∨ w₁ = .annaOnly ∧ w₂ ≠ .neither ∨ w₁ = .both ∧ w₂ = .ottoOnly)
  (by decide) (by decide)

instance (w : Party) : DecidableRel (partySim w).le := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- *The party was fun* holds only when Anna came alone. -/
abbrev partyFun : Finset Party := {.annaOnly}

/-- On the distributive parsing, (57) is true and (58) false although their antecedents are
logically equivalent. -/
theorem substitution_fails :
    anna = anna ∪ (otto ∩ anna) ∧
      .neither ∈ distributiveImp partySim {anna} ↑partyFun ∧
      .neither ∉ distributiveImp partySim {anna, otto ∩ anna} ↑partyFun := by
  decide

end Santorio2018
