/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Languages and typologies

An OT system pairs each input's candidates with a constraint set on input–output mappings
(`ConstraintSystem`). Under a ranking, the winners of every input's tableau form the ranking's
language. Following Merchant and Prince, the rankings with the same language form a ranking
grammar, and the grammars partition the rankings into the system's typology, the kernel of the
language map.

A system with finitely many inputs has the same typology as its joint system. The joint system is
a single tableau whose candidates choose a candidate for every input and whose violations are
summed over the inputs, the Minkowski sum of the system's tableaux. Prince shows that its language
is the product of the languages, so summation loses no ranking information. Magri traces this to
the additivity of the lexicographic order, under which minimizing a sum over a product of
candidate sets minimizes each summand (`Finset.mem_argmin_piFinset_sum`).

## Main definitions

* `ConstraintSystem.tableau`: the tableau of an input under a ranking.
* `ConstraintSystem.language`: the winners of each input under a ranking.
* `ConstraintSystem.typology`: the partition of the rankings by their languages.

## Main results

* `ConstraintSystem.language_eq_singleton_iff`: a ranking selects `o` alone at an input iff `o`
  is a candidate lexicographically below every other.
* `ConstraintSystem.mem_language_iff_of_mem`: tied winners have the same violations, so the
  language at an input consists of the candidates with any one winner's violations.
* `ConstraintSystem.language_joint`: the language of the joint system is the product of the
  languages.
* `ConstraintSystem.typology_joint`: one tableau suffices, the joint system having the system's
  typology when every input has a candidate.

## References

* [N. Merchant and A. Prince, *The Mother of All Tableaux* (2022)][merchant-prince-2022]
* [A. Prince, *One Tableau Suffices* (2015)][prince-2015]
* [G. Magri, *When is it the case that one tableau suffices?* (2015)][magri-2015]
-/

@[expose] public section

namespace OptimalityTheory

namespace ConstraintSystem

variable {I O ι : Type*} {n : ℕ} (S : ConstraintSystem I O ι) (r : Ranking ι n) (i : I)

/-- The tableau of an input under a ranking evaluates its candidates by the system's constraints
in rank order. -/
def tableau : Tableau O n := Tableau.ofRanking (S.conAt i) r (S.gen i)

/-- The **language** of a ranking assigns each input the winners of its tableau
([merchant-prince-2022]). -/
def language : Finset O := (S.tableau r i).optimal

/-- The **typology** of a system identifies the rankings with the same language, so that its
classes, the ranking grammars, partition the rankings ([merchant-prince-2022]). -/
def typology : Setoid (Ranking ι n) := Setoid.ker S.language

variable {S r i} {o : O}

theorem typology_iff {r' : Ranking ι n} : S.typology r r' ↔ S.language r = S.language r' :=
  Iff.rfl

/-- A ranking selects `o` alone at an input iff `o` is a candidate whose violations, read in
rank order, are lexicographically below every other candidate's. -/
theorem language_eq_singleton_iff : S.language r i = {o} ↔ o ∈ S.gen i ∧ ∀ o' ∈ S.gen i, o' ≠ o →
    toLex (fun k ↦ S.con (r k) (i, o)) < toLex (fun k ↦ S.con (r k) (i, o')) :=
  Tableau.optimal_eq_singleton_iff

/-- A ranking selects a winner at every input that has a candidate. -/
theorem language_nonempty (h : (S.gen i).Nonempty) : (S.language r i).Nonempty :=
  Tableau.optimal_nonempty h

theorem language_nonempty_iff : (S.language r i).Nonempty ↔ (S.gen i).Nonempty :=
  ⟨fun ⟨o, ho⟩ ↦ ⟨o, Tableau.optimal_subset ho⟩, language_nonempty⟩

/-- Tied winners have the same violations on every constraint, since the ranking reads distinct
violation vectors as distinct profiles. -/
theorem con_eq_of_mem_language {o' : O} (ho : o ∈ S.language r i) (ho' : o' ∈ S.language r i)
    (C : ι) : S.con C (i, o) = S.con C (i, o') := by
  have h := le_antisymm (Tableau.le_of_mem_optimal ho (Tableau.optimal_subset ho'))
    (Tableau.le_of_mem_optimal ho' (Tableau.optimal_subset ho))
  simpa [tableau, Tableau.profile] using congrFun (congrArg ofLex h) (r.symm C)

/-- The language of a ranking at an input consists of the candidates with the violations of any
one of its winners. -/
theorem mem_language_iff_of_mem {o' : O} (ho : o ∈ S.language r i) :
    o' ∈ S.language r i ↔ o' ∈ S.gen i ∧ ∀ C, S.con C (i, o') = S.con C (i, o) := by
  refine ⟨fun h ↦ ⟨Tableau.optimal_subset h, con_eq_of_mem_language h ho⟩, fun ⟨hg, he⟩ ↦ ?_⟩
  have hp : (S.tableau r i).profile o' = (S.tableau r i).profile o := by
    simp only [tableau, Tableau.profile, Tableau.ofRanking_constraints, Function.comp_apply,
      conAt_apply, he]
  exact Tableau.mem_optimal_iff.2 ⟨hg, fun d hd ↦ hp ▸ Tableau.le_of_mem_optimal ho hd⟩

section Joint

variable [Fintype I] [DecidableEq I] (S r)

/-- The language of the joint system is the product of the system's languages, so a tuple wins
iff each of its candidates wins at its input ([prince-2015]). -/
theorem language_joint : S.joint.language r () = Fintype.piFinset (S.language r) := by
  have hprofile : (S.joint.tableau r ()).profile = fun g ↦ ∑ i, (S.tableau r i).profile (g i) :=
    funext fun g ↦ funext fun p ↦
      (Finset.sum_apply p _ fun i ↦ ofLex ((S.tableau r i).profile (g i))).symm
  ext f
  rw [Fintype.mem_piFinset, language, Tableau.optimal, hprofile]
  exact Finset.mem_argmin_piFinset_sum S.gen fun i ↦ (S.tableau r i).profile

variable {S}

/-- **One tableau suffices** ([prince-2015]). When every input has a candidate, the joint system
has the system's typology. -/
theorem typology_joint [DecidableEq O] (h : ∀ i, (S.gen i).Nonempty) :
    (S.joint.typology : Setoid (Ranking ι n)) = S.typology := by
  refine Setoid.ext fun r r' ↦ ?_
  rw [typology_iff, typology_iff]
  refine ⟨fun hj ↦ funext fun i ↦ ?_, fun hl ↦ funext fun _ ↦ by rw [language_joint, hl,
    ← language_joint]⟩
  have hne (r : Ranking ι n) : ∀ j, i ≠ j → (S.language r j).Nonempty :=
    fun j _ ↦ language_nonempty (h j)
  have := congrArg (fun F ↦ (F ()).image (· i)) hj
  simpa only [language_joint, Fintype.eval_image_piFinset _ _ (hne _)] using this

end Joint

end ConstraintSystem

end OptimalityTheory
