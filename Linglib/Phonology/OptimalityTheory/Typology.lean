/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Evaluation
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Languages and typologies

An OT system pairs each input's candidates with a constraint set on input–output mappings
(`ConstraintSystem`). Under a ranking, the winners of every input's tableau form the ranking's
[language](##OptimalityTheory.ConstraintSystem.language). A ranking
[picks](##OptimalityTheory.ConstraintSystem.PicksAt) an output when it is the sole winner, which
holds iff [against each rival some constraint preferring it dominates every constraint
preferring the rival](##OptimalityTheory.ConstraintSystem.picksAt_iff_exists_dominates).
Following Merchant and Prince, the rankings with the same language form a ranking grammar, and
the grammars partition the rankings into the system's
[typology](##OptimalityTheory.ConstraintSystem.typology), the kernel of the language map.

A system with finitely many inputs has
[the same typology as its joint system](##OptimalityTheory.ConstraintSystem.typology_joint), a
single tableau whose candidates choose a candidate for every input and whose violations are
summed over the inputs, the Minkowski sum of the system's tableaux. Prince shows that
[its language is the product of the languages](##OptimalityTheory.ConstraintSystem.language_joint),
so summation loses no ranking information. Magri traces this to the additivity of the
lexicographic order, under which minimizing a sum over a product of candidate sets minimizes each
summand (`Finset.mem_argmin_piFinset_sum`).

## References

* [N. Merchant and A. Prince, *The Mother of All Tableaux* (2022)][merchant-prince-2022]
* [A. Prince, *One Tableau Suffices* (2015)][prince-2015]
* [G. Magri, *When is it the case that one tableau suffices?* (2015)][magri-2015]
-/

@[expose] public section

namespace OptimalityTheory

namespace ConstraintSystem

variable {I O ι : Type*} {n : ℕ} (S : ConstraintSystem I O ι) (r : Ranking.Enumeration ι n) (i : I)

/-- The **language** of a ranking assigns each input its optimal candidates
([merchant-prince-2022]). -/
def language : Finset O := r.optimal (S.marks i) (S.gen i)

/-- The **typology** of a system identifies the rankings with the same language, so that its
classes, the ranking grammars, partition the rankings ([merchant-prince-2022]). -/
def typology : Setoid (Ranking.Enumeration ι n) := Setoid.ker S.language

variable {S r i} {o : O}

theorem typology_iff {r' : Ranking.Enumeration ι n} : S.typology r r' ↔ S.language r =
    S.language r' :=
  Iff.rfl

theorem language_subset : S.language r i ⊆ S.gen i := Ranking.Enumeration.optimal_subset

/-- A ranking selects `o` alone at an input iff `o` is a candidate whose violations, read in
rank order, are lexicographically below every other candidate's. -/
theorem language_eq_singleton_iff : S.language r i = {o} ↔ o ∈ S.gen i ∧ ∀ o' ∈ S.gen i, o' ≠ o →
    r.profile (S.marks i) o < r.profile (S.marks i) o' :=
  Finset.argmin_eq_singleton_iff

theorem language_nonempty (h : (S.gen i).Nonempty) : (S.language r i).Nonempty :=
  Ranking.Enumeration.optimal_nonempty h

theorem language_nonempty_iff : (S.language r i).Nonempty ↔ (S.gen i).Nonempty :=
  ⟨fun ⟨o, ho⟩ ↦ ⟨o, language_subset ho⟩, language_nonempty⟩

/-- The language of a ranking at an input consists of the candidates with the violations of any
one of its winners. -/
theorem mem_language_iff_of_mem {o' : O} (ho : o ∈ S.language r i) :
    o' ∈ S.language r i ↔ o' ∈ S.gen i ∧ S.marks i o' = S.marks i o :=
  Ranking.Enumeration.mem_optimal_iff_of_mem ho

theorem marks_eq_of_mem_language {o' : O} (ho : o ∈ S.language r i) (ho' : o' ∈ S.language r i) :
    S.marks i o = S.marks i o' :=
  ((mem_language_iff_of_mem ho').1 ho).2

/-! ### Sole winners -/

variable (S r i o) in
/-- The ranking `r` *picks* the output `o` for the input `i` when `o` alone is the language of `r`
at `i`, the sole winner of the input's tableau. -/
def PicksAt : Prop := S.language r i = {o}

/-- A ranking picks `o` iff `o` is a candidate whose violations, read in rank order, are
lexicographically below every other candidate's. -/
theorem picksAt_iff : S.PicksAt r i o ↔ o ∈ S.gen i ∧ ∀ o' ∈ S.gen i, o' ≠ o →
    r.profile (S.marks i) o < r.profile (S.marks i) o' :=
  language_eq_singleton_iff

/-- A ranking picks `o` iff `o` is a candidate and, against each rival, some constraint
preferring `o` dominates every constraint preferring the rival. -/
theorem picksAt_iff_exists_dominates : S.PicksAt r i o ↔ o ∈ S.gen i ∧ ∀ o' ∈ S.gen i, o' ≠ o →
    ∃ c, S.marks i o c < S.marks i o' c ∧
      ∀ c', S.marks i o' c' < S.marks i o c' → r.Dominates c c' :=
  Ranking.Enumeration.optimal_eq_singleton_iff

/-- Picking is decided by comparing the candidate with each rival, without computing the set of
winners. -/
instance [DecidableEq O] : Decidable (S.PicksAt r i o) := decidable_of_iff _ picksAt_iff.symm

theorem PicksAt.unique {o' : O} (h : S.PicksAt r i o) (h' : S.PicksAt r i o') : o = o' :=
  Finset.singleton_injective (h.symm.trans h')

/-- A ranking picks some candidate at an input whose candidates have distinct violations. -/
theorem exists_picksAt (h : (S.gen i).Nonempty) (hinj : Set.InjOn (S.marks i) (S.gen i))
    (r : Ranking.Enumeration ι n) : ∃ o ∈ S.gen i, S.PicksAt r i o := by
  obtain ⟨o, ho⟩ := language_nonempty (r := r) h
  refine ⟨o, language_subset ho, Finset.eq_singleton_iff_unique_mem.2 ⟨ho, fun o' ho' ↦ ?_⟩⟩
  exact hinj (language_subset ho') (language_subset ho) (marks_eq_of_mem_language ho' ho)

section Joint

variable [Fintype I] [DecidableEq I] (S r)

/-- The language of the joint system is the product of the system's languages, so a tuple wins
iff each of its candidates wins at its input ([prince-2015]). -/
theorem language_joint : S.joint.language r () = Fintype.piFinset (S.language r) := by
  have hprofile : r.profile (S.joint.marks ()) = fun g ↦ ∑ i, r.profile (S.marks i) (g i) :=
    funext fun g ↦ funext fun p ↦
      (Finset.sum_apply p _ fun i ↦ ofLex (r.profile (S.marks i) (g i))).symm
  ext f
  rw [Fintype.mem_piFinset, language, Ranking.Enumeration.optimal, hprofile]
  exact Finset.mem_argmin_piFinset_sum S.gen fun i ↦ r.profile (S.marks i)

variable {S}

/-- **One tableau suffices** ([prince-2015]). When every input has a candidate, the joint system
has the system's typology. -/
theorem typology_joint [DecidableEq O] (h : ∀ i, (S.gen i).Nonempty) :
    (S.joint.typology : Setoid (Ranking.Enumeration ι n)) = S.typology := by
  refine Setoid.ext fun r r' ↦ ?_
  rw [typology_iff, typology_iff]
  refine ⟨fun hj ↦ funext fun i ↦ ?_, fun hl ↦ funext fun _ ↦ by rw [language_joint, hl,
    ← language_joint]⟩
  have hne (r : Ranking.Enumeration ι n) : ∀ j, i ≠ j → (S.language r j).Nonempty :=
    fun j _ ↦ language_nonempty (h j)
  have := congrArg (fun F ↦ (F ()).image (· i)) hj
  simpa only [language_joint, Fintype.eval_image_piFinset _ _ (hne _)] using this

end Joint

end ConstraintSystem

end OptimalityTheory
