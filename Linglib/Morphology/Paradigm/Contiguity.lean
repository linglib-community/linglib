module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Paradigm contiguity: the *ABA generalization

The *ABA generalization says graded paradigms are contiguous (`IsContiguous`), no form recurring
across a distinct intervening form, for degree (positive < comparative < superlative, after
Bobaljik), case (after Caha), and path roles (after Pantcheva). Of the five syncretism patterns of
three cells, named as Bobaljik names the degree patterns, contiguity excludes exactly ABA.

## Main definitions

* `Paradigm.aaa`, `Paradigm.abb`, `Paradigm.abc`, `Paradigm.aba`, `Paradigm.aab`: the
  three-cell patterns.

## Main results

* `isContiguous_iff_ker_ne_ker_aba`: over three cells contiguity excludes exactly ABA.
* `ker_eq_ker_aba_iff`, `ker_eq_ker_aab_iff`, `ker_eq_ker_abc_iff`, `ker_eq_ker_iff_fin_three`:
  the three-cell patterns by equalities of their cells.

## References

* [bobaljik-2012]
* [caha-2009]
* [pantcheva-2011]
-/

@[expose] public section

namespace Morphology

variable {F : Type*}

/-! ### The three-cell patterns

The five syncretism patterns of a three-cell chain, as form-class indices,
named as [bobaljik-2012] names the degree patterns over positive <
comparative < superlative. A concrete paradigm has a pattern when its
syncretism, the kernel `Setoid.ker`, is the pattern's. ABA is the pattern contiguity excludes; AAB
is contiguous, and its exclusion for degree is a vocabulary-level matter
(`Morphology/Exponence/Containment/Contiguity.lean`). -/

namespace Paradigm

/-- The AAA pattern has one form throughout (*tall – taller – tallest*). -/
def aaa : Paradigm 3 ℕ := ![0, 0, 0]

/-- In the ABB pattern the two upper cells share a form the lowest lacks
(*good – better – best*). -/
def abb : Paradigm 3 ℕ := ![0, 1, 1]

/-- The ABC pattern has three forms (*bonus – melior – optimus*). -/
def abc : Paradigm 3 ℕ := ![0, 1, 2]

/-- In the ABA pattern the outer cells share a form the middle one lacks. -/
def aba : Paradigm 3 ℕ := ![0, 1, 0]

/-- In the AAB pattern the two lower cells share a form the highest lacks. -/
def aab : Paradigm 3 ℕ := ![0, 0, 1]

end Paradigm

/-- Over three cells contiguity is the one condition on the outer pair. -/
theorem isContiguous_fin_three_iff (p : Paradigm 3 F) :
    IsContiguous p ↔ (p 0 = p 2 → p 0 = p 1) := by
  refine ⟨fun h ↦ h (i := 0) (j := 1) (k := 2) (by decide) (by decide),
    fun h i j k hij hjk heq ↦ ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | rfl
    | exact heq
    | exact h heq
    | exact absurd hij (by decide)
    | exact absurd hjk (by decide)

/-- A three-cell paradigm has the ABA pattern iff its outer cells agree and
its middle cell differs. -/
theorem ker_eq_ker_aba_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.aba ↔ p 0 = p 2 ∧ p 0 ≠ p 1 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨(h 0 2).mpr rfl, fun h01 ↦ absurd ((h 0 1).mp h01) (by decide)⟩, ?_⟩
  rintro ⟨h02, h01⟩ a b
  have h12 : p 1 ≠ p 2 := fun h ↦ h01 (h02.trans h.symm)
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_true h02 rfl
    | exact iff_of_true h02.symm rfl
    | exact iff_of_false h01 (by decide)
    | exact iff_of_false h01.symm (by decide)
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)

/-- A three-cell paradigm has the AAB pattern iff its lower cells agree and its highest cell
differs. -/
theorem ker_eq_ker_aab_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.aab ↔ p 0 = p 1 ∧ p 1 ≠ p 2 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨(h 0 1).mpr rfl, fun h12 ↦ absurd ((h 1 2).mp h12) (by decide)⟩, ?_⟩
  rintro ⟨h01, h12⟩ a b
  have h02 : p 0 ≠ p 2 := fun h ↦ h12 (h01.symm.trans h)
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_true h01 rfl
    | exact iff_of_true h01.symm rfl
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)
    | exact iff_of_false h02 (by decide)
    | exact iff_of_false h02.symm (by decide)

/-- A three-cell paradigm has the ABC pattern iff its cells differ pairwise. -/
theorem ker_eq_ker_abc_iff (p : Paradigm 3 F) :
    Setoid.ker p = Setoid.ker Paradigm.abc ↔ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧ p 0 ≠ p 2 := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨fun e ↦ absurd ((h 0 1).mp e) (by decide),
    fun e ↦ absurd ((h 1 2).mp e) (by decide), fun e ↦ absurd ((h 0 2).mp e) (by decide)⟩, ?_⟩
  rintro ⟨h01, h12, h02⟩ a b
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact iff_of_false h01 (by decide)
    | exact iff_of_false h01.symm (by decide)
    | exact iff_of_false h12 (by decide)
    | exact iff_of_false h12.symm (by decide)
    | exact iff_of_false h02 (by decide)
    | exact iff_of_false h02.symm (by decide)

/-- Two three-cell paradigms have the same pattern iff the same pairs of cells agree. -/
theorem ker_eq_ker_iff_fin_three {G : Type*} (p : Paradigm 3 F) (q : Paradigm 3 G) :
    Setoid.ker p = Setoid.ker q ↔
      (p 0 = p 1 ↔ q 0 = q 1) ∧ (p 1 = p 2 ↔ q 1 = q 2) ∧ (p 0 = p 2 ↔ q 0 = q 2) := by
  simp only [Setoid.ext_iff, Setoid.ker_def]
  refine ⟨fun h ↦ ⟨h 0 1, h 1 2, h 0 2⟩, fun ⟨h01, h12, h02⟩ a b ↦ ?_⟩
  fin_cases a <;> fin_cases b <;>
    first
    | exact iff_of_true rfl rfl
    | exact h01
    | exact h12
    | exact h02
    | exact (eq_comm.trans h01).trans eq_comm
    | exact (eq_comm.trans h12).trans eq_comm
    | exact (eq_comm.trans h02).trans eq_comm

/-- ABA is the only three-cell pattern contiguity excludes. -/
theorem isContiguous_iff_ker_ne_ker_aba (p : Paradigm 3 F) :
    IsContiguous p ↔ Setoid.ker p ≠ Setoid.ker Paradigm.aba := by
  rw [isContiguous_fin_three_iff, ne_eq, ker_eq_ker_aba_iff, not_and, not_not]

end Morphology
