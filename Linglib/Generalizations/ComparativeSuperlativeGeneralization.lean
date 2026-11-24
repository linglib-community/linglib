/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Inflection.Paradigm.Contiguity

/-!
# The Comparative-Superlative Generalization

The positive, comparative and superlative of an adjective may be built on one root, as in
*tall – taller – tallest*, or on several, as in *good – better – best* and Latin
*bonus – melior – optimus*. A grade is suppletive when its root is not the root of the positive.
The Comparative-Superlative Generalization says that the comparative of an adjective is suppletive
exactly when its superlative is. It has two parts: if the comparative is suppletive then so is the
superlative, and if the superlative is suppletive then so is the comparative.

The roots of the three grades are a paradigm of three cells, the positive, the comparative and
the superlative in that order, and the generalization is the predicate `CSG.Holds` on it. Of the
five patterns of three cells it allows AAA, ABB and ABC. Its first part excludes ABA and is the
contiguity of the grades. Its second part excludes AAB, which is contiguous.

## Main definitions

* `CSG.Part1`: if the comparative is suppletive, so is the superlative.
* `CSG.Part2`: if the superlative is suppletive, so is the comparative.
* `CSG.Holds`: both parts.

## Main results

* `CSG.holds_iff_ne_iff_ne`: the generalization holds exactly when the comparative and the
  superlative are suppletive together.
* `CSG.part1_iff_isContiguous`: the first part holds exactly when the grades are contiguous.
* `CSG.part1_iff_ker_ne_ker_aba`, `CSG.part2_iff_ker_ne_ker_aab`: the pattern each part excludes.
* `CSG.holds_iff_ker`: the generalization holds of the AAA, ABB and ABC patterns and of no other.

## Implementation notes

The generalization is stated of the roots of the grades and mentions no account of how a grade is
built or how a root is chosen. Which forms count as grades, such as morphological and not
periphrastic ones, and relative and not absolute superlatives, is settled by whoever describes an
adjective. An account of suppletion gives the roots of the grades, and whether they obey the
generalization is a theorem about the account, stated with it.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace CSG

open Morphology

variable {F : Type*} {p : Paradigm 3 F}

/-- The first part of the generalization: if the comparative is suppletive, so is the
superlative. -/
def Part1 (p : Paradigm 3 F) : Prop := p 1 ≠ p 0 → p 2 ≠ p 0

/-- The second part of the generalization: if the superlative is suppletive, so is the
comparative. -/
def Part2 (p : Paradigm 3 F) : Prop := p 2 ≠ p 0 → p 1 ≠ p 0

/-- The Comparative-Superlative Generalization holds of the roots of an adjective's grades when
both of its parts do. -/
@[mk_iff]
structure Holds (p : Paradigm 3 F) : Prop where
  /-- If the comparative is suppletive, so is the superlative. -/
  part1 : Part1 p
  /-- If the superlative is suppletive, so is the comparative. -/
  part2 : Part2 p

instance [DecidableEq F] : DecidablePred (Part1 : Paradigm 3 F → Prop) :=
  fun _ ↦ inferInstanceAs (Decidable (_ → _))

instance [DecidableEq F] : DecidablePred (Part2 : Paradigm 3 F → Prop) :=
  fun _ ↦ inferInstanceAs (Decidable (_ → _))

instance [DecidableEq F] : DecidablePred (Holds : Paradigm 3 F → Prop) :=
  fun _ ↦ decidable_of_iff' _ (holds_iff _)

/-- The generalization holds exactly when the comparative and the superlative are suppletive
together. -/
theorem holds_iff_ne_iff_ne : Holds p ↔ (p 1 ≠ p 0 ↔ p 2 ≠ p 0) :=
  ⟨fun h ↦ ⟨h.part1, h.part2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-! ### The parts and the three-cell patterns -/

/-- The first part holds exactly when the grades are contiguous. -/
theorem part1_iff_isContiguous : Part1 p ↔ IsContiguous p := by
  rw [isContiguous_fin_three_iff, Part1, not_imp_not]
  exact ⟨fun h e ↦ (h e.symm).symm, fun h e ↦ (h e.symm).symm⟩

/-- The first part excludes exactly the ABA pattern. -/
theorem part1_iff_ker_ne_ker_aba : Part1 p ↔ Setoid.ker p ≠ Setoid.ker Paradigm.aba :=
  part1_iff_isContiguous.trans (isContiguous_iff_ker_ne_ker_aba p)

/-- The second part excludes exactly the AAB pattern. -/
theorem part2_iff_ker_ne_ker_aab : Part2 p ↔ Setoid.ker p ≠ Setoid.ker Paradigm.aab := by
  rw [ne_eq, ker_eq_ker_aab_iff, Part2, not_imp_not, not_and, not_not]
  exact ⟨fun h h01 ↦ h01.symm.trans (h h01.symm).symm, fun h h10 ↦ (h h10.symm).symm.trans h10⟩

/-- The generalization holds of the AAA, ABB and ABC patterns and of no other. -/
theorem holds_iff_ker : Holds p ↔ Setoid.ker p = Setoid.ker Paradigm.aaa ∨
    Setoid.ker p = Setoid.ker Paradigm.abb ∨ Setoid.ker p = Setoid.ker Paradigm.abc := by
  simp only [holds_iff_ne_iff_ne, ker_eq_ker_iff_fin_three, Paradigm.aaa, Paradigm.abb,
    Paradigm.abc, Fin.isValue, ne_eq, Matrix.cons_val_zero, Matrix.cons_val_one, iff_true,
    Matrix.cons_val, zero_ne_one, iff_false, OfNat.one_ne_ofNat, OfNat.zero_ne_ofNat]
  grind

theorem holds_aaa : Holds Paradigm.aaa := by decide

theorem holds_abb : Holds Paradigm.abb := by decide

theorem holds_abc : Holds Paradigm.abc := by decide

theorem not_part1_aba : ¬ Part1 Paradigm.aba := by decide

theorem part2_aba : Part2 Paradigm.aba := by decide

theorem part1_aab : Part1 Paradigm.aab := by decide

theorem not_part2_aab : ¬ Part2 Paradigm.aab := by decide

end CSG
