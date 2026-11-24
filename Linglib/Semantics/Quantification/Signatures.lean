/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Natural.ProjectivitySignature

/-!
# Projectivity signatures of the determiners

This file places the argument positions of *every*, *some* and *no* in the function classes of
natural logic. A determiner is a map of its scope for each restrictor and a map of its restrictor
for each scope, and each of these maps has a projectivity signature: *some* is additive in both
arguments, *no* is anti-additive in both, and *every* is anti-additive in its restrictor and
multiplicative in its scope. The unit condition of each class holds when the other argument is not
trivial, a nonempty restrictor or a scope that is neither empty nor everything.

## Main results

* `Quantifier.Det.holdsFor_antiAdd_every_left`, `Quantifier.Det.holdsFor_mult_every`: *every* is
  anti-additive in its restrictor and multiplicative in its scope.
* `Quantifier.Det.holdsFor_additive_some_left`, `Quantifier.Det.holdsFor_additive_some`: *some* is
  additive in both arguments.
* `Quantifier.Det.holdsFor_antiAdd_no_left`, `Quantifier.Det.holdsFor_antiAdd_no`: *no* is
  anti-additive in both arguments.
* `Quantifier.Det.holdsFor_additive_not_every_left`,
  `Quantifier.Det.holdsFor_antiMult_not_every`: *not every* is additive in its restrictor and
  anti-multiplicative in its scope, by composition with negation.
* `Quantifier.Det.not_holdsFor_additive_every`: the scope of *every* is not additive.

## References

* [icard-2012]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier.Det

open NaturalLogic ProjectivitySignature

variable {α : Type*} {A B : Set α}

/-! ### Every -/

/-- The restrictor of a universal whose scope is not everything is anti-additive. -/
theorem holdsFor_antiAdd_every_left (hB : B ≠ Set.univ) : antiAdd.HoldsFor (every · B) :=
  holdsFor_antiAdd_iff.2
    ⟨leftAntiAdditive_every B, eq_false fun h ↦ hB (Set.univ_subset_iff.1 h)⟩

/-- The scope of a universal over a nonempty restrictor is multiplicative. -/
theorem holdsFor_mult_every (hA : A.Nonempty) : mult.HoldsFor (every A) :=
  holdsFor_mult_iff.2 ⟨fun _ _ ↦ propext Set.subset_inter_iff,
    eq_false fun h ↦ hA.ne_empty (Set.subset_empty_iff.1 h)⟩

/-- The scope of a universal over a restrictor with two members is not additive. -/
theorem not_holdsFor_additive_every {a b : α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ¬ additive.HoldsFor (every A) := fun h ↦ by
  have := eq_iff_iff.1 ((holdsFor_additive_iff.1 h).1 {a}ᶜ {b}ᶜ)
  refine (this.1 fun x _ ↦ ?_).elim (fun h ↦ h ha rfl) fun h ↦ h hb rfl
  by_cases hx : x = a
  exacts [.inr (hx ▸ hab), .inl hx]

/-- The restrictor of *not every* with a scope that is not everything is additive: negation after
an anti-additive map. -/
theorem holdsFor_additive_not_every_left (hB : B ≠ Set.univ) :
    additive.HoldsFor fun A ↦ ¬ every A B :=
  holdsFor_compl_comp_iff.2 (holdsFor_antiAdd_every_left hB)

/-- The scope of *not every* over a nonempty restrictor is anti-multiplicative: negation after a
multiplicative map. -/
theorem holdsFor_antiMult_not_every (hA : A.Nonempty) :
    antiMult.HoldsFor fun B ↦ ¬ every A B :=
  holdsFor_compl_comp_iff.2 (holdsFor_mult_every hA)

/-! ### Some -/

/-- The restrictor of an existential with a nonempty scope is additive. -/
theorem holdsFor_additive_some_left (hB : B.Nonempty) : additive.HoldsFor (Det.some · B) :=
  holdsFor_additive_iff.2 ⟨fun A A' ↦ congrFun (some_union A A') B, eq_true (by simpa using hB)⟩

/-- The scope of an existential over a nonempty restrictor is additive. -/
theorem holdsFor_additive_some (hA : A.Nonempty) : additive.HoldsFor (Det.some A) :=
  holdsFor_additive_iff.2 ⟨fun B B' ↦ by
      simp [Det.some, Set.inter_union_distrib_left, Set.union_nonempty],
    eq_true (by simpa [Det.some] using hA)⟩

/-! ### No -/

/-- The restrictor of a negative universal with a nonempty scope is anti-additive. -/
theorem holdsFor_antiAdd_no_left (hB : B.Nonempty) : antiAdd.HoldsFor (no · B) :=
  holdsFor_antiAdd_iff.2 ⟨leftAntiAdditive_no B, eq_false (by simpa using hB.ne_empty)⟩

/-- The scope of a negative universal over a nonempty restrictor is anti-additive. -/
theorem holdsFor_antiAdd_no (hA : A.Nonempty) : antiAdd.HoldsFor (no A) :=
  holdsFor_antiAdd_iff.2 ⟨rightAntiAdditive_no A,
    eq_false fun h ↦ hA.ne_empty (Set.subset_empty_iff.1 (by simpa [no] using h))⟩

end Quantifier.Det
