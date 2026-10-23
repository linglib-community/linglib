module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.ModelTheory.Lindstrom
public import Linglib.Core.ModelTheory.Monadic
public import Linglib.Semantics.Quantification.Basic

/-!
# Realizing Lindström quantifiers as GQ denotations

A determiner, a Lindström quantifier of type `⟨1,1⟩`, is an isomorphism-invariant class of
structures for the monadic language with two predicate symbols, the restrictor `pred 0` and the
scope `pred 1`. `Det.toGQ` realizes it as a generalized-quantifier denotation `GQ α`: a pair of
predicates `(A, B)` becomes the structure `(α, A, B)`, and the quantifier holds of `(A, B)` when
that structure is in the class. Quantity invariance is then a theorem about every realized
determiner, and the determiners defined by the sentences for *every*, *some* and *no* realize the
denotations of `Quantification/Basic.lean`.

The language is `Language.monadic (Fin 2)`, so the monadic Ehrenfeucht–Fraïssé results apply to
determiners directly: `foDefinable_iff_exists_min_encard_eq` is van Benthem's characterization of
the first-order definable determiners as those invariant under agreement of the four Venn region
sizes up to a threshold.

## Main definitions

* `Det`, `Det.toGQ`: determiners and their realization as `GQ α` denotations.
* `everyDet`, `someDet`, `noDet`: the determiners of the square of opposition.

## Main results

* `Det.realize_quantityInvariant`: every realized determiner satisfies
  `Quantifier.GQ.QuantityInvariant`, the type-`⟨1,1⟩` form of Mostowski's permutation
  invariance.
* `everyDet_toGQ`, `someDet_toGQ`, `noDet_toGQ`: the realizations are `every`, `GQ.some`, `no`.
* `toGQ_compl`: realization carries the complement of a class to GQ outer negation.
* `someDet_holds_eq_compl`, `noDet_toGQ_eq_innerNeg`, `someDet_toGQ_eq_dual`: the `no` and
  `some` corners as the complement, inner negation and dual of `every`.

## References

* [barwise-cooper-1981]
* [demey-frijters-2023]
* [mostowski-1957]
* [van-benthem-1984]
-/

@[expose] public section

universe u v

namespace Quantifier.Lindstrom

open Quantifier.GQ

open FirstOrder Language BoundedFormula
open CategoryTheory (Bundled)

/-! ### The realization functor -/

/-- A *determiner* is a Lindström quantifier of type `⟨1,1⟩`, an iso-invariant class of
structures for the monadic language with a restrictor and a scope predicate. -/
abbrev Det := LindstromQuantifier.{0, 0, u} (Language.monadic (Fin 2))

namespace Det

/-- `Q.toGQ α` holds of `(A, B)` iff the structure `(α, A, B)` is in the class `Q`. -/
def toGQ (Q : Det.{u}) (α : Type u) : GQ α :=
  fun A B => (⟨α, monadicStructure α ![A, B]⟩ : Bundled.{u} (Language.monadic (Fin 2)).Structure)
    ∈ Q.holds

/-- Every realized Lindström quantifier satisfies `QuantityInvariant`, so `q A B` is invariant
under a bijective relabelling of the domain. This is the type-`⟨1,1⟩` form of Mostowski's
permutation invariance, derived from `iso_inv` rather than stipulated on the denotation. -/
theorem realize_quantityInvariant (Q : Det.{u}) {α : Type u} :
    Quantifier.GQ.QuantityInvariant (Q.toGQ α) := by
  intro A B A' B' f hBij hA hB
  refine Q.iso_inv ⟨monadicStructureEquiv (Equiv.ofBijective f hBij).symm
    (Fin.forall_fin_two.2 ⟨fun x => ?_, fun x => ?_⟩)⟩
  · simpa [Equiv.ofBijective_apply_symm_apply] using (hA ((Equiv.ofBijective f hBij).symm x)).symm
  · simpa [Equiv.ofBijective_apply_symm_apply] using (hB ((Equiv.ofBijective f hBij).symm x)).symm

end Det

/-! ### The Aristotelian determiners -/

/-- The determiner *every*, defined by `∀x (U x → V x)`. -/
def everyDet : Det.{u} := .ofSentence
  (∀' (Relations.boundedFormula₁ (.pred 0) &0 ⟹ Relations.boundedFormula₁ (.pred 1) &0))

/-- The determiner *some*, defined by `∃x (U x ∧ V x)`. -/
def someDet : Det.{u} := .ofSentence
  (∃' (Relations.boundedFormula₁ (.pred 0) &0 ⊓ Relations.boundedFormula₁ (.pred 1) &0))

/-- The determiner *no*, defined by `∀x (U x → ¬ V x)`. -/
def noDet : Det.{u} := .ofSentence
  (∀' (Relations.boundedFormula₁ (.pred 0) &0 ⟹ ∼(Relations.boundedFormula₁ (.pred 1) &0)))

/-! ### Theory-hub tie-ins

The GQ denotations the codebase already uses (`every`, `GQ.some`, `no`) are
exactly the realizations of the Lindström classes above. -/

theorem everyDet_toGQ (α : Type u) : everyDet.toGQ α = (every : GQ α) := by
  funext A B
  simp [Det.toGQ, everyDet, Sentence.Realize, Formula.Realize, Fin.snoc, every]

theorem someDet_toGQ (α : Type u) : someDet.toGQ α = (GQ.some : GQ α) := by
  funext A B
  simp [Det.toGQ, someDet, Sentence.Realize, Formula.Realize, Fin.snoc, GQ.some]

theorem noDet_toGQ (α : Type u) : noDet.toGQ α = (no : GQ α) := by
  funext A B
  simp [Det.toGQ, noDet, Sentence.Realize, Formula.Realize, Fin.snoc, no]

/-! ### The square of opposition

The relations of the square live on `GQ α` in `Quantification/Basic.lean`:
`every_contradicts_notEvery` and `no_contradicts_some`, and `a_e_contrary` and
`subalternation_a_i`, which need a non-empty restrictor, an instance of the logic-sensitivity
Demey and Frijters describe. This section shows that realization carries the class-level
structure to the GQ duality operators. Outer negation is the complement of the class
(`toGQ_compl`), the corners `no` and `some` are the inner negation and the dual of `every`
(`noDet_toGQ_eq_innerNeg`, `someDet_toGQ_eq_dual`), and the contradictory diagonal between `no`
and `some` is the class-level fact `some = ¬ no` (`someDet_holds_eq_compl`). -/

/-- As iso-invariant classes, `some` is the complement of `no`, since `∃x. Ux ∧ Vx` is the
negation of `∀x. Ux → ¬Vx`. Its image under `toGQ` is `Quantifier.GQ.no_contradicts_some`. -/
theorem someDet_holds_eq_compl : (someDet.{u}).holds = (noDet.{u}).holdsᶜ := by
  ext M
  simp [someDet, noDet, Sentence.Realize, Formula.Realize]

/-- Realization carries the complement of an iso-invariant class to GQ outer negation. With
`everyDet` this realizes the contradictory diagonal between `A` and `O` as
`Quantifier.GQ.every_contradicts_notEvery`. -/
theorem toGQ_compl (Q : Det.{u}) (α : Type u) : Det.toGQ Qᶜ α = (Q.toGQ α)ᶜ := by
  funext A B
  simp only [Det.toGQ, LindstromQuantifier.holds_compl, Set.mem_compl_iff, compl_apply]

/-- At the `E` corner, `no` realizes the inner negation of `every`. -/
theorem noDet_toGQ_eq_innerNeg (α : Type u) :
    noDet.toGQ α = innerNeg (everyDet.toGQ α) := by
  rw [noDet_toGQ, everyDet_toGQ, innerNeg_every]

/-- At the `I` corner, `some` realizes the dual of `every`. -/
theorem someDet_toGQ_eq_dual (α : Type u) :
    someDet.toGQ α = dual (everyDet.toGQ α) := by
  rw [someDet_toGQ, everyDet_toGQ, dual_every]

end Quantifier.Lindstrom
