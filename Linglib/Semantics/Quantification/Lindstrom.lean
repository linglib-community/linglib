module

public import Linglib.Core.Data.Fin.VecNotation
public import Linglib.Core.ModelTheory.Lindstrom
public import Linglib.Core.ModelTheory.Monadic
public import Linglib.Semantics.Quantification.Basic

/-!
# Realizing Lindström quantifiers as determiner denotations

A determiner, a Lindström quantifier of type `⟨1,1⟩`, is an isomorphism-invariant class of
structures for the monadic language with two predicate symbols, the restrictor `pred 0` and the
scope `pred 1`. `Det.toDet` realizes it as a determiner denotation `Quantifier.Det α`: a pair
of sets `(A, B)` becomes the structure `(α, A, B)`, and the quantifier holds of `(A, B)` when
that structure is in the class. Quantity invariance is then a theorem about every realized
determiner, and the determiners defined by the sentences for *every*, *some* and *no* realize the
denotations of `Quantification/Basic.lean`.

The language is `Language.monadic (Fin 2)`, so the monadic Ehrenfeucht–Fraïssé results apply to
determiners directly: `foDefinable_iff_exists_min_encard_eq` is van Benthem's characterization of
the first-order definable determiners as those invariant under agreement of the four Venn region
sizes up to a threshold.

## Main definitions

* `Det`, `Det.toDet`, `Det.toFamily`: determiners and their realization as determiner
  denotations, on one universe and on all finite universes.
* `everyDet`, `someDet`, `noDet`: the determiners of the square of opposition.

## Main results

* `Det.isom_toFamily`: the realization of a determiner is closed under isomorphism across
  universes, and so permutation invariant on each (`Det.realize_quantityInvariant`).
* `everyDet_toDet`, `someDet_toDet`, `noDet_toDet`: the realizations are `every`,
  `Quantifier.Det.some` and `no`.
* `toDet_compl`: realization carries the complement of a class to outer negation.
* `someDet_holds_eq_compl`, `noDet_toDet_eq_innerNeg`, `someDet_toDet_eq_dual`: the `no` and
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

open Quantifier.Det

open FirstOrder Language BoundedFormula
open CategoryTheory (Bundled)

/-! ### The realization functor -/

/-- A *determiner* is a Lindström quantifier of type `⟨1,1⟩`, an iso-invariant class of
structures for the monadic language with a restrictor and a scope predicate. -/
abbrev Det := LindstromQuantifier.{0, 0, u} (Language.monadic (Fin 2))

namespace Det

/-- `Q.toDet α` holds of `(A, B)` iff the structure `(α, A, B)` is in the class `Q`. -/
def toDet (Q : Det.{u}) (α : Type u) : Quantifier.Det α :=
  fun A B => (⟨α, monadic.structure ![A, B]⟩ : Bundled.{u} (Language.monadic (Fin 2)).Structure)
    ∈ Q.holds

/-- Every realized Lindström quantifier is permutation invariant, derived from `iso_inv` rather
than stipulated on the denotation. -/
theorem realize_quantityInvariant (Q : Det.{u}) {α : Type u} :
    (Q.toDet α).QuantityInvariant := fun σ _ _ ↦
  Q.iso_inv ⟨monadic.structureEquiv σ (Fin.forall_fin_two.2 ⟨fun _ ↦ .rfl, fun _ ↦ .rfl⟩)⟩

/-- The global determiner denotation of a Lindström quantifier, its realization on every finite
universe. -/
def toFamily (Q : Det.{u}) : Quantifier.Det.Family.{u} := fun α _ ↦ Q.toDet α

/-- A Lindström quantifier is closed under isomorphism across universes, since isomorphic
structures are equally in its class: isomorphism closure is Lindström's own condition. -/
theorem isom_toFamily (Q : Det.{u}) : Q.toFamily.Isom := fun _ _ _ _ e _ _ ↦
  Q.iso_inv ⟨monadic.structureEquiv e (Fin.forall_fin_two.2 ⟨fun _ ↦ .rfl, fun _ ↦ .rfl⟩)⟩

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

The determiner denotations the codebase already uses (`every`, `Quantifier.Det.some`, `no`) are
exactly the realizations of the Lindström classes above. -/

theorem everyDet_toDet (α : Type u) : everyDet.toDet α = (every : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, everyDet, Sentence.Realize, Formula.Realize, Fin.snoc, every]
  exact Iff.rfl

theorem someDet_toDet (α : Type u) :
    someDet.toDet α = (Quantifier.Det.some : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, someDet, Sentence.Realize, Formula.Realize, Fin.snoc, Quantifier.Det.some]
  exact Iff.rfl

theorem noDet_toDet (α : Type u) : noDet.toDet α = (no : Quantifier.Det α) := by
  funext A B
  simp [Det.toDet, noDet, Sentence.Realize, Formula.Realize, Fin.snoc, no]
  exact Iff.rfl

/-! ### The square of opposition

The relations of the square live on `Quantifier.Det α` in `Quantification/Basic.lean`:
`every_contradicts_notEvery` and `no_contradicts_some`, and `a_e_contrary` and
`subalternation_a_i`, which need a non-empty restrictor, an instance of the logic-sensitivity
Demey and Frijters describe. This section shows that realization carries the class-level
structure to the duality operators of determiner denotations. Outer negation is the complement
of the class (`toDet_compl`), the corners `no` and `some` are the inner negation and the dual of
`every` (`noDet_toDet_eq_innerNeg`, `someDet_toDet_eq_dual`), and the contradictory diagonal
between `no` and `some` is the class-level fact `some = ¬ no` (`someDet_holds_eq_compl`). -/

/-- As iso-invariant classes, `some` is the complement of `no`, since `∃x. Ux ∧ Vx` is the
negation of `∀x. Ux → ¬Vx`. Its image under `toDet` is `Quantifier.Det.no_contradicts_some`. -/
theorem someDet_holds_eq_compl : (someDet.{u}).holds = (noDet.{u}).holdsᶜ := by
  ext M
  simp [someDet, noDet, Sentence.Realize, Formula.Realize]

/-- Realization carries the complement of an iso-invariant class to outer negation. With
`everyDet` this realizes the contradictory diagonal between `A` and `O` as
`Quantifier.Det.every_contradicts_notEvery`. -/
theorem toDet_compl (Q : Det.{u}) (α : Type u) : Det.toDet Qᶜ α = (Q.toDet α)ᶜ := by
  funext A B
  simp only [Det.toDet, LindstromQuantifier.holds_compl, Set.mem_compl_iff, compl_apply]

/-- At the `E` corner, `no` realizes the inner negation of `every`. -/
theorem noDet_toDet_eq_innerNeg (α : Type u) :
    noDet.toDet α = innerNeg (everyDet.toDet α) := by
  rw [noDet_toDet, everyDet_toDet, innerNeg_every]

/-- At the `I` corner, `some` realizes the dual of `every`. -/
theorem someDet_toDet_eq_dual (α : Type u) :
    someDet.toDet α = dual (everyDet.toDet α) := by
  rw [someDet_toDet, everyDet_toDet, dual_every]

end Quantifier.Lindstrom
