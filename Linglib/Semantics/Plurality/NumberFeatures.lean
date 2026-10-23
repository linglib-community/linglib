/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Number.Basic
public import Linglib.Semantics.Plurality.Number
public import Linglib.Core.Order.UpperLower.Finset

/-!
# The feature decomposition of number

Harbour decomposes the three basic number values into two features, [±atomic] and [±minimal]. A
bundle is the set of its positive features, and it passes the containment filter when they form a
lower set of the chain minimal < atomic, so the three values are the chain's initial segments. For
number the filter follows from the semantics: an atom is minimal in every region excluding the
null individual (`Number.singular_subset_minimal`), so [+atomic, −minimal] corresponds to no
number, as Harbour observes. Lattice elements are classified by the regions of Harbour's
features (`Semantics/Plurality/Number.lean`).

## Main definitions

* `Number.Feature`, `Number.Features`: the two features and their bundles, with
  `Features.toNumber` and `Features.ofNumber` relating bundles to `Number`.
* `Number.latticeToFeatures`: the bundle a lattice element realizes in a region, singular on its
  atoms, dual on its minimal non-atoms, plural otherwise.
* `Number.dualPredOnLattice`: the dual as a predicate modifier.

## Main results

* `Number.card_wellFormed`: exactly three bundles pass the containment filter.
* `Number.toNumber_isSome_iff`, `Number.ofNumber_toNumber`, `Number.toNumber_ofNumber`: bundles
  and values correspond on those cells.
* `Number.latticeToFeatures_wellFormed`: classification never produces the filtered cell.
* `Number.dualPredOnLattice_iff`: the dual predicate modifier is the restriction to elements
  classified `dualF`.

## Implementation notes

Harbour argues that the features are bivalent, a privative encoding collapsing values such as
unit augmented and minimal; a bundle here is the set of positive values of a bivalent valuation,
the negative values being its complement. The examples use the powerset lattice `Finset (Fin n)`
on its nonempty subsets, whose atoms are the singletons.

## References

* [harbour-2014], §5.1, p. 213
* [harbour-2016], §9.5, pp. 222–223
* [link-1983]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025], §4.2.1, §8
-/

@[expose] public section

namespace Number

open Mereology (Atom CUM atomize)

/-! ### The feature bundle -/

/-- Harbour's two number features, atomicity depending on minimality. -/
inductive Feature where
  /-- `[minimal]` holds of a referent minimal in its region. -/
  | minimal
  /-- `[atomic]` holds of an atom. -/
  | atomic
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places minimal below atomic on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .minimal => 0
  | .atomic => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

/-- A number feature bundle is the set of its positive features. -/
abbrev Features := Finset Feature

open Finset in
/-- The singular is `[+atomic, +minimal]`, the whole chain. -/
def singularF : Features := Iic .atomic

open Finset in
/-- The dual is `[−atomic, +minimal]`, the chain below atomic. -/
def dualF : Features := Iic .minimal

/-- The plural is `[−atomic, −minimal]`, the empty bundle. -/
def pluralF : Features := ∅

theorem singularF_eq : singularF = {.minimal, .atomic} := by decide

theorem dualF_eq : dualF = {.minimal} := by decide

/-- The number value a bundle realizes; the ill-formed `[+atomic, −minimal]`
realizes none. -/
def Features.toNumber (f : Features) : Option Number :=
  if .atomic ∈ f then if .minimal ∈ f then some .singular else none
  else if .minimal ∈ f then some .dual else some .plural

/-- The bundle of a basic number value; the values that need feature
recursion or additivity have none. -/
def Features.ofNumber : Number → Option Features
  | .singular => some singularF
  | .dual => some dualF
  | .plural => some pluralF
  | _ => none

/-- Exactly three bundles pass the containment filter, the three basic number values. -/
theorem card_wellFormed : Fintype.card {nf : Features // IsLowerSet (↑nf : Set Feature)} = 3 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

theorem toNumber_isSome_iff :
    ∀ f : Features, f.toNumber.isSome ↔ IsLowerSet (↑f : Set Feature) := by
  decide

theorem ofNumber_toNumber :
    ∀ f : Features, IsLowerSet (↑f : Set Feature) → f.toNumber.bind Features.ofNumber = some f := by
  decide

theorem toNumber_ofNumber : ∀ (n : Number) (f : Features),
    Features.ofNumber n = some f → f.toNumber = some n := by
  decide

/-! ### Classification by lattice position -/

section Lattice

variable {D : Type*} [SemilatticeSup D] [Fintype D] [DecidableLE D]

/-- A lattice element realizes, in the region `P`, the singular on the atoms of `P`, the dual on
its minimal non-atoms, and the plural on the rest. -/
def latticeToFeatures (P : D → Prop) [DecidablePred P] (x : D) : Features :=
  if atomsOf P x then singularF else if dualOf P x then dualF else pluralF

/-- Classification never produces the ill-formed cell. -/
theorem latticeToFeatures_wellFormed (P : D → Prop) [DecidablePred P] (x : D) :
    IsLowerSet (↑(latticeToFeatures P x) : Set Feature) := by
  unfold latticeToFeatures
  split_ifs <;> decide

/-- The dual as a predicate modifier holds of `x` when `P x` and `x` has exactly two atomic parts,
being a minimal non-atom of the region `domain`
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025] (39)). -/
abbrev dualPredOnLattice (domain P : D → Prop) (x : D) : Prop :=
  P x ∧ dualOf domain x

/-- The dual predicate modifier is the restriction of `P` to the elements
classified `dualF`. -/
theorem dualPredOnLattice_iff (domain : D → Prop) [DecidablePred domain] (P : D → Prop)
    (x : D) : dualPredOnLattice domain P x ↔ P x ∧ latticeToFeatures domain x = dualF := by
  unfold latticeToFeatures
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [ite_eq_right fun ha => h.1.2 ha.2, ite_eq_left h]
  · intro h
    by_contra hd
    split_ifs at h with ha <;> exact absurd h (by decide)

end Lattice

/-! ### The powerset lattice -/

/-- The nonempty subsets of `Fin 3`, a lattice with three atoms. -/
def ps3 (s : Finset (Fin 3)) : Prop := s.Nonempty

instance : DecidablePred ps3 := fun s => inferInstanceAs (Decidable s.Nonempty)

example : latticeToFeatures ps3 {0} = singularF := by decide
example : latticeToFeatures ps3 {0, 1} = dualF := by decide
example : latticeToFeatures ps3 {0, 1, 2} = pluralF := by decide

example : dualPredOnLattice ps3 (fun _ => True) {0, 2} := by decide
example : ¬ dualPredOnLattice ps3 (fun _ => True) ({0, 1, 2} : Finset (Fin 3)) := by decide

/-- With three atoms the non-atomic region is cumulative, so `[±additive]`
cannot split it; the paucal/plural contrast needs a larger lattice. -/
example : CUM (fun s : Finset (Fin 3) => 2 ≤ s.card) := by decide

/-- A paucal region of two to three atoms is not cumulative, since `{0, 1} ⊔ {2, 3}` has four.
Complement completeness ([harbour-2014] (11)) holds of the plural region of four or more atoms. -/
example :
    ¬ CUM (fun s : Finset (Fin 5) => 2 ≤ s.card ∧ s.card ≤ 3) ∧
      CUM (fun s : Finset (Fin 5) => 4 ≤ s.card) := by
  decide

end Number
