module

public import Linglib.Semantics.Conditionals.Basic

/-!
# The generic operator

This file defines the generic operator GEN of characterizing sentences as the conditional
quantifying over the normal cases of its restrictor. [krifka-etal-1995] survey the ways of
spelling GEN out. On the prototype analysis a characterizing sentence quantifies universally over
the typical instances of its restrictor, (80) and (81), and on relevant quantification over the
restrictor cases that meet a contextual restriction, (78). Each picks out, for a restrictor, a set
of normal cases inside it, and the generic holds when the matrix holds throughout that set. A
normality is such a selection (`Normality`), the selection function of [asher-morreau-1995] under
their one constraint, Facticity, and GEN is the conditional over its domain (`Normality.gen`), the
domain conditional `Conditional.ofDomain` of the conditionals file. The modal analysis, (86), is
not a selection: GEN holds when every case of the restrictor in the modal base has one at least as
normal from which on the matrix holds, the variably strict conditional
`Conditional.variablyStrictImp` over the ordering source.

Unlike the universal, GEN tolerates exceptions, (74) (`Normality.exists_mem_gen_not_subset`),
though a universal generalization is a generic one (`Normality.gen_eq_univ_of_subset`), and when
every case is normal it is the universal (`Normality.mem_gen_top`). A normality given by a fixed
set of normal cases, as on relevant quantification, makes GEN the strict conditional
(`Normality.ofAccess`, `Normality.gen_ofAccess`). It overgenerates, since the restriction can be
the matrix itself, [krifka-etal-1995]'s (79) (`Normality.gen_ofAccess_self`).
A normality given by a preorder on the cases makes GEN the conditional of the best accessible
cases (`Normality.ofOrdering`, `Normality.gen_ofOrdering`). This is the modal analysis under the
Limit Assumption, that every set of accessible cases has best members
(`Normality.gen_ofOrdering_eq_variablyStrictImp`); without it a restrictor can have no best
cases, and then every generic with it is true where the modal analysis is not
(`Normality.exists_gen_ofOrdering_not_variablyStrictImp`). Whatever the normality, two generics
with one restrictor and disjoint matrices leave the restrictor no normal case, and then every
generic with that restrictor is true. This is the problem of (82) for the prototype analysis:
male ducks have colorful feathers and female ducks lay whitish eggs, so no duck is typical for
both, and every sentence *a duck Fs* comes out true (`Normality.normal_eq_empty_of_disjoint`,
`Normality.mem_gen_of_disjoint`). Generics with disjoint matrices and different restrictors
select disjoint normal cases (`Normality.disjoint_normal_of_disjoint`).

## Main definitions

* `Genericity.Normality`: a selection of the normal cases of each restrictor.
* `Genericity.Normality.gen`: GEN, the conditional over the normal cases.
* `Genericity.Normality.ofAccess`, `Genericity.Normality.ofOrdering`: normality by a fixed set
  of normal cases and by a preorder.

## Implementation notes

* GEN is evaluated at an index (a world, a world and a time, a context) and quantifies over cases
  of another type (individuals, events, situations, worlds), so a normality has both as
  parameters. Restrictors and matrices are sets of cases, as for the conditionals.
* The one law every selection shares, Asher and Morreau's Facticity, is that the normal cases of a
  restrictor are among its cases. Normality is not monotone in the restrictor: the normal penguins
  need not be normal birds.

## TODO

* The probabilistic generic of [cohen-1999a] and [tessler-goodman-2019], a threshold on the
  conditional probability of the matrix given the restrictor, on mathlib measures.
* The homogeneity presupposition of GEN of `Studies/Magri2009`, beside
  `Conditional.homogeneityCounterfactual`.

## References

* [krifka-etal-1995]
* [asher-morreau-1995]
* [cohen-1999a]
* [tessler-goodman-2019]
-/

@[expose] public section

namespace Genericity

open Conditional Set

/-- A normality on cases `X` at indices `I`: for each index and restrictor, the normal cases of
the restrictor, which are cases of it. -/
structure Normality (I X : Type*) where
  /-- The normal cases of a restrictor at an index. -/
  normal : I → Set X → Set X
  /-- The normal cases of a restrictor are cases of it. -/
  normal_subset (i : I) (R : Set X) : normal i R ⊆ R

namespace Normality

variable {I X : Type*} (N : Normality I X) {R S S' : Set X} {i : I}

/-- GEN with restrictor `R` and matrix `S`, true at the indices where every normal case of `R` is
a case of `S`. -/
def gen (R S : Set X) : Set I := ofDomain N.normal R S

@[simp]
theorem mem_gen : i ∈ N.gen R S ↔ N.normal i R ⊆ S := Iff.rfl

theorem gen_eq_univ_of_subset (h : R ⊆ S) : N.gen R S = univ :=
  ofDomain_eq_univ fun i ↦ (N.normal_subset i R).trans h

theorem disjoint_normal_of_disjoint {R' : Set X} (hS : i ∈ N.gen R S) (hS' : i ∈ N.gen R' S')
    (h : Disjoint S S') : Disjoint (N.normal i R) (N.normal i R') :=
  h.mono hS hS'

/-- (82): two generics with one restrictor and disjoint matrices leave the restrictor no normal
case. -/
theorem normal_eq_empty_of_disjoint (hS : i ∈ N.gen R S) (hS' : i ∈ N.gen R S')
    (h : Disjoint S S') : N.normal i R = ∅ :=
  disjoint_self.1 (N.disjoint_normal_of_disjoint hS hS' h)

/-- (82): two generics with one restrictor and disjoint matrices make every generic with that
restrictor true. -/
theorem mem_gen_of_disjoint (hS : i ∈ N.gen R S) (hS' : i ∈ N.gen R S') (h : Disjoint S S')
    (T : Set X) : i ∈ N.gen R T := by
  simp [N.normal_eq_empty_of_disjoint hS hS' h]

/-- The normality on which every case of a restrictor is normal. -/
instance : Top (Normality I X) := ⟨⟨fun _ R ↦ R, fun _ _ ↦ subset_rfl⟩⟩

@[simp]
theorem mem_gen_top : i ∈ (⊤ : Normality I X).gen R S ↔ R ⊆ S := Iff.rfl

/-- The normality of relevant quantification, (78): the normal cases of a restrictor at an index
are its cases in a fixed set. -/
def ofAccess (B : I → Set X) : Normality I X :=
  ⟨fun i R ↦ B i ∩ R, fun _ _ ↦ inter_subset_right⟩

theorem gen_ofAccess (B : I → Set X) : (ofAccess B).gen = strictImp B := rfl

/-- (79): restricted to the cases of its own matrix, every generic is true, so relevant
quantification needs a theory of the admissible restrictions. -/
theorem gen_ofAccess_self : (ofAccess fun _ : I ↦ S).gen R S = univ :=
  ofDomain_eq_univ fun _ ↦ inter_subset_left

/-- (74): unlike the universal, a generic tolerates exceptions; a cat that lost its tail does not
falsify *a cat has a tail*. -/
theorem exists_mem_gen_not_subset :
    ∃ (N : Normality Unit Bool) (R S : Set Bool), () ∈ N.gen R S ∧ ¬ R ⊆ S :=
  ⟨ofAccess fun _ ↦ {true}, univ, {true}, fun _ hx ↦ hx.1,
    fun h ↦ Bool.false_ne_true (h (mem_univ false))⟩

/-- The normality of a preorder on the cases: the normal cases of a restrictor at an index are
its best accessible cases. -/
def ofOrdering (access : I → Set X) (ord : I → Preorder X) : Normality I X :=
  ⟨fun i R ↦ (ord i).minimals (access i ∩ R),
    fun i _ ↦ ((ord i).minimals_subset _).trans inter_subset_right⟩

theorem gen_ofOrdering (access : I → Set X) (ord : I → Preorder X) :
    (ofOrdering access ord).gen = orderingImp access ord := rfl

/-- The modal analysis (86) entails GEN over the best accessible cases. -/
theorem variablyStrictImp_subset_gen_ofOrdering (access : I → Set X) (ord : I → Preorder X) :
    variablyStrictImp access ord R S ⊆ (ofOrdering access ord).gen R S :=
  variablyStrictImp_subset_orderingImp

/-- Under the Limit Assumption, that every nonempty set of accessible cases has best members, the
modal analysis (86) is GEN over the best accessible cases. -/
theorem gen_ofOrdering_eq_variablyStrictImp {access : I → Set X} {ord : I → Preorder X}
    (hlim : ∀ i B, (access i ∩ B).Nonempty → ((ord i).minimals (access i ∩ B)).Nonempty) :
    (ofOrdering access ord).gen R S = variablyStrictImp access ord R S :=
  ext fun i ↦ (mem_variablyStrictImp_iff_mem_orderingImp (hlim i)).symm

theorem gen_ofOrdering_eq_variablyStrictImp_of_finite [Finite X] (access : I → Set X)
    (ord : I → Preorder X) : (ofOrdering access ord).gen R S = variablyStrictImp access ord R S :=
  gen_ofOrdering_eq_variablyStrictImp fun i _ ↦ (ord i).minimals_nonempty

/-- Without the Limit Assumption, GEN over the best cases can hold vacuously: on the integers no
case is best, so every generic is true, while the modal analysis (86) is false of a matrix that no
case satisfies. -/
theorem exists_gen_ofOrdering_not_variablyStrictImp :
    ∃ (access : Unit → Set ℤ) (ord : Unit → Preorder ℤ),
      (∀ S, (ofOrdering access ord).gen univ S = univ) ∧
        () ∉ variablyStrictImp access ord univ ∅ := by
  refine ⟨fun _ ↦ univ, fun _ ↦ inferInstance, fun _ ↦ eq_univ_of_forall fun _ x hx ↦ ?_,
    fun h ↦ ?_⟩
  · have hle : x - 1 ≤ x := by omega
    have h : x ≤ x - 1 := hx.2 ⟨trivial, trivial⟩ hle
    exact absurd h (by omega)
  · rw [mem_variablyStrictImp, OrderingSemantics.mem_necessityFilter] at h
    obtain ⟨v, hv, -, hvt⟩ := h 0 ⟨trivial, trivial⟩
    exact hvt v hv le_rfl

end Normality

end Genericity
