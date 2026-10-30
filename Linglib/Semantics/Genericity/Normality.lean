module

public import Linglib.Semantics.Conditionals.Basic
public import Mathlib.Order.WellFoundedSet

/-!
# The generic operator

GEN, the operator of characterizing sentences, quantifies over the normal cases of its
restrictor, which a `Normality` picks out among its cases, and unlike the universal it
[tolerates exceptions](##exists_mem_gen_not_subset). Normal cases fixed in advance make it
[the strict conditional](##gen_ofAccess). The best cases of a preorder make it, under the Limit
Assumption,
[the variably strict conditional of the modal analysis](##gen_ofOrdering_eq_variablyStrictImp),
which without that assumption [no normality gives](##not_exists_gen_eq_variablyStrictImp). Two
generics with one restrictor and disjoint matrices
[make every generic with that restrictor true](##mem_gen_of_disjoint).

## Main definitions

* `Genericity.Normality`: a selection of the normal cases of each restrictor.
* `Genericity.Normality.gen`: GEN, the conditional over the normal cases.
* `Genericity.Normality.ofAccess`, `Genericity.Normality.ofOrdering`: normality by a fixed set
  of normal cases and by a preorder.

## Implementation notes

* GEN is evaluated at an index (a world, a world and a time, a context) and quantifies over cases
  of another type (individuals, events, situations, worlds), so a normality has both as
  parameters. Restrictors and matrices are sets of cases, and GEN is the domain conditional
  `Conditional.ofDomain` of the normality.
* A normality is the selection function of [asher-morreau-1995] under their one constraint,
  Facticity, that the normal cases of a restrictor are among its cases (`Normality.normal_subset`).
* Of the analyses [krifka-etal-1995] survey, relevant quantification is `ofAccess`, and the
  prototype analysis and the modal analysis are `ofOrdering` and `Conditional.variablyStrictImp`
  over an ordering of the cases.

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

section Ordering

variable {access : I → Set X} {ord : I → Preorder X}

@[simp]
theorem gen_ofOrdering : (ofOrdering access ord).gen = orderingImp access ord := rfl

/-- Under the Limit Assumption, that each preorder is well founded on the accessible cases, so that
every nonempty set of them has best members, GEN over the best accessible cases is the modal
analysis (86), the variably strict conditional over the ordering source. -/
theorem gen_ofOrdering_eq_variablyStrictImp (hlim : ∀ i, (access i).WellFoundedOn (ord i).lt) :
    (ofOrdering access ord).gen R S = variablyStrictImp access ord R S :=
  ext fun i ↦ (mem_variablyStrictImp_iff_mem_orderingImp fun _ hB ↦
    letI := ord i; ((hlim i).subset inter_subset_left).exists_minimal hB).symm

theorem gen_ofOrdering_eq_variablyStrictImp_of_finite (hfin : ∀ i, (access i).Finite) :
    (ofOrdering access ord).gen R S = variablyStrictImp access ord R S :=
  gen_ofOrdering_eq_variablyStrictImp fun i ↦ (hfin i).wellFoundedOn

end Ordering

private theorem notMem_variablyStrictImp_empty :
    () ∉ variablyStrictImp (fun _ ↦ univ) (fun _ ↦ (inferInstance : Preorder ℤ)) univ ∅ :=
  fun h ↦ by
    rw [mem_variablyStrictImp, OrderingSemantics.mem_necessityFilter] at h
    obtain ⟨v, hv, -, hvt⟩ := h 0 ⟨trivial, trivial⟩
    exact hvt v hv le_rfl

private theorem mem_variablyStrictImp_Iic (n : ℤ) :
    () ∈ variablyStrictImp (fun _ ↦ univ) (fun _ ↦ (inferInstance : Preorder ℤ)) univ (Iic n) := by
  rw [mem_variablyStrictImp, OrderingSemantics.mem_necessityFilter]
  exact fun u _ ↦ ⟨min u n, ⟨trivial, trivial⟩, min_le_left u n,
    fun _ _ hw ↦ hw.trans (min_le_right u n)⟩

/-- Without the Limit Assumption GEN over the best cases can hold vacuously: on the integers no
case is best, so every generic is true, while the modal analysis (86) is false of a matrix that no
case satisfies. -/
theorem exists_gen_ofOrdering_not_variablyStrictImp :
    ∃ (access : Unit → Set ℤ) (ord : Unit → Preorder ℤ),
      (∀ S, (ofOrdering access ord).gen univ S = univ) ∧
        () ∉ variablyStrictImp access ord univ ∅ := by
  refine ⟨fun _ ↦ univ, fun _ ↦ inferInstance, fun _ ↦ eq_univ_of_forall fun _ x hx ↦ ?_,
    notMem_variablyStrictImp_empty⟩
  have hle : x - 1 ≤ x := by omega
  have h : x ≤ x - 1 := hx.2 ⟨trivial, trivial⟩ hle
  exact absurd h (by omega)

/-- Without the Limit Assumption no normality gives the modal analysis (86): on the integers every
down-ray is a generic consequence of the trivial restrictor and the empty matrix is not, so the
normal cases would lie in every down-ray and be none. -/
theorem not_exists_gen_eq_variablyStrictImp :
    ¬ ∃ N : Normality Unit ℤ, ∀ R S,
      N.gen R S = variablyStrictImp (fun _ ↦ univ) (fun _ ↦ inferInstance) R S := by
  rintro ⟨N, hN⟩
  have h : () ∈ N.gen univ ∅ := N.mem_gen.2 fun x hx ↦ by
    have hx' : () ∈ N.gen univ (Iic (x - 1)) := by
      rw [hN]; exact mem_variablyStrictImp_Iic _
    exact absurd (mem_Iic.1 (N.mem_gen.1 hx' hx)) (by omega)
  rw [hN] at h
  exact notMem_variablyStrictImp_empty h

end Normality

end Genericity
