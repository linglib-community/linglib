module

public import Linglib.Semantics.Genericity.Normality
public import Studies.Cohen1999

/-!
# Nickel (2009): Generics and the Ways of Normality

[nickel-2009] proposes that a characterizing sentence with restrictor `A` and matrix `F` is true
when there is a way of being a normal `A`, in the respect that `F` fixes, such that every `A`
normal in that way is `F`. A way of being normal is here a `Genericity.Normality`, the ways of
being normal in the respect of a matrix are a set `ways F` of them, and we define
`gen ways A F ↔ ∃ N ∈ ways F, N.gen A F`.

The paper's argument concerns generics whose matrices exclude one another, as in *elephants live
in Africa and elephants live in Asia*. On a majority-based account such as the probabilistic one
of [cohen-1999a], two generics with one restrictor have compatible matrices
(`not_disjoint_of_gen_of_gen`), so the two conjuncts cannot both be true. With one way of being
normal the two conjuncts leave the restrictor no normal case
(`normal_eq_empty_of_gen_of_gen`). With a way for each matrix both conjuncts are true, and where
each is instantiated the generic with the conjoined matrix is false (`gen_and_not_gen_inter`).

## Implementation notes

* A way of being normal is a normality and not a set of individuals, so that a way may select
  its normal cases by any means. The ways of the paper's examples are the normalities
  `Genericity.Normality.restrict F`, whose normal cases are the cases that are `F`.
* The ways depend on the matrix through the function `ways`, which stands for the respect of
  normality that the matrix determines.
* The paper notes that its truth conditions need a counterfactual element where nothing is
  normal in the relevant respect. That element is not represented, and `gen ways A F` holds when
  some way in `ways F` leaves `A` no normal case.

## References

* [nickel-2009]
* [cohen-1999a]
-/

@[expose] public section

namespace Nickel2009

open Genericity Quantifier MeasureTheory Set

variable {α : Type*}

/-! ### Majority-based accounts -/

/-- On the probabilistic account, two generics with one restrictor have compatible matrices. -/
theorem not_disjoint_of_gen_of_gen [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {ψ φ φ' : Set α} (hψ : MeasurableSet ψ) (hφ' : MeasurableSet φ')
    (h : Cohen1999.gen μ ψ φ) (h' : Cohen1999.gen μ ψ φ') : ¬ Disjoint φ φ' := by
  intro hd
  rw [Cohen1999.gen_iff_lt hψ] at h h'
  have hu : μ (ψ ∩ φ) + μ (ψ ∩ φ') ≤ μ ψ := by
    rw [← measure_union (hd.mono inter_subset_right inter_subset_right) (hψ.inter hφ'),
      ← inter_union_distrib_left]
    exact measure_mono inter_subset_left
  have hlt := ENNReal.add_lt_add h h'
  rw [← mul_add, ← two_mul] at hlt
  exact (hlt.trans_le (by gcongr)).false

/-! ### Ways of being normal -/

variable {ways : Set α → Set (Normality α)} {N : Normality α} {A F F' : Set α}

/-- The truth conditions for characterizing sentences: there is a way of being normal in the
respect of the matrix such that every normal case of the restrictor is a case of the matrix. -/
def gen (ways : Set α → Set (Normality α)) : Det α :=
  fun A F ↦ ∃ N ∈ ways F, N.gen A F

theorem gen_iff : gen ways A F ↔ ∃ N ∈ ways F, N.gen A F := Iff.rfl

@[simp]
theorem gen_singleton : gen (fun _ ↦ {N}) A F ↔ N.gen A F := by
  simp [gen]

theorem gen_of_restrict_mem (h : Normality.restrict F ∈ ways F) : gen ways A F :=
  ⟨_, h, inter_subset_left⟩

/-- With one way of being normal, two generics with one restrictor and disjoint matrices leave
the restrictor no normal case. -/
theorem normal_eq_empty_of_gen_of_gen (h : gen (fun _ ↦ {N}) A F) (h' : gen (fun _ ↦ {N}) A F')
    (hd : Disjoint F F') : N.normal A = ∅ :=
  N.normal_eq_empty_of_disjoint (gen_singleton.1 h) (gen_singleton.1 h')
    (hd.mono_left inter_subset_right)

/-- (22): with a way of being normal for each of two disjoint matrices that the restrictor
instantiates, each generic is true and the generic with the conjoined matrix is false. -/
theorem gen_and_not_gen_inter (hd : Disjoint F F') (hF : (A ∩ F).Nonempty)
    (hF' : (A ∩ F').Nonempty) :
    gen (fun _ ↦ {.restrict F, .restrict F'}) A F ∧
      gen (fun _ ↦ {.restrict F, .restrict F'}) A F' ∧
        ¬ gen (fun _ ↦ {.restrict F, .restrict F'}) A (F ∩ F') := by
  refine ⟨gen_of_restrict_mem (.inl rfl), gen_of_restrict_mem (.inr rfl), ?_⟩
  rintro ⟨N, rfl | rfl, hN⟩
  · obtain ⟨x, hA, hx⟩ := hF
    exact hd.le_bot ⟨hx, (hN ⟨hx, hA⟩).2⟩
  · obtain ⟨x, hA, hx⟩ := hF'
    exact hd.le_bot ⟨(hN ⟨hx, hA⟩).1, hx⟩

end Nickel2009
