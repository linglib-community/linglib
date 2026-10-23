module

public import Linglib.Semantics.Questions.Partition.Basic
public import Linglib.Core.Order.Partition.Finpartition
public import Linglib.Core.Probability.Decision.ValueOfInformation
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Partition.Finpartition

/-!
# Merin (1999): Negative Attributes, Partitions, and Rational Decisions

Merin argues that attribute spaces are partitions for decision-theoretic reasons and
characterizes negative attributes epistemically, as proper coarsenings, rather than by their
form. The complements of a partition's cells form a partition, and their probabilities a
distribution, only when the partition has two cells. The partition of a cell and its complement
is the coarsest coarsening that decides the cell, and an attribute is negative when its
complement is a cell and its two-cell partition properly coarsens the partition.

## Main statements

* `compl_isPartition_iff`: the complements of the cells form a partition exactly for two cells.
* `sum_measureReal_compl`, `sum_measureReal_compl_eq_one_iff`: the complement probabilities sum
  to one less than the number of cells, and to one exactly for two cells.
* `isGreatest_polar_cell`: a cell and its complement give the coarsest coarsening deciding it.
* `integral_eq_partitionEU`, `partitionEU_congr`: expected utility computed cell by cell does not
  depend on the partition.

## Implementation notes

Coarsening is the refinement order on `Setoid`. Expected utility integrates a utility against a
prior measure independent of the act; the paper's computation for coarsenings uses Jeffrey's
form, with probabilities conditional on the act.

## TODO

The paper's point that under a coarsening each coarse cell's term is the sum of the terms of the
finer cells it contains, and FACT 5, that re-coverings which neither coarsen nor refine admit no
such regrouping, are not formalized; nor is the conditional-independence result of
[johnson-1986] that the paper cites.

## References

* [merin-1999]
* [johnson-1986]
-/

@[expose] public section

namespace Merin1999b

/-! ### FACT 1: complement families -/

/-- The complements of the cells of a partition of a nonempty type form a partition exactly
when it has two cells (FACT 1 of [merin-1999]). -/
theorem compl_isPartition_iff {W : Type*} [Nonempty W] {F : Set (Set W)}
    (hF : Setoid.IsPartition F) :
    Setoid.IsPartition (compl '' F) ↔ F.encard = 2 := by
  have cover : ∀ a : W, ∃ B ∈ F, a ∈ B := fun a ↦
    let ⟨B, hB, _⟩ := hF.2 a; ⟨B, hB.1, hB.2⟩
  have uniq : ∀ {a : W} {B₁ B₂ : Set W}, B₁ ∈ F → B₂ ∈ F →
      a ∈ B₁ → a ∈ B₂ → B₁ = B₂ := by
    intro a B₁ B₂ h1 h2 ha1 ha2
    obtain ⟨B, _, hu⟩ := hF.2 a
    rw [hu B₁ ⟨h1, ha1⟩, hu B₂ ⟨h2, ha2⟩]
  constructor
  · intro hFc
    -- A first cell, through an arbitrary point.
    obtain ⟨A, hA, haA⟩ := cover (Classical.arbitrary W)
    -- A second cell: `Aᶜ ≠ ∅` (it is a cell of the complement
    -- partition), so some point lies outside `A`.
    have hAc : Aᶜ ∈ compl '' F := Set.mem_image_of_mem _ hA
    obtain ⟨b, hb⟩ : Set.Nonempty (Aᶜ) :=
      Set.nonempty_iff_ne_empty.mpr (fun h ↦ hFc.1 (h ▸ hAc))
    obtain ⟨B, hB, hbB⟩ := cover b
    have hBA : B ≠ A := fun h ↦ hb (h ▸ hbB)
    -- No third cell: its points would witness overlap of `Aᶜ` and `Bᶜ`.
    have hall : ∀ C ∈ F, C = A ∨ C = B := by
      intro C hC
      by_contra hne
      push Not at hne
      obtain ⟨hCA, hCB⟩ := hne
      obtain ⟨c, hc⟩ : Set.Nonempty C :=
        Set.nonempty_iff_ne_empty.mpr (fun h ↦ hF.1 (h ▸ hC))
      have hcA : c ∈ Aᶜ := fun h ↦ hCA (uniq hC hA hc h)
      have hcB : c ∈ Bᶜ := fun h ↦ hCB (uniq hC hB hc h)
      obtain ⟨D, _, hu⟩ := hFc.2 c
      have h1 := hu Aᶜ ⟨Set.mem_image_of_mem _ hA, hcA⟩
      have h2 := hu Bᶜ ⟨Set.mem_image_of_mem _ hB, hcB⟩
      exact hBA (compl_inj_iff.mp (h2.trans h1.symm))
    have hFeq : F = {A, B} := by
      ext C
      constructor
      · intro hC
        rcases hall C hC with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · exact hA
        · exact hB
    rw [hFeq]
    exact Set.encard_pair (Ne.symm hBA)
  · intro h2
    obtain ⟨A, B, hAB, rfl⟩ := Set.encard_eq_two.mp h2
    have hA : A ∈ ({A, B} : Set (Set W)) := Set.mem_insert _ _
    have hB : B ∈ ({A, B} : Set (Set W)) := Set.mem_insert_of_mem _ rfl
    -- In a binary partition the two cells are mutual complements.
    have hcompl : Aᶜ = B := by
      ext a
      constructor
      · intro haAc
        rcases cover a with ⟨C, hC, haC⟩
        rcases hC with rfl | rfl
        · exact absurd haC haAc
        · exact haC
      · intro haB haA
        exact hAB (uniq hA hB haA haB)
    have hcompl' : Bᶜ = A := by rw [← hcompl, compl_compl]
    have himg : compl '' {A, B} = {A, B} := by
      rw [Set.image_pair, hcompl, hcompl', Set.pair_comm]
    rw [himg]
    exact hF

/-! ### FACTs 2 and 3: complement probabilities -/

section Probability

open MeasureTheory

variable {M : Type*} [MeasurableSpace M] (μ : Measure M) [IsProbabilityMeasure μ]
  {F : Finset (Set M)}

/-- Under a probability measure the probabilities of the complements of the `n` cells of a
finite partition sum to `n − 1` (FACT 3 of [merin-1999]). -/
theorem sum_measureReal_compl (hF : Setoid.IsPartition (F : Set (Set M)))
    (hm : ∀ c ∈ F, MeasurableSet c) :
    ∑ c ∈ F, μ.real cᶜ = F.card - 1 := by
  have hsum : ∑ c ∈ F, μ.real c = 1 := by
    have h := measureReal_biUnion_finset (μ := μ) hF.pairwiseDisjoint hm
    simp only [id] at h
    rw [← h, ← Finset.set_biUnion_coe, ← Set.sUnion_eq_biUnion, hF.sUnion_eq_univ, probReal_univ]
  rw [Finset.sum_congr rfl fun c hc ↦ probReal_compl_eq_one_sub (hm c hc),
    Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The complement probabilities sum to one exactly when the partition has two cells, so for
more than two cells they are not a distribution (FACTs 2 and 3 of [merin-1999]). -/
theorem sum_measureReal_compl_eq_one_iff (hF : Setoid.IsPartition (F : Set (Set M)))
    (hm : ∀ c ∈ F, MeasurableSet c) :
    ∑ c ∈ F, μ.real cᶜ = 1 ↔ F.card = 2 := by
  rw [sum_measureReal_compl μ hF hm]
  constructor
  · intro h
    exact_mod_cast (by linarith : (F.card : ℝ) = 2)
  · intro h
    rw [h]
    norm_num

end Probability

/-! ### Coarsening and negative attributes -/

/-- `Q` properly coarsens `Q'` when it is strictly coarser in the refinement order, which over
a finite domain means coarsening with strictly fewer cells ([merin-1999]). -/
def IsProperCoarsening {M : Type*} (q q' : Setoid M) : Prop := q' < q

/-- For a cell `P` of a partition, the partition `{P, ¬P}` is its coarsest coarsening that
decides `P` (FACT 4 of [merin-1999]). -/
theorem isGreatest_polar_cell {M : Type*} (q : Setoid M) (w : M) :
    IsGreatest {q' | q ≤ q' ∧ q'.Decides (q.cell w)} (Setoid.polar (q.cell w)) :=
  ⟨⟨Setoid.decides_cell w, Setoid.polar_decides⟩, fun _ h ↦ h.2⟩

/-- An attribute `R` is negative with respect to `q` when the complement of `R` is a cell of `q`
and the partition `{R, ¬R}` properly coarsens `q` ([merin-1999]). -/
def IsNegativeAttribute {M : Type*} (R : Set M) (q : Setoid M) : Prop :=
  (∃ w, q.cell w = Rᶜ) ∧ IsProperCoarsening (Setoid.polar R) q

/-! ### EU compositionality under coarsening -/

section ExpectedUtility

open MeasureTheory ProbabilityTheory

variable {M A : Type*} [Fintype M] [DecidableEq M] [MeasurableSpace M] [DiscreteMeasurableSpace M]
  [Nonempty M]

/-- The expected utility of an act computed through a partition weights each cell's conditional
expected utility by the cell's probability. -/
noncomputable def partitionEU (μ : Measure M) (U : M → A → ℝ) (q : Setoid M) [DecidableRel q]
    (a : A) : ℝ :=
  ∑ cell ∈ (Finpartition.ofSetoid q).parts, μ.real cell * ∫ m, U m a ∂μ[|cell]

/-- Expected utility computed through any partition is the expected utility. -/
theorem integral_eq_partitionEU (μ : Measure M) [IsProbabilityMeasure μ] (U : M → A → ℝ)
    (q : Setoid M) [DecidableRel q] (a : A) : ∫ m, U m a ∂μ = partitionEU μ U q a := by
  rw [partitionEU, (Finpartition.ofSetoid q).sum_parts_eq_sum_preimage_part
    (F := fun c ↦ μ.real c * ∫ m, U m a ∂μ[|c]) (by simp), sum_measureReal_mul_integral_cond]

/-- Expected utility computed through a partition does not depend on the partition. -/
theorem partitionEU_congr (μ : Measure M) [IsProbabilityMeasure μ] (U : M → A → ℝ)
    (q q' : Setoid M) [DecidableRel q] [DecidableRel q'] (a : A) :
    partitionEU μ U q a = partitionEU μ U q' a :=
  (integral_eq_partitionEU μ U q a).symm.trans (integral_eq_partitionEU μ U q' a)

end ExpectedUtility

end Merin1999b
