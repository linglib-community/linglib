module

public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Pragmatics.NeoGricean.Basic
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Optimal assertions and priors

Under a prior on the worlds, the more informative of two propositions is the less probable one,
the one of greater surprisal. An assertion a speaker is certain of is [the least probable
alternative she is certain of under every prior](##NeoGricean.forall_subset_iff_forall_measure_le)
exactly when it entails all the others. The assertion is optimal, in that no stronger alternative
is one she is certain of, exactly when it is [the least probable under some prior that gives every
world positive probability](##NeoGricean.isOptimal_iff_exists_measure), over finitely many worlds.
The two agree when the alternatives are closed under intersection: asserting an alternative is
then optimal exactly when it is [the least probable alternative the speaker is certain of whatever
the prior](##NeoGricean.isOptimal_iff_forall_measure).

## Implementation notes

A prior is a measure, with no normalization: the comparisons do not depend on the total mass. The
prior of the existence statement is finite and positive at every world.

## References

* [spector-2007]
* [sauerland-2004]
-/

@[expose] public section

namespace NeoGricean

open MeasureTheory Set

variable {W : Type*} [MeasurableSpace W] {alts : Set (Set W)} {φ s : Set W}

/-- The assertion entails every alternative the speaker is certain of exactly when it is at most
as probable as each of them under every prior. -/
theorem forall_subset_iff_forall_measure_le [MeasurableSingletonClass W] :
    (∀ ψ ∈ alts, s ⊆ ψ → φ ⊆ ψ) ↔ ∀ μ : Measure W, ∀ ψ ∈ alts, s ⊆ ψ → μ φ ≤ μ ψ :=
  ⟨fun h _ ψ hψ hsψ ↦ measure_mono (h ψ hψ hsψ),
    fun h ψ hψ hsψ ↦ subset_iff_forall_measure_le.2 fun μ ↦ h μ ψ hψ hsψ⟩

/-- With the alternatives closed under intersection, asserting an alternative the speaker is
certain of is optimal exactly when it is at most as probable as every alternative she is certain
of, whatever the prior. -/
theorem isOptimal_iff_forall_measure [MeasurableSingletonClass W] (hinf : InfClosed alts)
    (hφ : φ ∈ alts) (hs : s ⊆ φ) :
    IsOptimal alts φ s ↔ ∀ μ : Measure W, ∀ ψ ∈ alts, s ⊆ ψ → μ φ ≤ μ ψ := by
  rw [← forall_subset_iff_forall_measure_le]
  refine ⟨fun h ψ hψ hsψ ↦ by_contra fun hφψ ↦ ?_,
    fun h ↦ ⟨hs, fun ψ hψ hsψ hlt ↦ hlt.2 (h ψ hψ hsψ)⟩⟩
  exact h.not_ssubset (ψ ∩ φ) (hinf hψ hφ) (subset_inter hsψ hs)
    ⟨inter_subset_right, fun h' ↦ hφψ fun w hw ↦ (h' hw).1⟩

/-- Over finitely many worlds, asserting what the speaker is certain of is optimal exactly when it
is at most as probable as every alternative she is certain of under some prior that gives every
world positive probability. -/
theorem isOptimal_iff_exists_measure [Fintype W] [DiscreteMeasurableSpace W] (hs : s ⊆ φ) :
    IsOptimal alts φ s ↔ ∃ μ : Measure W, IsFiniteMeasure μ ∧ (∀ w, μ {w} ≠ 0) ∧
      ∀ ψ ∈ alts, s ⊆ ψ → μ φ ≤ μ ψ := by
  constructor
  · intro h
    refine ⟨(Measure.count + (Fintype.card W : NNReal) • Measure.count.restrict φᶜ : Measure W),
      inferInstance, fun w ↦ by simp, fun ψ hψ hsψ ↦ ?_⟩
    by_cases hφψ : φ ⊆ ψ
    · exact measure_mono hφψ
    · obtain ⟨w, hwψ, hwφ⟩ := not_subset.1 fun hψφ ↦ h.not_ssubset ψ hψ hsψ ⟨hψφ, hφψ⟩
      have hK : Measure.count φ ≤ (Fintype.card W : ENNReal) :=
        (measure_mono (subset_univ φ)).trans (by simp)
      have h1 : (1 : ENNReal) ≤ Measure.count (ψ ∩ φᶜ) :=
        (by simp : (1 : ENNReal) = Measure.count ({w} : Set W)).trans_le
          (measure_mono (singleton_subset_iff.2 ⟨hwψ, hwφ⟩))
      simp only [Measure.add_apply, Measure.smul_apply,
        Measure.restrict_apply MeasurableSet.of_discrete, inter_compl_self, measure_empty,
        ENNReal.smul_def, smul_eq_mul, ENNReal.coe_natCast, mul_zero, add_zero]
      calc Measure.count φ ≤ (Fintype.card W : ENNReal) * 1 := by simpa using hK
        _ ≤ (Fintype.card W : ENNReal) * Measure.count (ψ ∩ φᶜ) := by gcongr
        _ ≤ _ := le_add_self
  · rintro ⟨μ, _, hpos, hμ⟩
    refine ⟨hs, fun ψ hψ hsψ hlt ↦ ?_⟩
    obtain ⟨w, hwφ, hwψ⟩ := exists_of_ssubset hlt
    have h1 : μ ψ + μ {w} ≤ μ φ := by
      rw [← measure_union (disjoint_singleton_right.2 hwψ) (measurableSet_singleton w)]
      exact measure_mono (union_subset hlt.subset (singleton_subset_iff.2 hwφ))
    have h2 : μ ψ + μ {w} ≤ μ ψ + 0 := by simpa using h1.trans (hμ ψ hψ hsψ)
    exact hpos w (le_antisymm ((ENNReal.add_le_add_iff_left (measure_ne_top μ ψ)).1 h2) zero_le)

end NeoGricean
