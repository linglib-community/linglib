module

public import Linglib.Core.InformationTheory.KullbackLeibler.Cond
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Pragmatics.Implicature.OptimalAssertion
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Optimal assertions and priors

Under a prior on the worlds, the more informative of two propositions is the less probable one,
the one of greater surprisal. An assertion a speaker is certain of is [the least probable
alternative she is certain of under every prior](##Implicature.forall_subset_iff_forall_measure_le)
exactly when it entails all the others. The assertion is optimal, in that no stronger alternative
is one she is certain of, exactly when it is [the least probable under some prior that gives every
world positive probability](##Implicature.isOptimalAssertion_iff_exists_measure), over finitely
many worlds.
The two agree when the alternatives are closed under intersection: asserting an alternative is
then optimal exactly when it is [the least probable alternative the speaker is certain of whatever
the prior](##Implicature.isOptimalAssertion_iff_forall_measure).

The divergence of the speaker's beliefs, the prior conditioned on her state, from the literal
reading of a proposition, the prior conditioned on it, is finite [exactly when she is certain of
the proposition](##Implicature.klDiv_cond_cond_ne_top_iff), and among the propositions she is
certain of it is [least for the least probable](##Implicature.klDiv_cond_cond_le_iff). So Quality
is finiteness of the divergence and Quantity its size, and under closure by intersection an
assertion is optimal exactly when it [minimizes the divergence among the alternatives under every
prior](##Implicature.isOptimalAssertion_iff_forall_klDiv) that gives every world positive
probability. On the hearer's side, closure under unions as well makes the minimal worlds of the
assertion [at most as probable as any state in which it is
optimal](##Implicature.IsOptimalAssertion.measure_exhMW_le).

## Implementation notes

A prior is a measure, with no normalization: the comparisons do not depend on the total mass. The
prior of the existence statement is finite and positive at every world, as are the priors of the
statements about divergence, which are over finitely many worlds.

## References

* [grice-1975]
* [spector-2007]
* [benz-vanrooij-2007]
-/

@[expose] public section

namespace Implicature

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
theorem isOptimalAssertion_iff_forall_measure [MeasurableSingletonClass W] (hinf : InfClosed alts)
    (hφ : φ ∈ alts) (hs : s ⊆ φ) :
    IsOptimalAssertion alts φ s ↔ ∀ μ : Measure W, ∀ ψ ∈ alts, s ⊆ ψ → μ φ ≤ μ ψ := by
  rw [← forall_subset_iff_forall_measure_le]
  refine ⟨fun h ψ hψ hsψ ↦ by_contra fun hφψ ↦ ?_,
    fun h ↦ ⟨hs, fun ψ hψ hsψ hlt ↦ hlt.2 (h ψ hψ hsψ)⟩⟩
  exact h.not_ssubset (ψ ∩ φ) (hinf hψ hφ) (subset_inter hsψ hs)
    ⟨inter_subset_right, fun h' ↦ hφψ fun w hw ↦ (h' hw).1⟩

/-- Over finitely many worlds, asserting what the speaker is certain of is optimal exactly when it
is at most as probable as every alternative she is certain of under some prior that gives every
world positive probability. -/
theorem isOptimalAssertion_iff_exists_measure [Fintype W] [DiscreteMeasurableSpace W] (hs : s ⊆ φ) :
    IsOptimalAssertion alts φ s ↔ ∃ μ : Measure W, IsFiniteMeasure μ ∧ (∀ w, μ {w} ≠ 0) ∧
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

/-- With the alternatives closed under intersection and nonempty unions, the minimal worlds of the
assertion are at most as probable, whatever the prior, as any consistent state in which the
assertion is optimal, taken up to the worlds the alternatives do not tell apart: the hearer who
takes the speaker to be as informed as her assertion allows takes her to be in that state. -/
theorem IsOptimalAssertion.measure_exhMW_le (hinf : InfClosed alts)
    (hsup : ∀ A ⊆ alts, A.Nonempty → ⋃₀ A ∈ alts) (hφ : φ ∈ alts) (hne : s.Nonempty)
    (hs : IsOptimalAssertion alts φ s) (μ : Measure W) :
    μ (Exhaustification.exhMW alts φ) ≤
      μ (Preorder.satisfied (· ∈ ·) alts ⁻¹' (Preorder.satisfied (· ∈ ·) alts '' s)) :=
  measure_mono fun _ hu ↦ hs.exists_satisfied_eq hinf hsup hφ hne hu

/-! ### Divergence from the literal reading -/

section KullbackLeibler

open InformationTheory ProbabilityTheory

variable {μ : Measure W} {t t' : Set W}

private theorem ae_le_iff_subset (hμ : ∀ w, μ {w} ≠ 0) : s ≤ᵐ[μ] t ↔ s ⊆ t :=
  ⟨fun h w hw ↦ by_contra fun hwt ↦ hμ w (measure_mono_null
      (singleton_subset_iff.2 (show w ∈ s \ t from ⟨hw, hwt⟩)) (ae_le_set.1 h)),
    fun h ↦ ae_le_set.2 (by rw [sdiff_eq_empty.2 h, measure_empty])⟩

private theorem measure_ne_zero_of_nonempty (hμ : ∀ w, μ {w} ≠ 0) (hne : s.Nonempty) : μ s ≠ 0 :=
  let ⟨w, hw⟩ := hne
  fun h ↦ hμ w (measure_mono_null (singleton_subset_iff.2 hw) h)

variable [DiscreteMeasurableSpace W] [IsFiniteMeasure μ]

/-- Under a prior that gives every world positive probability, the speaker's beliefs are at a
finite divergence from the literal reading of a proposition exactly when she is certain of it. -/
theorem klDiv_cond_cond_ne_top_iff (hμ : ∀ w, μ {w} ≠ 0) : klDiv μ[|s] μ[|t] ≠ ⊤ ↔ s ⊆ t := by
  rw [Ne, klDiv_cond_cond_eq_top_iff .of_discrete .of_discrete, not_not, ae_le_iff_subset hμ]

/-- Of two propositions a consistent speaker is certain of, her beliefs are closer to the literal
reading of the less probable one. -/
theorem klDiv_cond_cond_le_iff (hμ : ∀ w, μ {w} ≠ 0) (hne : s.Nonempty) (hst : s ⊆ t)
    (hst' : s ⊆ t') : klDiv μ[|s] μ[|t] ≤ klDiv μ[|s] μ[|t'] ↔ μ t ≤ μ t' := by
  have hs0 := measure_ne_zero_of_nonempty hμ hne
  have hspos : 0 < μ.real s := ENNReal.toReal_pos hs0 (measure_ne_top μ s)
  have hpos : ∀ {r : Set W}, s ⊆ r → 0 < μ.real r := fun h ↦ hspos.trans_le (measureReal_mono h)
  rw [klDiv_cond_cond .of_discrete .of_discrete hs0 ((ae_le_iff_subset hμ).2 hst),
    klDiv_cond_cond .of_discrete .of_discrete hs0 ((ae_le_iff_subset hμ).2 hst'),
    ENNReal.ofReal_le_ofReal_iff (Real.log_nonneg ((one_le_div hspos).2 (measureReal_mono hst'))),
    Real.log_le_log_iff (div_pos (hpos hst) hspos) (div_pos (hpos hst') hspos),
    div_le_div_iff_of_pos_right hspos, measureReal_def, measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top μ t) (measure_ne_top μ t')]

omit [IsFiniteMeasure μ] in
/-- With the alternatives closed under intersection, asserting an alternative is optimal for a
consistent speaker exactly when, under every prior that gives every world positive probability,
her beliefs are at a finite divergence from its literal reading, and at no greater a divergence
than from the literal reading of any alternative. -/
theorem isOptimalAssertion_iff_forall_klDiv [Fintype W] (hinf : InfClosed alts) (hφ : φ ∈ alts)
    (hne : s.Nonempty) :
    IsOptimalAssertion alts φ s ↔ ∀ μ : Measure W, IsFiniteMeasure μ → (∀ w, μ {w} ≠ 0) →
      klDiv μ[|s] μ[|φ] ≠ ⊤ ∧ ∀ ψ ∈ alts, klDiv μ[|s] μ[|φ] ≤ klDiv μ[|s] μ[|ψ] := by
  constructor
  · intro h μ _ hμ
    refine ⟨(klDiv_cond_cond_ne_top_iff hμ).2 h.admissible, fun ψ hψ ↦ ?_⟩
    by_cases hsψ : s ⊆ ψ
    · exact (klDiv_cond_cond_le_iff hμ hne h.admissible hsψ).2
        ((isOptimalAssertion_iff_forall_measure hinf hφ h.admissible).1 h μ ψ hψ hsψ)
    · exact le_of_le_of_eq le_top (not_not.1 (mt (klDiv_cond_cond_ne_top_iff hμ).1 hsψ)).symm
  · intro h
    have hc : ∀ w : W, (Measure.count : Measure W) {w} ≠ 0 := fun w ↦ by simp
    obtain ⟨hfin, hle⟩ := h Measure.count inferInstance hc
    have hs := (klDiv_cond_cond_ne_top_iff hc).1 hfin
    refine ⟨hs, fun ψ hψ hsψ hlt ↦ ?_⟩
    obtain ⟨w, hwφ, hwψ⟩ := exists_of_ssubset hlt
    have h1 : Measure.count ψ + Measure.count ({w} : Set W) ≤ Measure.count φ := by
      rw [← measure_union (disjoint_singleton_right.2 hwψ) (measurableSet_singleton w)]
      exact measure_mono (union_subset hlt.subset (singleton_subset_iff.2 hwφ))
    have h2 : Measure.count ψ + Measure.count ({w} : Set W) ≤ Measure.count ψ + 0 := by
      simpa using h1.trans ((klDiv_cond_cond_le_iff hc hne hs hsψ).1 (hle ψ hψ))
    exact hc w (le_antisymm
      ((ENNReal.add_le_add_iff_left (measure_ne_top Measure.count ψ)).1 h2) zero_le)

end KullbackLeibler

end Implicature
