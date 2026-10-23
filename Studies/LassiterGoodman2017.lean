module

public import Linglib.Pragmatics.RSA.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Lassiter and Goodman (2017): Adjectival Vagueness in a Bayesian Model of Interpretation

This file formalizes Lassiter and Goodman's free-variable Rational Speech Act model on the
RSA kernel pipeline. A positive-form gradable adjective compares a degree with a threshold
the semantics leaves open (`sem`); the pragmatic listener resolves the threshold jointly with
the state, threading each candidate assignment through a threshold-indexed literal listener and
speaker (`L0`, `S1`) and inverting the family against the product of the degree prior and the
threshold prior (`L1`). The threshold marginal of that posterior gives the metalinguistic
probability that an individual counts as tall, the posterior mass of thresholds below the
individual's height (`metalinguistic`), and borderline cases are those of intermediate
metalinguistic probability.

The sorites dissolves as in Edgington. Read materially, the inductive premises fail exactly
when the threshold falls in the gap between adjacent members, and the gap masses sum to the
mass of the whole range (`sum_gapMass`), so each can be small while their sum is near one;
Adams's theorem bounds the uncertainty of the conclusion of a valid argument by the summed
uncertainty of its premises (`adams`), and the sorites is valid (`sorites_uncertainty`).
Read by Adams's Thesis, each premise is a conditional probability of the threshold marginal
and is at most the material premise (`conditionalPremise_le`).

## Implementation notes

Degrees form a finite linear order so that the discrete pipeline applies; the paper's
continuous scale and normal prior enter only through its simulations, which are not stated.
The assignment of the paper's eq. 27 is the pair of thresholds for the adjective and its
antonym, and the threshold prior is a parameter rather than the paper's uniform prior, which
the model never uses beyond its being a prior.

## TODO

The free-variable reading of the inductive premise (the paper's eq. 44), the antonym symmetry
of the simulations, and the scalar-implicature warm-up of §3 are not stated.

## References

* [D. Lassiter and N. D. Goodman, *Adjectival Vagueness in a Bayesian Model of Interpretation*
  (2017)][lassiter-goodman-2017]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace LassiterGoodman2017

/-- The utterances are the adjective, its antonym, and saying nothing. -/
inductive Utterance
  | tall | short | silent
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ ↦ trivial⟩
instance : Nonempty Utterance := ⟨.silent⟩

variable {D : Type*} [LinearOrder D]

theorem sorites_valid (x : ℕ → D) (n : ℕ) {θ : D} (hθ : θ < x n)
    (hgap : ∀ i ∈ Finset.range n, θ ∉ Set.Ico (x i) (x (i + 1))) : θ < x 0 := by
  induction n with
  | zero => exact hθ
  | succ n ih =>
    exact ih (lt_of_not_ge fun h ↦ hgap n (Finset.mem_range.mpr n.lt_succ_self) ⟨h, hθ⟩)
      fun i hi ↦ hgap i (Finset.range_mono n.le_succ hi)

variable [MeasurableSpace D] [DiscreteMeasurableSpace D]

/-- The meaning of an utterance at a degree under an assignment of thresholds to the adjective
and its antonym (eqs. 22–23). *Tall* holds above the first threshold, *short* below the second,
and silence everywhere. -/
def sem (θ : D × D) : Utterance → Set D
  | .tall => Set.Ioi θ.1
  | .short => Set.Iio θ.2
  | .silent => Set.univ

/-- The literal listener at an assignment (eq. 27) is the degree prior conditioned on the truth of
the utterance. -/
noncomputable def L0 (μ : Measure D) (θ : D × D) : Kernel Utterance D :=
  listener μ (truthful fun u ↦ sem θ u)

theorem L0_apply_singleton_ne_zero_iff (μ : Measure D) [IsFiniteMeasure μ] (θ : D × D)
    (u : Utterance) (d : D) : L0 μ θ u {d} ≠ 0 ↔ d ∈ sem θ u ∧ μ {d} ≠ 0 :=
  listener_truthful_apply_singleton_ne_zero_iff μ (sem θ) u d

section Model

variable [Fintype D]

/-- The speaker at a degree and an assignment (eq. 28) addresses the literal listener at the
assignment, at rationality `α` with costs `cost`. -/
noncomputable def S1 (μ : Measure D) (α : ℝ) (cost : Utterance → ℝ) (p : D × (D × D)) :
    Measure Utterance :=
  speaker α cost (L0 μ p.2) Measure.dirac p.1

instance (μ : Measure D) (α : ℝ) (cost : Utterance → ℝ) (p : D × (D × D)) :
    IsFiniteMeasure (S1 μ α cost p) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

/-- The pragmatic listener (eq. 29) inverts the speaker against the product of the degree prior
and the threshold prior. Its first marginal is the degree posterior (eq. 31), its second the
posterior over assignments (eq. 30). -/
noncomputable def L1 (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure (D × D)) [IsProbabilityMeasure ν] (α : ℝ) (cost : Utterance → ℝ) :
    Kernel Utterance (D × (D × D)) :=
  listener (μ.prod ν) (S1 μ α cost)

variable (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure (D × D)) (α : ℝ)
  (cost : Utterance → ℝ)

theorem S1_apply_singleton_ne_zero_iff (hα : 0 < α) (d : D) (θ : D × D) (u : Utterance) :
    S1 μ α cost (d, θ) {u} ≠ 0 ↔ d ∈ sem θ u ∧ μ {d} ≠ 0 :=
  speaker_listener_truthful_dirac_apply_singleton_ne_zero_iff hα cost μ (sem θ) u d

variable [IsProbabilityMeasure ν]

theorem L1_apply_singleton_ne_zero_iff (hα : 0 < α) (u : Utterance) (d : D) (θ : D × D) :
    L1 μ ν α cost u {(d, θ)} ≠ 0 ↔ μ {d} ≠ 0 ∧ ν {θ} ≠ 0 ∧ d ∈ sem θ u := by
  rw [L1, listener_apply_singleton_ne_zero_iff, ← Set.singleton_prod_singleton,
    Measure.prod_prod, mul_ne_zero_iff, S1_apply_singleton_ne_zero_iff μ α cost hα d θ u]
  tauto

theorem isProbabilityMeasure_L1 (hα : 0 < α) {u : Utterance} {d : D} {θ : D × D}
    (hd : μ {d} ≠ 0) (hθ : ν {θ} ≠ 0) (hu : d ∈ sem θ u) :
    IsProbabilityMeasure (L1 μ ν α cost u) :=
  isProbabilityMeasure_listener_of_ne_zero _ _
    (by rw [← Set.singleton_prod_singleton, Measure.prod_prod]; exact mul_ne_zero hd hθ)
    ((S1_apply_singleton_ne_zero_iff μ α cost hα d θ u).mpr ⟨hu, hd⟩)

/-- The posterior over the adjective's threshold (eq. 30) is the marginal of the listener on the
first coordinate of the assignment. -/
noncomputable def thresholdPosterior (u : Utterance) : Measure D :=
  (L1 μ ν α cost u).snd.fst

theorem isProbabilityMeasure_thresholdPosterior (hα : 0 < α) {u : Utterance} {d : D} {θ : D × D}
    (hd : μ {d} ≠ 0) (hθ : ν {θ} ≠ 0) (hu : d ∈ sem θ u) :
    IsProbabilityMeasure (thresholdPosterior μ ν α cost u) := by
  have := isProbabilityMeasure_L1 μ ν α cost hα hd hθ hu
  unfold thresholdPosterior
  infer_instance

/-- The metalinguistic probability that a degree counts as tall under a threshold measure
(eq. 32) is the mass of thresholds below it. -/
noncomputable def metalinguistic (ρ : Measure D) (d : D) : ℝ≥0∞ := ρ (Set.Iio d)

theorem metalinguistic_thresholdPosterior (u : Utterance) (d : D) :
    metalinguistic (thresholdPosterior μ ν α cost u) d
      = L1 μ ν α cost u {p | p.2.1 < d} := by
  rw [metalinguistic, thresholdPosterior, Measure.fst_apply .of_discrete,
    Measure.snd_apply .of_discrete]
  rfl

/-- A borderline case is a degree of intermediate metalinguistic probability. -/
def Borderline (ρ : Measure D) (d : D) : Prop :=
  0 < metalinguistic ρ d ∧ metalinguistic ρ d < 1

end Model

/-! ### The sorites -/

section Sorites

variable (ρ : Measure D)

/-- The failure probability of a material inductive premise (eq. 37) is the probability that the
threshold falls between two adjacent members. -/
noncomputable def gapMass (a b : D) : ℝ≥0∞ := ρ (Set.Ico a b)

theorem sum_gapMass (x : ℕ → D) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n, gapMass ρ (x i) (x (i + 1)) = gapMass ρ (x 0) (x n) := by
  induction n with
  | zero => simp [gapMass]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, gapMass, gapMass, gapMass,
      ← measure_union Set.Ico_disjoint_Ico_same .of_discrete,
      Set.Ico_union_Ico_eq_Ico (hx (Nat.zero_le n)) (hx n.le_succ)]

theorem adams {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ s, MeasurableSet (A i)) {C : Set Ω}
    (hC : ⋂ i ∈ s, A i ⊆ C) : 1 - μ C ≤ ∑ i ∈ s, (1 - μ (A i)) := by
  calc 1 - μ C ≤ 1 - μ (⋂ i ∈ s, A i) := tsub_le_tsub_left (measure_mono hC) 1
    _ = μ (⋂ i ∈ s, A i)ᶜ := (prob_compl_eq_one_sub (.biInter s.countable_toSet hA)).symm
    _ = μ (⋃ i ∈ s, (A i)ᶜ) := by rw [Set.compl_iInter₂]
    _ ≤ ∑ i ∈ s, μ (A i)ᶜ := measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, (1 - μ (A i)) :=
      Finset.sum_congr rfl fun i hi ↦ prob_compl_eq_one_sub (hA i hi)

variable [IsProbabilityMeasure ρ]

theorem sorites_uncertainty (x : ℕ → D) (hx : Monotone x) (n : ℕ) :
    1 - metalinguistic ρ (x 0) ≤ (1 - metalinguistic ρ (x n)) + gapMass ρ (x 0) (x n) := by
  have h := adams ρ (Finset.range (n + 1))
    (fun i ↦ if i < n then (Set.Ico (x i) (x (i + 1)))ᶜ else Set.Iio (x n))
    (fun _ _ ↦ .of_discrete) (C := Set.Iio (x 0)) ?_
  · rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl n),
      Finset.sum_congr rfl (fun i hi ↦ by rw [ite_eq_left (Finset.mem_range.mp hi)]),
      add_comm] at h
    simp only [prob_compl_eq_one_sub (MeasurableSet.of_discrete),
      ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one] at h
    rwa [← sum_gapMass ρ x hx]
  · intro θ hθ
    rw [Set.mem_iInter₂] at hθ
    have htop := hθ n (Finset.mem_range.mpr n.lt_succ_self)
    rw [ite_eq_right (lt_irrefl n)] at htop
    exact sorites_valid x n htop fun i hi ↦ by
      have := hθ i (Finset.range_mono n.le_succ hi)
      rwa [ite_eq_left (Finset.mem_range.mp hi)] at this

/-- Under Adams's Thesis (eq. 40) an inductive premise is the conditional probability that
the lower member is tall given that the upper one is, which is at most the material premise,
the probability that the threshold avoids the gap. -/
theorem conditionalPremise_le {a b : D} (hab : a ≤ b) :
    ρ[Set.Iio a | Set.Iio b] ≤ ρ (Set.Ico a b)ᶜ := by
  rw [cond_apply .of_discrete, Set.Iio_inter_Iio, min_eq_right hab,
    prob_compl_eq_one_sub .of_discrete]
  have hsplit : ρ (Set.Iio b) = ρ (Set.Iio a) + ρ (Set.Ico a b) := by
    rw [← measure_union ((Set.Iio_disjoint_Ici le_rfl).mono_right Set.Ico_subset_Ici_self)
      .of_discrete, Set.Iio_union_Ico_eq_Iio hab]
  rcases eq_or_ne (ρ (Set.Iio b)) 0 with h0 | h0
  · rw [measure_mono_null (Set.Iio_subset_Iio hab) h0, mul_zero]
    exact zero_le
  rw [ENNReal.inv_mul_le_iff h0 (measure_ne_top _ _),
    ENNReal.mul_sub (fun _ _ ↦ measure_ne_top _ _), mul_one, hsplit]
  calc ρ (Set.Iio a) = ρ (Set.Iio a) + ρ (Set.Ico a b) - ρ (Set.Ico a b) :=
        (ENNReal.add_sub_cancel_right (measure_ne_top _ _)).symm
    _ ≤ ρ (Set.Iio a) + ρ (Set.Ico a b) - (ρ (Set.Iio a) + ρ (Set.Ico a b)) * ρ (Set.Ico a b) :=
        tsub_le_tsub_left (mul_le_of_le_one_left zero_le (hsplit ▸ prob_le_one)) _

end Sorites

end LassiterGoodman2017
