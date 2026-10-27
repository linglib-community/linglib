module

public import Linglib.Phonology.HarmonicGrammar.Expressivity
public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Linglib.Data.Examples.GoldwaterJohnson2003

/-!
# Goldwater and Johnson (2003): Learning OT Constraint Rankings Using a Maximum Entropy Model

Goldwater and Johnson's maximum entropy model of constraint-based phonology gives an output of an
input the probability of eq. (1), the MaxEnt distribution `maxEnt` of the input's candidates.
Learning maximizes the log pseudo-likelihood of the training pairs (eq. (2)) less a Gaussian
penalty on the weights (eq. (3)). The log pseudo-likelihood is concave in the weights, as
footnote 4 says, and the penalty makes the objective strictly concave, so at most one weighting
maximizes it. Replicating the corpus r times while dividing the prior's variance by r rescales the
objective by r, so only nσ² matters for the weights learned.

The learned weights of the Wolof tongue-root grammar (Table 1) are exponentially separated, the
spacing that recovers strict domination in Johnson's limit. For Boersma and Hayes's Finnish
genitive plurals, a model choosing between two candidates sees their violations only through the
difference vector, so Table 2's *naapuri* and *ministeri* classes, distinct in violations but not
in differences, are one class for the learner.

## Implementation notes

Footnote 4 infers a single global maximum from concavity of the log conditional likelihood, but a
concave function can be maximized on a whole convex set, as when two constraints are violated
alike; uniqueness comes from the strictly convex penalty of (3).

The four Finnish rows carry Table 2's violation vectors as digit strings, one digit per constraint
in Boersma and Hayes's order; Anttila's full grammar is in `Studies/Anttila1997.lean`. The Wolof
weights are the learned values of Table 1; the error rates and Table 4 stay in the paper, as does
the comparison with Boersma's Gradual Learning Algorithm.

## References

* [goldwater-johnson-2003]
* [boersma-hayes-2001]
* [boersma-1997]
* [berger-della-pietra-della-pietra-1996]
* [johnson-2002]
* [smolensky-legendre-2006]
-/

@[expose] public section

namespace GoldwaterJohnson2003

open OptimalityTheory HarmonicGrammar MeasureTheory ProbabilityTheory InformationTheory Finset Real
open scoped ENNReal

variable {I O : Type*} [MeasurableSpace O] {n : ℕ}

/-- The log pseudo-likelihood of the training pairs, eq. (2) logged, sums the log-probabilities
of the observed outputs under the MaxEnt distributions (1) of their inputs' candidates. -/
noncomputable def logPseudoLikelihood (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) : ℝ :=
  (data.map fun p ↦ log ((maxEnt (con.comap (p.1, ·)).violations w).real {p.2})).sum

/-- Eq. (3) with the paper's common prior, mean zero and deviation σ for every weight. -/
noncomputable def regularizedObjective (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) (σ : ℝ) : ℝ :=
  logPseudoLikelihood con w data - ∑ j, w j ^ 2 / (2 * σ ^ 2)

/-- Replicating the corpus r times while dividing the prior's variance by r multiplies the
objective by r: the weights learned depend on nσ² alone. -/
theorem regularizedObjective_replicate (con : ConstraintSet (I × O) (Fin n)) (w : Fin n → ℝ)
    (data : List (I × O)) {r : ℕ} (hr : 0 < r) {σ σ' : ℝ} (hσ : 0 < σ)
    (h : (r : ℝ) * σ' ^ 2 = σ ^ 2) :
    regularizedObjective con w (List.replicate r data).flatten σ' =
      r * regularizedObjective con w data σ := by
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hσ' : σ' ^ 2 = σ ^ 2 / r := by rw [← h]; field_simp
  unfold regularizedObjective logPseudoLikelihood
  simp only [List.map_flatten, List.map_replicate, List.sum_flatten, List.sum_replicate,
    nsmul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hσ']
  field_simp

theorem regularizedObjective_replicate_le_iff (con : ConstraintSet (I × O) (Fin n))
    (w w' : Fin n → ℝ) (data : List (I × O)) {r : ℕ} (hr : 0 < r) {σ σ' : ℝ} (hσ : 0 < σ)
    (h : (r : ℝ) * σ' ^ 2 = σ ^ 2) :
    regularizedObjective con w' (List.replicate r data).flatten σ' ≤
        regularizedObjective con w (List.replicate r data).flatten σ' ↔
      regularizedObjective con w' data σ ≤ regularizedObjective con w data σ := by
  rw [regularizedObjective_replicate con w data hr hσ h,
    regularizedObjective_replicate con w' data hr hσ h]
  exact mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hr)

section Empirical

variable [MeasurableSpace I] (data : List (I × O))

/-- The empirical distribution of the training pairs. -/
noncomputable def empirical : Measure (I × O) :=
  (data.length : ℝ≥0∞)⁻¹ • ∑ i : Fin data.length, Measure.dirac data[i]

theorem isProbabilityMeasure_empirical (h : data ≠ []) : IsProbabilityMeasure (empirical data) :=
  ⟨by
    simp only [empirical, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simpa using h) (ENNReal.natCast_ne_top _)⟩

end Empirical

variable [Fintype O] [MeasurableSingletonClass O]

/-- The log pseudo-likelihood is concave in the weights (footnote 4), as a sum of the
log-likelihoods of single observations. -/
theorem concaveOn_logPseudoLikelihood (con : ConstraintSet (I × O) (Fin n)) (data : List (I × O)) :
    ConcaveOn ℝ Set.univ fun w ↦ logPseudoLikelihood con w data := by
  induction data with
  | nil => simpa [logPseudoLikelihood] using concaveOn_const (0 : ℝ) convex_univ
  | cons p data ih =>
    have : Nonempty O := ⟨p.2⟩
    simp only [logPseudoLikelihood, List.map_cons, List.sum_cons] at ih ⊢
    exact ((concaveOn_logLikelihood (con.comap (p.1, ·)).violations (Measure.dirac p.2)).congr
      fun w _ ↦ logLikelihood_dirac _ _ _).add ih

private theorem strictConvexOn_sum_sq_div {σ : ℝ} (hσ : σ ≠ 0) :
    StrictConvexOn ℝ Set.univ fun w : Fin n → ℝ ↦ ∑ j, w j ^ 2 / (2 * σ ^ 2) := by
  have hc : 0 < 2 * σ ^ 2 := by positivity
  have hsq := Even.strictConvexOn_pow (n := 2) even_two two_ne_zero
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab ↦ ?_⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hxy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_lt_sum (fun k _ ↦ ?_) ⟨j, mem_univ _, ?_⟩
  · have := hsq.convexOn.2 (Set.mem_univ (x k)) (Set.mem_univ (y k)) ha.le hb.le hab
    simp only [smul_eq_mul] at this
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right hc]
    exact this
  · have := hsq.2 (Set.mem_univ (x j)) (Set.mem_univ (y j)) hj ha hb hab
    simp only [smul_eq_mul] at this
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_lt_div_iff_of_pos_right hc]
    exact this

-- (3)
theorem strictConcaveOn_regularizedObjective (con : ConstraintSet (I × O) (Fin n))
    (data : List (I × O)) {σ : ℝ} (hσ : σ ≠ 0) :
    StrictConcaveOn ℝ Set.univ fun w ↦ regularizedObjective con w data σ :=
  (concaveOn_logPseudoLikelihood con data).sub_strictConvexOn (strictConvexOn_sum_sq_div hσ)

/-- At most one weighting maximizes the objective (3), footnote 4's single global maximum. -/
theorem eq_of_isMaxOn_regularizedObjective (con : ConstraintSet (I × O) (Fin n))
    (data : List (I × O)) {σ : ℝ} (hσ : σ ≠ 0) {w w' : Fin n → ℝ}
    (hw : IsMaxOn (fun w ↦ regularizedObjective con w data σ) Set.univ w)
    (hw' : IsMaxOn (fun w ↦ regularizedObjective con w data σ) Set.univ w') : w = w' :=
  (strictConcaveOn_regularizedObjective con data hσ).eq_of_isMaxOn hw hw' trivial trivial

/-! ### Maximum entropy (section 2) -/

section MaximumEntropy

variable [MeasurableSpace I] [Fintype I] [MeasurableSingletonClass I]
  (con : ConstraintSet (I × O) (Fin n)) (data : List (I × O))

-- (2)
theorem logPseudoLikelihood_eq (h : data ≠ []) (w : Fin n → ℝ) :
    logPseudoLikelihood con w data =
      data.length * condLogLikelihood con.violations (empirical data) w := by
  have hlen : (data.length : ℝ) ≠ 0 := by simpa using h
  rw [condLogLikelihood, empirical, integral_smul_measure,
    integral_finsetSum_measure fun _ _ ↦ .of_finite]
  simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← mul_assoc,
    mul_inv_cancel₀ hlen, one_mul]
  rw [logPseudoLikelihood, ← Fin.sum_univ_fun_getElem]
  rfl

/-- Maximum entropy models "have as high an entropy as possible under the constraint that they
match the training data" (section 2). Weights maximizing the log pseudo-likelihood give the
grammar of greatest conditional entropy among the conditional models whose violations, averaged
over the training inputs, are the training data's. -/
theorem isGreatest_condEntropy_of_isMaxOn_logPseudoLikelihood (h : data ≠ []) {w : Fin n → ℝ}
    (hw : IsMaxOn (fun w ↦ logPseudoLikelihood con w data) Set.univ w) :
    IsGreatest ((fun q : Kernel I O ↦ H[Prod.snd | Prod.fst ; (empirical data).fst ⊗ₘ q]) ''
      {q | IsMarkovKernel q ∧ ∫ z, (con.violations z : Fin n → ℝ) ∂((empirical data).fst ⊗ₘ q) =
        ∫ z, con.violations z ∂empirical data})
      (H[Prod.snd | Prod.fst ; (empirical data).fst ⊗ₘ condMaxEnt con.violations w]) := by
  have := isProbabilityMeasure_empirical data h
  have : Nonempty O := ⟨(data.head h).2⟩
  have hlen : (0 : ℝ) < data.length := by exact_mod_cast List.length_pos_of_ne_nil h
  refine isGreatest_condEntropy_of_isMaxOn _ w _ (isMaxOn_iff.2 fun w' _ ↦ ?_)
  have hw' : logPseudoLikelihood con w' data ≤ logPseudoLikelihood con w data :=
    hw (Set.mem_univ w')
  rw [logPseudoLikelihood_eq con data h, logPseudoLikelihood_eq con data h] at hw'
  exact le_of_mul_le_mul_left hw' hlen

end MaximumEntropy

/-! ### Two candidates: learning from differences (section 3.2) -/

/-- Two candidates as a constraint set, the winner at 0 and the loser at 1. -/
def pairConstraintSet (win lose : Fin n → ℕ) : ConstraintSet (Fin 2) (Fin n) :=
  fun j c ↦ if c = 0 then win j else lose j

/-- A two-candidate model sees the violations only through their difference, the winner's
probability being the sigmoid of the weighted difference vector. -/
theorem maxEnt_pairConstraintSet_real_zero (w : Fin n → ℝ) (win lose : Fin n → ℕ) :
    (maxEnt (pairConstraintSet win lose).violations w).real {0} =
      sigmoid (∑ j, w j * ((lose j : ℝ) - win j)) := by
  rw [maxEnt_real_singleton, harmony_violations, softmax_fin_two]
  congr 1
  simp only [harmonyScore_eq_neg_sum, pairConstraintSet, Fin.isValue, ite_true, ite_false,
    one_ne_zero, mul_sub, Finset.sum_sub_distrib]
  ring

theorem maxEnt_pairConstraintSet_real_zero_eq_of_diff_eq (w : Fin n → ℝ)
    {win lose win' lose' : Fin n → ℕ}
    (h : (fun j ↦ (lose j : ℤ) - win j) = fun j ↦ (lose' j : ℤ) - win' j) :
    (maxEnt (pairConstraintSet win lose).violations w).real {0} =
      (maxEnt (pairConstraintSet win' lose').violations w).real {0} := by
  rw [maxEnt_pairConstraintSet_real_zero, maxEnt_pairConstraintSet_real_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj := congrFun h j
  have : ((lose j : ℝ) - win j) = (((lose j : ℤ) - win j : ℤ) : ℝ) := by push_cast; ring
  rw [this, hj]
  push_cast
  ring

/-! ### Table 1: the Wolof tongue-root grammar -/

/-- The weights learned for Boersma's five Wolof constraints *RTRHI, PARSE[RTR],
GESTURE[CONTOUR], PARSE[ATR] and *ATRLO (Table 1, nσ² ≈ 1,200,000). -/
noncomputable def wolofWeights : Fin 5 → ℝ
  | 0 => 3389 / 100
  | 1 => 17
  | 2 => 10
  | 3 => 353 / 100
  | 4 => 41 / 100

/-- The learned weights are exponentially separated, each exceeding the sum of all lower ones, the
spacing under which Harmonic Grammar reproduces the strict domination of the ranking the Gradual
Learning Algorithm finds ([johnson-2002], `Pi.strictMonoOn_sum_mul`) (Table 1). -/
theorem wolof_separated : ExponentiallySeparated wolofWeights 1 := fun k ↦ by
  rw [← Finset.filter_lt_eq_Ioi]
  fin_cases k <;>
    simp +decide only [wolofWeights, Finset.sum_filter, Fin.sum_univ_five] <;>
    norm_num

/-! ### Tables 2 and 3: Finnish genitive plurals -/

/-- The digits of a feature string as violation counts, one per constraint. -/
def digits (s : String) : List ℕ := s.toList.map fun c ↦ c.toNat - '0'.toNat

/-- A violation vector over [boersma-hayes-2001]'s eleven constraints. -/
def vec (l : List ℕ) : Fin 11 → ℕ := fun j ↦ l.getD j 0

/-- A stem class, given by the violation vectors of the winning and the losing genitive plural. -/
structure Row where
  winner : Fin 11 → ℕ
  loser : Fin 11 → ℕ
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let w ← ex.feature? "winnerViolations"
  let l ← ex.feature? "loserViolations"
  pure ⟨vec (digits w), vec (digits l)⟩

/-- Table 3's learning signal, the loser's violations minus the winner's. -/
def Row.diff (r : Row) : Fin 11 → ℤ := fun j ↦ (r.loser j : ℤ) - r.winner j

/-- The four stem classes of Table 2. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = Examples.all.length := by decide

/-- Two of Table 2's classes differ in their violation vectors but not in their differences (Table
3). -/
theorem rows_collapse : ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁.winner ≠ r₂.winner ∧ r₁.diff = r₂.diff := by
  decide

theorem rows_collapse_prob :
    ∃ r₁ ∈ rows, ∃ r₂ ∈ rows, r₁ ≠ r₂ ∧
      ∀ w, (maxEnt (pairConstraintSet r₁.winner r₁.loser).violations w).real {0} =
        (maxEnt (pairConstraintSet r₂.winner r₂.loser).violations w).real {0} := by
  obtain ⟨r₁, h₁, r₂, h₂, hne, hd⟩ := rows_collapse
  exact ⟨r₁, h₁, r₂, h₂, fun h ↦ hne (congrArg Row.winner h),
    fun w ↦ maxEnt_pairConstraintSet_real_zero_eq_of_diff_eq w hd⟩

end GoldwaterJohnson2003
