module

public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Instances.Matrix

/-!
# Error-driven learning

A learner holds a matrix `W` of association weights from cues to outcomes and meets learning
events, each a cue vector `x` paired with an outcome vector `y`. The weights predict the outcome
`x ᵥ* W`, and the error-driven update moves the weight from cue `i` to outcome `j` by the cue's
value times the outcome's prediction error, scaled by a rate `α i` for the cue and a rate `β j`
for the outcome. On indicator vectors this is the rule of Rescorla and Wagner, where `α` is the
salience of a cue and `β` the importance of an outcome. With a single rate it is the rule of
Widrow and Hoff for real-valued vectors.

The cues of an event share its prediction error. An event that the weights already predict
therefore changes nothing, and repeating an event shrinks its error geometrically while dividing
the weight gained among the cues in proportion to their rates.

## Main definitions

* `ErrorDrivenLearning.update`: the weights after one learning event.

## Main results

* `ErrorDrivenLearning.update_eq_self_iff`: an event leaves the weights fixed exactly when none
  of its cues is effective or none of its outcomes is mispredicted.
* `ErrorDrivenLearning.iterate_update`, `ErrorDrivenLearning.tendsto_iterate_update_apply`: the
  weights after `n` repetitions of an event, and their limit.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [R. A. Rescorla and A. R. Wagner, *A theory of Pavlovian conditioning*
  (1972)][rescorla-wagner-1972]
* [B. Widrow and M. Hoff, *Adaptive switching circuits* (1960)][widrow-hoff-1960]
-/

@[expose] public section

namespace ErrorDrivenLearning

open Matrix Filter Finset
open scoped Topology

variable {ι κ : Type*} [Fintype ι] (α : ι → ℝ) (β : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ)
  (W : Matrix ι κ ℝ)

/-- The **error-driven update** of the weights `W` on a learning event with cues `x` and outcomes
`y` adds `α i * x i * ((y j - (x ᵥ* W) j) * β j)` to the weight from cue `i` to outcome `j`, the
cue's rate and value times the outcome's prediction error and rate. -/
noncomputable def update : Matrix ι κ ℝ :=
  W + vecMulVec (α * x) ((y - x ᵥ* W) * β)

theorem update_apply (i : ι) (j : κ) :
    update α β x y W i j = W i j + α i * x i * ((y j - (x ᵥ* W) j) * β j) := rfl

theorem update_smul_one (η : ℝ) :
    update (η • 1) 1 x y W = W + η • vecMulVec x (y - x ᵥ* W) := by
  rw [update, smul_mul_assoc, one_mul, mul_one, smul_vecMulVec]

theorem update_smul_one_smul_one (a b : ℝ) :
    update (a • 1) (b • 1) x y W = update ((a * b) • 1) 1 x y W := by
  rw [update_smul_one, update, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_vecMulVec,
    vecMulVec_smul, smul_smul]

theorem update_indicator_apply (s : Finset ι) (t : Set κ) (lam : κ → ℝ) (i : ι) (j : κ) :
    update α β ((s : Set ι).indicator 1) (t.indicator lam) W i j =
      W i j + (s : Set ι).indicator α i * β j * (t.indicator lam j - ∑ i' ∈ s, W i' j) := by
  classical
  by_cases hi : i ∈ s <;>
    simp [update_apply, vecMul, dotProduct, Set.indicator_apply, Finset.sum_ite_mem, hi]
  ring

/-! ### One event -/

theorem vecMul_update (x' : ι → ℝ) :
    x' ᵥ* update α β x y W = x' ᵥ* W + (x' ⬝ᵥ (α * x)) • ((y - x ᵥ* W) * β) := by
  rw [update, vecMul_add, vecMul_vecMulVec]

theorem sub_vecMul_update :
    y - x ᵥ* update α β x y W = (y - x ᵥ* W) * (1 - (x ⬝ᵥ (α * x)) • β) := by
  rw [vecMul_update, mul_sub, mul_one, mul_smul_comm, sub_add_eq_sub_sub]

theorem update_eq_self_iff :
    update α β x y W = W ↔ α * x = 0 ∨ (y - x ᵥ* W) * β = 0 := by
  simp [update, ← Matrix.ext_iff, vecMulVec_apply, funext_iff, forall_or_left, forall_or_right]

theorem update_eq_self_of_vecMul_eq {x y W} (h : x ᵥ* W = y) : update α β x y W = W :=
  (update_eq_self_iff ..).2 <| .inr <| by rw [h, sub_self, zero_mul]

/-! ### Repeating an event -/

theorem sub_vecMul_iterate_update (n : ℕ) :
    y - x ᵥ* (update α β x y)^[n] W = (y - x ᵥ* W) * (1 - (x ⬝ᵥ (α * x)) • β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', sub_vecMul_update, ih, pow_succ, mul_assoc]

theorem iterate_update (n : ℕ) :
    (update α β x y)^[n] W = W + vecMulVec (α * x)
      ((y - x ᵥ* W) * β * ∑ k ∈ range n, (1 - (x ⬝ᵥ (α * x)) • β) ^ k) := by
  induction n with
  | zero => ext; simp [vecMulVec_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', update, sub_vecMul_iterate_update, ih, add_assoc,
      ← vecMulVec_add, sum_range_succ]
    congr 2
    ring

theorem iterate_update_apply (n : ℕ) (i : ι) (j : κ) :
    (update α β x y)^[n] W i j = W i j +
      α i * x i * ((y j - (x ᵥ* W) j) * β j * ∑ k ∈ range n, (1 - x ⬝ᵥ (α * x) * β j) ^ k) := by
  simp [iterate_update, vecMulVec_apply]

variable {α β x}

theorem tendsto_vecMul_iterate_update (h : ∀ j, |1 - x ⬝ᵥ (α * x) * β j| < 1) :
    Tendsto (fun n ↦ x ᵥ* (update α β x y)^[n] W) atTop (𝓝 y) := by
  refine tendsto_pi_nhds.2 fun j ↦ ?_
  have hn (n : ℕ) : (x ᵥ* (update α β x y)^[n] W) j =
      y j - (y j - (x ᵥ* W) j) * (1 - x ⬝ᵥ (α * x) * β j) ^ n := by
    have := congrFun (sub_vecMul_iterate_update α β x y W n) j
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, Pi.smul_apply,
      smul_eq_mul] at this
    linarith
  simpa [hn] using
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (h j)).const_mul (y j - (x ᵥ* W) j)).const_sub
      (y j)

theorem tendsto_iterate_update_apply (i : ι) {j : κ} (h : |1 - x ⬝ᵥ (α * x) * β j| < 1) :
    Tendsto (fun n ↦ (update α β x y)^[n] W i j) atTop
      (𝓝 (W i j + α i * x i / x ⬝ᵥ (α * x) * (y j - (x ᵥ* W) j))) := by
  have hg : x ⬝ᵥ (α * x) * β j ≠ 0 := fun h0 ↦ by simp [h0] at h
  have hn (n : ℕ) : (update α β x y)^[n] W i j = W i j +
      α i * x i / x ⬝ᵥ (α * x) * (y j - (x ᵥ* W) j) * (1 - (1 - x ⬝ᵥ (α * x) * β j) ^ n) := by
    rw [iterate_update_apply, ← mul_neg_geom_sum]
    have := left_ne_zero_of_mul hg
    field_simp
    ring
  simpa [hn] using ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).const_sub 1).const_mul
    (α i * x i / x ⬝ᵥ (α * x) * (y j - (x ᵥ* W) j)) |>.const_add (W i j)

end ErrorDrivenLearning
