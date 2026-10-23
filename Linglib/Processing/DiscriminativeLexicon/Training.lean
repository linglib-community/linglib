module

public import Linglib.Core.Analysis.LeastSquares
public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Training a discriminative lexicon

This file defines training for a linear discriminative lexicon and proves the normal equations
and the existence and uniqueness results that the papers rely on.

A discriminative lexicon is trained by solving `SG = C` in the least-squares sense over the
semantic matrix `S` and form matrix `C` of a training experience, the mapping matrix `G`
minimising the frequency-weighted loss `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²`. The weights record the cognitive
commitment. They are uniform for endstate learning and token counts for the frequency-informed
learning of Heitmeier, Chuang, Axen and Baayen, and the optimisation itself is fixed. The loss
separates over form coordinates, so each column of `G` is a vector least-squares problem for the
`√Q`-scaled design `√Q S`, whose minimisers Mathlib characterises by the adjoint
(`Core.IsLeastSquares`). From this we obtain the normal equations `SᵀQ(SG − C) = 0` of Gahl and
Baayen's appendix and their closed form `(SᵀQS)⁻¹SᵀQC`, the existence of trained matrices, the
uniqueness of the fitted values `SG` and hence of the predicted forms at experienced meanings,
the solution coset, and Heitmeier's identification of frequency-informed learning under `q` with
endstate learning on the `√Q`-premultiplied experience. Comprehension is the same regression
with the two matrices exchanged, `CF = S`, so every result applies to it on the experience
`⟨C, S⟩`.

The normal equations make the weighted residuals orthogonal to every linear functional of the
meanings. A trained production matrix therefore reproduces the observed forms on average over
any set of usage events whose membership is such a functional: it sends the frequency-weighted
centre of mass of the set's meanings to that of its forms, and under endstate learning centroid
to centroid. Chuang, Bell, Tseng and Baayen and Lu, Chuang and Baayen observe this as the similarity
between the contours predicted from centroid embeddings and the average observed contours of
word types and tone patterns.

## Main definitions

* `TrainingExperience`: a semantic matrix and a form matrix with one usage event per row.
* `FrequencyVector`, `weightedLoss`: the weights of the usage events and the loss they weight.
* `IsTrained`, `IsELTrained`: a mapping matrix minimises the weighted loss, under given or
  uniform weights.

## Main results

* `isTrained_iff`, `isTrained_closedForm`: training is the normal equations `SᵀQ(SG − C) = 0`,
  which the closed form solves.
* `IsTrained.mul_eq`, `existsUnique_isTrained_iff`: fitted values are unique, and the trained
  matrix is unique exactly when the experienced meanings span the meaning space.
* `isELTrained_sqrtScale_iff`: FIL under `q` is EL on `TrainingExperience.sqrtScale`.
* `IsTrained.centerMass_vecMul_eq_of_decodable`, `IsELTrained.centroid_vecMul_eq_of_decodable`:
  a trained mapping matrix sends the centre of mass of a linearly decodable set of meanings to the
  centre of mass of its forms.

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Heitmeier, *Mappings in the Discriminative Lexicon Model* (2024)][heitmeier-2024]
* [M. Heitmeier, Y.-Y. Chuang, S. D. Axen and R. H. Baayen, *Frequency effects in linear
  discriminative learning* (2024)][heitmeier-chuang-axen-baayen-2024]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken
  Taiwan Mandarin* (2026)][lu-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

noncomputable section

open Matrix NNReal

variable {m n d : ℕ}

/-! ### The training problem -/

/-- A **training experience** consists of the papers' semantic matrix `S` and form matrix `C`,
with one usage event per row. -/
structure TrainingExperience (numEvents formDim meaningDim : ℕ) where
  /-- The semantic matrix has the experienced meanings as its rows. -/
  S : Matrix (Fin numEvents) (Fin meaningDim) ℝ
  /-- The form matrix has the observed forms as its rows. -/
  C : Matrix (Fin numEvents) (Fin formDim) ℝ

/-- A **frequency vector** weights each usage event, the diagonal of the papers' `Q`. Uniform
weights give EL, token counts FIL ([gahl-baayen-2024]'s appendix, which warns against
log-transforming them). -/
abbrev FrequencyVector (numEvents : ℕ) : Type := Fin numEvents → ℝ≥0

variable (data : TrainingExperience m n d) (q : FrequencyVector m) (G : Matrix (Fin d) (Fin n) ℝ)

/-- The weight matrix `Q` places the frequencies on the diagonal. -/
def FrequencyVector.Q : Matrix (Fin m) (Fin m) ℝ := diagonal fun i ↦ (q i : ℝ)

/-- The matrix `√Q` of the papers' appendix places the square roots of the frequencies on the
diagonal. -/
def FrequencyVector.sqrtQ : Matrix (Fin m) (Fin m) ℝ := diagonal fun i ↦ √(q i : ℝ)

@[simp] theorem FrequencyVector.Q_one : (1 : FrequencyVector m).Q = 1 := by
  simp [FrequencyVector.Q]

@[simp] theorem FrequencyVector.sqrtQ_one : (1 : FrequencyVector m).sqrtQ = 1 := by
  simp [FrequencyVector.sqrtQ]

@[simp] theorem FrequencyVector.sqrtQ_transpose : q.sqrtQᵀ = q.sqrtQ := diagonal_transpose _

theorem FrequencyVector.sqrtQ_mul_sqrtQ : q.sqrtQ * q.sqrtQ = q.Q := by
  simp [FrequencyVector.sqrtQ, FrequencyVector.Q, diagonal_mul_diagonal, Real.mul_self_sqrt]

/-- Scaling by `√Q` premultiplies both matrices of the experience, giving the `(√Q S, √Q C)` of
the papers' appendix. -/
def TrainingExperience.sqrtScale : TrainingExperience m n d := ⟨q.sqrtQ * data.S, q.sqrtQ * data.C⟩

@[simp] theorem TrainingExperience.sqrtScale_S (i : Fin m) :
    (data.sqrtScale q).S i = √(q i : ℝ) • data.S i := by
  funext k; simp [TrainingExperience.sqrtScale, FrequencyVector.sqrtQ, diagonal_mul]

@[simp] theorem TrainingExperience.sqrtScale_C (i : Fin m) :
    (data.sqrtScale q).C i = √(q i : ℝ) • data.C i := by
  funext j; simp [TrainingExperience.sqrtScale, FrequencyVector.sqrtQ, diagonal_mul]

/-- The **frequency-weighted training loss** `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²` weights the squared residual
of each usage event by its frequency. -/
def weightedLoss : ℝ :=
  ∑ i, q i * ((data.S * G - data.C) i ⬝ᵥ (data.S * G - data.C) i)

theorem weightedLoss_nonneg : 0 ≤ weightedLoss data q G :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (q i).2 (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)

theorem weightedLoss_eq_zero_iff (hq : ∀ i, 0 < q i) :
    weightedLoss data q G = 0 ↔ data.S * G = data.C := by
  constructor
  · intro h0
    ext i j
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
      mul_nonneg (q k).2 (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)).1 h0 i
      (Finset.mem_univ i)
    have hrow := dotProduct_self_eq_zero.1
      ((mul_eq_zero.1 hterm).resolve_left (NNReal.coe_pos.2 (hq i)).ne')
    simpa [sub_eq_zero] using congrFun hrow j
  · intro h
    simp [weightedLoss, h, dotProduct]

/-- `G` is **trained** on `data` under `q` when it minimises the weighted loss over all mapping
matrices, which solves `SG = C` by least squares. -/
def IsTrained : Prop := IsMinOn (weightedLoss data q) Set.univ G

/-- **Endstate learning** is training under uniform weights ([gahl-baayen-2024] appendix). -/
abbrev IsELTrained : Prop := IsTrained data 1 G

theorem weightedLoss_smul (c : ℝ≥0) :
    weightedLoss data (c • q) G = c * weightedLoss data q G := by
  simp [weightedLoss, Finset.mul_sum, mul_assoc]

theorem isTrained_of_mul_eq (h : data.S * G = data.C) : IsTrained data q G :=
  isMinOn_univ_iff.2 fun G' ↦ by
    simpa [weightedLoss, h, dotProduct] using weightedLoss_nonneg data q G'

theorem isTrained_smul_iff {c : ℝ≥0} (hc : 0 < c) :
    IsTrained data (c • q) G ↔ IsTrained data q G := by
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_smul,
    mul_le_mul_iff_right₀ (NNReal.coe_pos.2 hc)]

theorem weightedLoss_sqrtScale :
    weightedLoss (data.sqrtScale q) 1 G = weightedLoss data q G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hrow : ((data.sqrtScale q).S * G - (data.sqrtScale q).C) i =
      √(q i : ℝ) • (data.S * G - data.C) i := by
    show (data.sqrtScale q).S i ᵥ* G - (data.sqrtScale q).C i =
      √(q i : ℝ) • (data.S i ᵥ* G - data.C i)
    rw [TrainingExperience.sqrtScale_S, TrainingExperience.sqrtScale_C, smul_vecMul, smul_sub]
  rw [hrow, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp [← mul_assoc, Real.mul_self_sqrt (q i).coe_nonneg]

/-- FIL under `q` is exactly EL on the `√Q`-premultiplied experience, which is the FIL–EL
equivalence of [heitmeier-2024] without any invertibility assumption. -/
theorem isELTrained_sqrtScale_iff : IsELTrained (data.sqrtScale q) G ↔ IsTrained data q G := by
  have h : weightedLoss (data.sqrtScale q) 1 = weightedLoss data q :=
    funext fun G ↦ weightedLoss_sqrtScale data q G
  simp only [IsELTrained, IsTrained, h]

/-! ### Training as columnwise least squares

The loss separates over form coordinates, so column `j` of `G` is a least-squares solution of
the `√Q`-scaled regression of column `j` of `C` on `S`, a vector problem in Euclidean space. -/

theorem weightedLoss_eq_sum_norm_sq :
    weightedLoss data q G = ∑ j, ‖WithLp.toLp 2 ((q.sqrtQ * data.C).col j) -
      toEuclideanLin (q.sqrtQ * data.S) (WithLp.toLp 2 (G.col j))‖ ^ 2 := by
  simp only [toLpLin_toLp, toLin'_apply, ← WithLp.toLp_sub, EuclideanSpace.norm_sq_eq,
    Pi.sub_apply, Real.norm_eq_abs, sq_abs, ← col_mul_eq_mulVec_col, col_apply, Matrix.mul_assoc,
    FrequencyVector.sqrtQ, diagonal_mul]
  rw [Finset.sum_comm]
  unfold weightedLoss dotProduct
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.sub_apply]
  linear_combination -(data.C i j - (data.S * G) i j) ^ 2 * Real.mul_self_sqrt (q i).coe_nonneg

private theorem sum_min_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    (g : ∀ i, β i → ℝ) (x : ∀ i, β i) :
    (∀ y : ∀ i, β i, ∑ i, g i (x i) ≤ ∑ i, g i (y i)) ↔ ∀ i, ∀ b : β i, g i (x i) ≤ g i b := by
  refine ⟨fun h i b ↦ ?_, fun h y ↦ Finset.sum_le_sum fun i _ ↦ h i (y i)⟩
  have hy := h (Function.update x i b)
  simp_rw [Function.apply_update (fun j ↦ g j) x i b] at hy
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), Finset.erase_eq] at hy
  linarith

theorem isTrained_iff_forall_isLeastSquares :
    IsTrained data q G ↔ ∀ j, Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C).col j)) (WithLp.toLp 2 (G.col j)) := by
  have key := sum_min_iff (fun j v ↦ ‖WithLp.toLp 2 ((q.sqrtQ * data.C).col j) -
    toEuclideanLin (q.sqrtQ * data.S) (WithLp.toLp 2 v)‖ ^ 2) G.col
  simp only [IsTrained, Core.IsLeastSquares, isMinOn_univ_iff, weightedLoss_eq_sum_norm_sq]
  refine ⟨fun h j z ↦ ?_,
    fun h G' ↦ key.2 (fun j v ↦ pow_le_pow_left₀ (norm_nonneg _) (h j _) 2) G'.col⟩
  have := key.1 (fun y ↦ h (of y)ᵀ) j z.ofLp
  simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem exists_isTrained : ∃ G, IsTrained data q G := by
  choose x hx using fun j ↦ Core.exists_isLeastSquares (A := toEuclideanLin (q.sqrtQ * data.S))
    (b := WithLp.toLp 2 ((q.sqrtQ * data.C).col j))
  exact ⟨Matrix.of fun k j ↦ (x j).ofLp k, (isTrained_iff_forall_isLeastSquares _ _ _).2 hx⟩

/-! ### The normal equations -/

/-- `G` is trained iff it satisfies the **normal equations** `SᵀQ(SG − C) = 0`
([gahl-baayen-2024] (A2), (A4)), by Mathlib's adjoint characterisation of least squares applied
column by column. -/
theorem isTrained_iff : IsTrained data q G ↔ data.Sᵀ * q.Q * (data.S * G - data.C) = 0 := by
  have hcol : ∀ j, Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C).col j)) (WithLp.toLp 2 (G.col j)) ↔
      ((q.sqrtQ * data.S)ᵀ * (q.sqrtQ * data.C - q.sqrtQ * data.S * G)).col j = 0 := fun j ↦ by
    rw [Core.isLeastSquares_iff_adjoint_eq_zero, ← toEuclideanLin_conjTranspose_eq_adjoint,
      conjTranspose_eq_transpose_of_trivial]
    simp only [toLpLin_toLp, toLin'_apply, ← WithLp.toLp_sub, WithLp.toLp_eq_zero,
      col_mul_eq_mulVec_col]
    rfl
  have hX : (q.sqrtQ * data.S)ᵀ * (q.sqrtQ * data.C - q.sqrtQ * data.S * G) =
      -(data.Sᵀ * q.Q * (data.S * G - data.C)) := by
    rw [transpose_mul, FrequencyVector.sqrtQ_transpose, Matrix.mul_assoc q.sqrtQ,
      ← Matrix.mul_sub, Matrix.mul_assoc, ← Matrix.mul_assoc q.sqrtQ,
      FrequencyVector.sqrtQ_mul_sqrtQ, ← Matrix.mul_assoc, ← neg_sub (data.S * G) data.C,
      Matrix.mul_neg]
  rw [isTrained_iff_forall_isLeastSquares]
  simp only [hcol]
  rw [hX, ← neg_eq_zero (a := data.Sᵀ * q.Q * (data.S * G - data.C)), ← transpose_eq_zero]
  exact ⟨funext, fun h j ↦ congrFun h j⟩

/-- When `SᵀQS` is invertible, the **closed form** `G = (SᵀQS)⁻¹SᵀQC` is trained
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_closedForm (hS : IsUnit (data.Sᵀ * q.Q * data.S)) :
    IsTrained data q ((data.Sᵀ * q.Q * data.S)⁻¹ * (data.Sᵀ * q.Q * data.C)) := by
  rw [isTrained_iff, Matrix.mul_sub, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hS), sub_self]

theorem isELTrained_closedForm (hS : IsUnit (data.Sᵀ * data.S)) :
    IsELTrained data ((data.Sᵀ * data.S)⁻¹ * (data.Sᵀ * data.C)) := by
  simpa only [FrequencyVector.Q_one, Matrix.mul_one] using
    isTrained_closedForm data 1 (by simpa using hS)

variable {data q G}

theorem IsTrained.sum_smul_sub_eq_zero (hG : IsTrained data q G) (w : MeaningVector d →ₗ[ℝ] ℝ) :
    ∑ i, (q i * w (data.S i)) • ((data.S * G) i - data.C i) = 0 := by
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ (Fin d)).surjective w
  have h : v ᵥ* (data.Sᵀ * q.Q * (data.S * G - data.C)) = 0 := by
    rw [(isTrained_iff data q G).1 hG, vecMul_zero]
  rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, vecMul_eq_sum] at h
  simp only [FrequencyVector.Q, vecMul_diagonal] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [mul_comm, dotProductEquiv_apply_apply, dotProduct_comm]; rfl

theorem IsTrained.sum_smul_mul_eq_of_decodable (hG : IsTrained data q G) {P : Finset (Fin m)}
    {w : MeaningVector d →ₗ[ℝ] ℝ} (hw : ∀ i, w (data.S i) = if i ∈ P then 1 else 0) :
    ∑ i ∈ P, (q i : ℝ) • (data.S * G) i = ∑ i ∈ P, (q i : ℝ) • data.C i := by
  simpa only [hw, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_mem,
    Finset.univ_inter, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] using
    hG.sum_smul_sub_eq_zero w

/-! ### Fitted values -/

/-- All trained matrices under positive weights produce the same predicted forms `SG` on the
training events, so fitted values are unique even when `G` is not. -/
theorem IsTrained.mul_eq (hq : ∀ i, 0 < q i) {G' : Matrix (Fin d) (Fin n) ℝ}
    (hG : IsTrained data q G) (hG' : IsTrained data q G') : data.S * G = data.S * G' := by
  rw [isTrained_iff_forall_isLeastSquares] at hG hG'
  ext i j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v.ofLp i) ((hG j).map_eq (hG' j))
  simp only [toLpLin_toLp, toLin'_apply, WithLp.ofLp_toLp, ← col_mul_eq_mulVec_col, col_apply,
    Matrix.mul_assoc, FrequencyVector.sqrtQ, diagonal_mul] at h
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' h

theorem IsTrained.vecMul_eq_of_mem_span (hq : ∀ i, 0 < q i) {G' : Matrix (Fin d) (Fin n) ℝ}
    (hG : IsTrained data q G) (hG' : IsTrained data q G') {s : MeaningVector d}
    (hs : s ∈ Submodule.span ℝ (Set.range data.S.row)) : s ᵥ* G = s ᵥ* G' := by
  have hker : Submodule.span ℝ (Set.range data.S.row) ≤ LinearMap.ker (toLin' (G - G')ᵀ) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i ↦ by
      simp only [SetLike.mem_coe, LinearMap.mem_ker, toLin'_apply, mulVec_transpose,
        Matrix.vecMul_sub, sub_eq_zero]
      exact congrFun (hG.mul_eq hq hG') i
  have h0 := hker hs
  rw [LinearMap.mem_ker, toLin'_apply, mulVec_transpose, Matrix.vecMul_sub, sub_eq_zero] at h0
  exact h0

theorem IsTrained.add_of_mul_eq_zero (hG : IsTrained data q G) {H : Matrix (Fin d) (Fin n) ℝ}
    (hH : data.S * H = 0) : IsTrained data q (G + H) := by
  have : weightedLoss data q (G + H) = weightedLoss data q G := by
    simp [weightedLoss, Matrix.mul_add, hH]
  simpa only [IsTrained, isMinOn_univ_iff, this] using hG

theorem IsTrained.exists_vecMul_ne [NeZero n] (hG : IsTrained data q G) {s : MeaningVector d}
    (hs : s ∉ Submodule.span ℝ (Set.range data.S.row)) :
    ∃ G' : Matrix (Fin d) (Fin n) ℝ, IsTrained data q G' ∧ s ᵥ* G ≠ s ᵥ* G' := by
  obtain ⟨φ, hφ, hφs⟩ :
      ∃ φ ∈ (Submodule.span ℝ (Set.range data.S.row)).dualAnnihilator, φ s ≠ 0 := by
    simpa using mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp hs
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ (Fin d)).surjective φ
  have hvec (x : MeaningVector d) : x ᵥ* vecMulVec v (Pi.single 0 1 : FormVector n) =
      dotProductEquiv ℝ (Fin d) v x • Pi.single 0 1 := by
    rw [vecMul_vecMulVec, dotProductEquiv_apply_apply, dotProduct_comm]
  have hSH : data.S * vecMulVec v (Pi.single 0 1 : FormVector n) = 0 := ext_row fun i ↦ by
    rw [row_mul_eq_vecMul_row, hvec,
      (Submodule.mem_dualAnnihilator _).1 hφ _ (Submodule.subset_span ⟨i, rfl⟩), zero_smul]; rfl
  exact ⟨G + vecMulVec v (Pi.single 0 1), hG.add_of_mul_eq_zero hSH,
    fun h ↦ hφs (by simpa [Matrix.vecMul_add, hvec] using h.symm)⟩

/-- The trained matrix is uniquely determined exactly when the experienced meanings span the
meaning space, which is the coordinate-free form of the papers' full-column-rank condition on
the closed-form solution ([gahl-baayen-2024] appendix; [heitmeier-2024]). -/
theorem existsUnique_isTrained_iff [NeZero n] (hq : ∀ i, 0 < q i) :
    (∃! G : Matrix (Fin d) (Fin n) ℝ, IsTrained data q G) ↔
      Submodule.span ℝ (Set.range data.S.row) = ⊤ := by
  refine ⟨fun ⟨G, hG, huniq⟩ ↦ Submodule.eq_top_iff'.2 fun s ↦ by_contra fun hs ↦ ?_,
    fun htop ↦ ?_⟩
  · obtain ⟨G', hG', hne⟩ := hG.exists_vecMul_ne hs
    exact hne (by rw [huniq G' hG'])
  · obtain ⟨G, hG⟩ := exists_isTrained data q
    refine ⟨G, hG, fun G' hG' ↦ ext_row fun k ↦ ?_⟩
    simpa using hG'.vecMul_eq_of_mem_span hq hG (Submodule.eq_top_iff'.mp htop (Pi.single k 1))

theorem IsTrained.mul_apply_eq_of_decodable (hq : ∀ i, 0 < q i) (hG : IsTrained data q G)
    {j₀ : Fin n} {w : MeaningVector d →ₗ[ℝ] ℝ} (hw : ∀ i, w (data.S i) = data.C i j₀) (i : Fin m) :
    (data.S * G) i j₀ = data.C i j₀ := by
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ (Fin d)).surjective w
  have hSv : data.S *ᵥ v = data.C.col j₀ := funext fun i' ↦ by
    rw [col_apply, ← hw i', dotProductEquiv_apply_apply, dotProduct_comm]; rfl
  have hls : Core.IsLeastSquares (toEuclideanLin (q.sqrtQ * data.S))
      (WithLp.toLp 2 ((q.sqrtQ * data.C).col j₀)) (WithLp.toLp 2 v) :=
    Core.isLeastSquares_of_map_eq (by
      rw [toLpLin_toLp, toLin'_apply, ← mulVec_mulVec, hSv, ← col_mul_eq_mulVec_col])
  have h := congrArg (fun u : EuclideanSpace ℝ (Fin m) ↦ u.ofLp i)
    (((isTrained_iff_forall_isLeastSquares data q G).1 hG j₀).map_eq hls)
  simp only [toLpLin_toLp, toLin'_apply, WithLp.ofLp_toLp] at h
  rw [← mulVec_mulVec, ← mulVec_mulVec, hSv, FrequencyVector.sqrtQ, mulVec_diagonal,
    mulVec_diagonal, ← col_mul_eq_mulVec_col, col_apply, col_apply] at h
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' h

/-! ### Centres of mass -/

/-- Whenever membership in a set `P` of usage events is a linear functional of the meanings, a
mapping matrix trained under `q` sends the `q`-weighted centre of mass of `P`'s meanings to the
`q`-weighted centre of mass of `P`'s observed forms. -/
theorem IsTrained.centerMass_vecMul_eq_of_decodable (hG : IsTrained data q G)
    {P : Finset (Fin m)} {w : MeaningVector d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = if i ∈ P then 1 else 0) :
    P.centerMass (fun i ↦ (q i : ℝ)) data.S.row ᵥ* G =
      P.centerMass (fun i ↦ (q i : ℝ)) data.C.row := by
  have h := hG.sum_smul_mul_eq_of_decodable hw
  rw [← vecMulLinear_apply]
  simp only [Finset.centerMass, map_smul, map_sum]
  simp only [vecMulLinear_apply, row_apply', ← mul_apply_eq_vecMul, h]

/-- Under endstate learning the centre of mass is the centroid, so an EL-trained mapping matrix
sends the centroid of the meanings of a nonempty linearly decodable set of usage events to the
centroid of its observed forms, the similarity that [chuang-bell-tseng-baayen-2026] §3.4 and
[lu-chuang-baayen-2026] §4.4 report. -/
theorem IsELTrained.centroid_vecMul_eq_of_decodable (hG : IsELTrained data G)
    {P : Finset (Fin m)} (hP : P.Nonempty) {w : MeaningVector d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = if i ∈ P then 1 else 0) :
    P.centroid ℝ data.S.row ᵥ* G = P.centroid ℝ data.C.row := by
  simpa [P.centroid_eq_centerMass hP, Finset.centerMass, ← Finset.smul_sum, hP.card_ne_zero] using
    hG.centerMass_vecMul_eq_of_decodable hw

end

end DiscriminativeLexicon
