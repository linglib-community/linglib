module

public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Order.Filter.Extr

/-!
# Training a discriminative lexicon

A discriminative lexicon is trained by solving `SG = C` in the least-squares sense, the mapping
matrix `G` minimising the frequency-weighted loss `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²`. Uniform weights give
endstate learning and token counts give frequency-informed learning, which is
[endstate learning on the repeated tokens](##isELTrained_tokens_iff) and equally
[on the `√Q`-premultiplied experience](##isELTrained_sqrtScale_iff). Endstate learning is
[orthogonal projection](##isELTrained_iff_fittedValues_eq_starProjection) onto the space of fitted
values, whence the [normal equations](##isTrained_iff) `SᵀQ(SG − C) = 0`,
[existence](##exists_isTrained), and [unique fitted values](##IsTrained.mul_eq); the matrix itself
is unique
[exactly when the experienced meanings span the meaning space](##existsUnique_isTrained_iff).
The residuals are orthogonal to every linear functional of the meanings, so a trained matrix
[sends the centre of mass](##IsTrained.centerMass_vecMul_eq_of_decodable) of a linearly decodable
set of meanings to that of its forms. Comprehension is the same regression on the experience
`⟨C, S⟩`.

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
open scoped RealInnerProductSpace

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

theorem isTrained_of_mul_eq (h : data.S * G = data.C) : IsTrained data q G :=
  isMinOn_univ_iff.2 fun G' ↦ by
    simpa [weightedLoss, h, dotProduct] using weightedLoss_nonneg data q G'

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

/-- FIL under `q` is exactly EL on the `√Q`-premultiplied experience ([gahl-baayen-2024] (A4);
[heitmeier-chuang-axen-baayen-2024] §3.4), which needs no invertibility assumption. -/
theorem isELTrained_sqrtScale_iff : IsELTrained (data.sqrtScale q) G ↔ IsTrained data q G := by
  have h : weightedLoss (data.sqrtScale q) 1 = weightedLoss data q :=
    funext fun G ↦ weightedLoss_sqrtScale data q G
  simp only [IsELTrained, IsTrained, h]

/-- The **token experience** under counts `f` repeats each usage event `i` exactly `f i` times, the
matrices `S_f` and `C_f` of [heitmeier-chuang-axen-baayen-2024] §3.4, which reflect the entire
learning history. -/
def TrainingExperience.tokens (f : Fin m → ℕ) : TrainingExperience (∑ i, f i) n d where
  S := data.S.submatrix (fun k ↦ (finSigmaFinEquiv.symm k).1) id
  C := data.C.submatrix (fun k ↦ (finSigmaFinEquiv.symm k).1) id

theorem weightedLoss_tokens (f : Fin m → ℕ) :
    weightedLoss (data.tokens f) 1 G = weightedLoss data (fun i ↦ (f i : ℝ≥0)) G := by
  have hrow (k) : ((data.tokens f).S * G - (data.tokens f).C) k =
      (data.S * G - data.C) (finSigmaFinEquiv.symm k).1 := rfl
  simp only [weightedLoss, hrow, Pi.one_apply, NNReal.coe_one, one_mul, NNReal.coe_natCast]
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
  simp

/-- FIL under token counts is exactly EL on the repeated tokens: working with one row per word type
weighted by its count trains the same mapping as working with one row per token
([gahl-baayen-2024] appendix; [heitmeier-chuang-axen-baayen-2024] §3.4). -/
theorem isELTrained_tokens_iff (f : Fin m → ℕ) :
    IsELTrained (data.tokens f) G ↔ IsTrained data (fun i ↦ (f i : ℝ≥0)) G := by
  have h : weightedLoss (data.tokens f) 1 = weightedLoss data fun i ↦ (f i : ℝ≥0) :=
    funext fun G ↦ weightedLoss_tokens data G f
  simp only [IsELTrained, IsTrained, h]

/-! ### Training as orthogonal projection

Through `Matrix.vec` the `m × n` tables form a Euclidean space, whose inner product is the trace
form and in which the loss under uniform weights is the squared distance from the observed forms to
the fitted values. Mapping matrices need no inner product of their own, and frequency-informed
learning reduces to this case by `isELTrained_sqrtScale_iff`. -/

/-- The **fitted values** `SG` of a mapping matrix, as a point of the Euclidean space of tables. -/
def TrainingExperience.fittedValues :
    Matrix (Fin d) (Fin n) ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m) where
  toFun G := WithLp.toLp 2 (data.S * G).vec
  map_add' G H := by rw [Matrix.mul_add]; rfl
  map_smul' c G := by rw [Matrix.mul_smul]; rfl

private theorem weightedLoss_one :
    weightedLoss data 1 G = ‖WithLp.toLp 2 data.C.vec - data.fittedValues G‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type_right, weightedLoss]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [TrainingExperience.fittedValues, dotProduct, ← pow_two, sub_sq_comm]

private theorem isELTrained_iff_forall_inner_eq_zero :
    IsELTrained data G ↔
      ∀ H, ⟪WithLp.toLp 2 data.C.vec - data.fittedValues G, data.fittedValues H⟫ = 0 := by
  have hb : BddBelow (Set.range fun w : LinearMap.range data.fittedValues ↦
      ‖WithLp.toLp 2 data.C.vec - w‖) := ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  have h := (LinearMap.range data.fittedValues).norm_eq_iInf_iff_inner_eq_zero
    (u := WithLp.toLp 2 data.C.vec) (LinearMap.mem_range_self data.fittedValues G)
  rw [le_antisymm_iff, and_iff_left (ciInf_le hb ⟨_, LinearMap.mem_range_self _ G⟩),
    le_ciInf_iff hb] at h
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_one,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa using h

/-- Endstate learning is orthogonal projection: `G` is trained exactly when its fitted values are
the projection of the observed forms onto the space of all fitted values. -/
theorem isELTrained_iff_fittedValues_eq_starProjection :
    IsELTrained data G ↔ data.fittedValues G =
      (LinearMap.range data.fittedValues).starProjection (WithLp.toLp 2 data.C.vec) := by
  rw [isELTrained_iff_forall_inner_eq_zero]
  refine ⟨fun h ↦ (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self _ G) ?_).symm, fun h H ↦ ?_⟩
  · rintro _ ⟨H, rfl⟩; exact h H
  · rw [h]; exact Submodule.starProjection_inner_eq_zero _ _ (LinearMap.mem_range_self _ H)

theorem exists_isTrained : ∃ G, IsTrained data q G := by
  obtain ⟨G, hG⟩ := LinearMap.mem_range.1 <| Submodule.starProjection_apply_mem
    (LinearMap.range (data.sqrtScale q).fittedValues) (WithLp.toLp 2 (data.sqrtScale q).C.vec)
  exact ⟨G, (isELTrained_sqrtScale_iff data q G).1
    ((isELTrained_iff_fittedValues_eq_starProjection _ _).2 hG)⟩

/-! ### The normal equations -/

private theorem isELTrained_iff_transpose_mul_eq_zero :
    IsELTrained data G ↔ data.Sᵀ * (data.S * G - data.C) = 0 := by
  have key (H : Matrix (Fin d) (Fin n) ℝ) :
      ⟪WithLp.toLp 2 data.C.vec - data.fittedValues G, data.fittedValues H⟫ =
        -(Hᵀ * (data.Sᵀ * (data.S * G - data.C))).trace := by
    change ⟪WithLp.toLp 2 (data.C - data.S * G).vec,
      (WithLp.toLp 2 (data.S * H).vec : EuclideanSpace ℝ _)⟫ = _
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, vec_dotProduct_vec, transpose_mul,
      Matrix.mul_assoc, ← trace_neg, ← Matrix.mul_neg, ← Matrix.mul_neg, neg_sub]
  rw [isELTrained_iff_forall_inner_eq_zero]
  simp only [key, neg_eq_zero]
  exact ⟨fun h ↦ ext_iff_trace_mul_left.2 fun x ↦ by simpa using h xᵀ, fun h H ↦ by simp [h]⟩

/-- `G` is trained iff it satisfies the **normal equations** `SᵀQ(SG − C) = 0`
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_iff : IsTrained data q G ↔ data.Sᵀ * q.Q * (data.S * G - data.C) = 0 := by
  have h : (data.sqrtScale q).Sᵀ * ((data.sqrtScale q).S * G - (data.sqrtScale q).C) =
      data.Sᵀ * q.Q * (data.S * G - data.C) := by
    change (q.sqrtQ * data.S)ᵀ * (q.sqrtQ * data.S * G - q.sqrtQ * data.C) = _
    rw [transpose_mul, FrequencyVector.sqrtQ_transpose, Matrix.mul_assoc q.sqrtQ, ← Matrix.mul_sub,
      Matrix.mul_assoc, ← Matrix.mul_assoc q.sqrtQ, FrequencyVector.sqrtQ_mul_sqrtQ,
      Matrix.mul_assoc]
  rw [← isELTrained_sqrtScale_iff, isELTrained_iff_transpose_mul_eq_zero, h]

/-- When `SᵀQS` is invertible, the **closed form** `G = (SᵀQS)⁻¹SᵀQC` is trained
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_closedForm (hS : IsUnit (data.Sᵀ * q.Q * data.S)) :
    IsTrained data q ((data.Sᵀ * q.Q * data.S)⁻¹ * (data.Sᵀ * q.Q * data.C)) := by
  rw [isTrained_iff, Matrix.mul_sub, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hS), sub_self]

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
  have h : q.sqrtQ * data.S * G = q.sqrtQ * data.S * G' :=
    vec_inj.1 <| WithLp.toLp_injective 2 <|
      ((isELTrained_iff_fittedValues_eq_starProjection _ G).1
        ((isELTrained_sqrtScale_iff data q G).2 hG)).trans
      ((isELTrained_iff_fittedValues_eq_starProjection _ G').1
        ((isELTrained_sqrtScale_iff data q G').2 hG')).symm
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_assoc, FrequencyVector.sqrtQ, diagonal_mul] at hij
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' hij

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
meaning space, the coordinate-free form of `S` having full column rank. The papers assume this
silently in writing the closed form `(SᵀS)⁻¹SᵀC`. -/
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

/-- A form coordinate that is a linear functional of the meanings is reproduced exactly, since its
residual is then a linear functional of the meanings as well, and so orthogonal to itself. -/
theorem IsTrained.mul_apply_eq_of_decodable (hq : ∀ i, 0 < q i) (hG : IsTrained data q G)
    {j₀ : Fin n} {w : MeaningVector d →ₗ[ℝ] ℝ} (hw : ∀ i, w (data.S i) = data.C i j₀) (i : Fin m) :
    (data.S * G) i j₀ = data.C i j₀ := by
  have hr := congrFun (hG.sum_smul_sub_eq_zero (LinearMap.proj j₀ ∘ₗ vecMulLinear G - w)) j₀
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.proj_apply, vecMulLinear_apply,
    hw, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
    ← mul_apply_eq_vecMul, mul_assoc] at hr
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦
    mul_nonneg (q x).2 (mul_self_nonneg _)).1 hr i (Finset.mem_univ i)
  simpa [(NNReal.coe_pos.2 (hq i)).ne', sub_eq_zero] using h0

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

/-- An EL-trained mapping sends the centroid of a linearly decodable set's meanings to the centroid
of its forms ([chuang-bell-tseng-baayen-2026] §3.4, [lu-chuang-baayen-2026] §4.4). -/
theorem IsELTrained.centroid_vecMul_eq_of_decodable (hG : IsELTrained data G)
    {P : Finset (Fin m)} (hP : P.Nonempty) {w : MeaningVector d →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = if i ∈ P then 1 else 0) :
    P.centroid ℝ data.S.row ᵥ* G = P.centroid ℝ data.C.row := by
  simpa [P.centroid_eq_centerMass hP, Finset.centerMass, ← Finset.smul_sum, hP.card_ne_zero] using
    hG.centerMass_vecMul_eq_of_decodable hw

end

end DiscriminativeLexicon
