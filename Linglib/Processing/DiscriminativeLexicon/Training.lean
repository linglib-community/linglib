module

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

The linear discriminative lexicon relates form and meaning by learned matrices rather than by
stored, decomposed entries. Words' forms and meanings are row vectors, stacked into a form matrix
`C` and a semantic matrix `S`; production predicts `Ĉ = SG` and comprehension `Ŝ = CF`. Training
solves `SG = C` in the least-squares sense, `G` minimising the frequency-weighted loss
`∑ᵢ qᵢ ‖(SG − C)ᵢ‖²`, and comprehension is the same regression with the matrices exchanged. Uniform
weights give endstate learning and token counts give frequency-informed learning, which is
[endstate learning on the repeated tokens](##isEndstateTrained_submatrix_fst_iff) and equally
[on the `√Q`-premultiplied matrices](##isEndstateTrained_diagonal_sqrt_mul_iff). Endstate learning
is [orthogonal projection](##isEndstateTrained_iff_predicted_eq_starProjection) onto the space of
predictions, whence the [normal equations](##isTrained_iff) `SᵀQ(SG − C) = 0`,
[existence](##exists_isTrained), and [unique predictions](##IsTrained.mul_eq); the matrix itself is
unique [exactly when the experienced meanings span the meaning space](##existsUnique_isTrained_iff).
A trained matrix [sends the centre of mass](##IsTrained.centerMass_vecMul_eq_of_decodable) of a
linearly decodable set of meanings to that of its forms.

## Implementation notes

The mappings are the papers' matrices rather than bundled linear maps, and `S`, `C` and `q` are
separate arguments, so statements read as the papers' equations; `Matrix.vecMulLinear` gives the
linear map where linear algebra needs one. The papers' weight matrix `Q` is `Matrix.diagonal` of
`q`. *Linearly decodable* is our term, not the papers': a set of usage events is linearly decodable
when membership in it is a linear functional of the meanings.

## TODO

The deep mappings that replace or augment the linear ones, DDL and ResLDL, are not formalized.

## References

* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Heitmeier, *Mappings in the Discriminative Lexicon Model* (2024)][heitmeier-2024]
* [M. Heitmeier, Y.-Y. Chuang, S. D. Axen and R. H. Baayen, *Frequency effects in linear
  discriminative learning* (2024)][heitmeier-chuang-axen-baayen-2024]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [M. Heitmeier, V. Schmidt, H. P. A. Lensch and R. H. Baayen, *Is deeper always better?*
  (2025)][heitmeier-schmidt-lensch-baayen-2025]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken
  Taiwan Mandarin* (2026)][lu-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

noncomputable section

open Matrix NNReal
open scoped RealInnerProductSpace

variable {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
  (S : Matrix ι δ ℝ) (C : Matrix ι κ ℝ) (q : ι → ℝ≥0) (G : Matrix δ κ ℝ)

/-! ### The training problem -/

/-- The **frequency-weighted training loss** `∑ᵢ qᵢ ‖(SG − C)ᵢ‖²` weights the squared residual of
each usage event by its frequency, `q` being the diagonal of the papers' `Q`. Uniform weights give
endstate learning and token counts frequency-informed learning ([gahl-baayen-2024]'s appendix,
which warns against log-transforming them). -/
def weightedLoss : ℝ := ∑ i, q i * ((S * G - C) i ⬝ᵥ (S * G - C) i)

theorem weightedLoss_nonneg : 0 ≤ weightedLoss S C q G :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (q i).2 (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)

theorem weightedLoss_eq_zero_iff (hq : ∀ i, 0 < q i) :
    weightedLoss S C q G = 0 ↔ S * G = C := by
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

/-- `G` is **trained** on `S` and `C` under `q` when it minimises the weighted loss over all mapping
matrices, which solves `SG = C` by least squares. -/
def IsTrained : Prop := IsMinOn (weightedLoss S C q) Set.univ G

/-- **Endstate learning** is training under uniform weights ([gahl-baayen-2024] appendix). -/
abbrev IsEndstateTrained : Prop := IsTrained S C 1 G

theorem isTrained_of_mul_eq (h : S * G = C) : IsTrained S C q G :=
  isMinOn_univ_iff.2 fun G' ↦ by
    simpa [weightedLoss, h, dotProduct] using weightedLoss_nonneg S C q G'

theorem weightedLoss_diagonal_sqrt_mul [DecidableEq ι] :
    weightedLoss (diagonal (fun i ↦ √(q i : ℝ)) * S) (diagonal (fun i ↦ √(q i : ℝ)) * C) 1 G =
      weightedLoss S C q G := by
  unfold weightedLoss
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hrow : (diagonal (fun i ↦ √(q i : ℝ)) * S * G - diagonal (fun i ↦ √(q i : ℝ)) * C) i =
      √(q i : ℝ) • (S * G - C) i := by
    funext j; simp [Matrix.mul_assoc, diagonal_mul, mul_sub]
  rw [hrow, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp [← mul_assoc, Real.mul_self_sqrt (q i).coe_nonneg]

/-- Frequency-informed learning under `q` is exactly endstate learning on the `√Q`-premultiplied
matrices ([gahl-baayen-2024] (A4); [heitmeier-chuang-axen-baayen-2024] §3.4), which needs no
invertibility assumption. -/
theorem isEndstateTrained_diagonal_sqrt_mul_iff [DecidableEq ι] :
    IsEndstateTrained (diagonal (fun i ↦ √(q i : ℝ)) * S) (diagonal (fun i ↦ √(q i : ℝ)) * C) G ↔
      IsTrained S C q G := by
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_diagonal_sqrt_mul]

theorem weightedLoss_submatrix_fst (f : ι → ℕ) :
    weightedLoss (S.submatrix (Sigma.fst : (Σ i, Fin (f i)) → ι) id)
      (C.submatrix Sigma.fst id) 1 G = weightedLoss S C (fun i ↦ (f i : ℝ≥0)) G := by
  have hrow (k : Σ i, Fin (f i)) :
      (S.submatrix Sigma.fst id * G - C.submatrix Sigma.fst id : Matrix (Σ i, Fin (f i)) κ ℝ) k =
        (S * G - C) k.1 := rfl
  simp [weightedLoss, hrow, Fintype.sum_sigma]

/-- Frequency-informed learning under token counts is exactly endstate learning on the repeated
tokens: one row per word type weighted by its count trains the same mapping as one row per token,
the matrices `S_f` and `C_f` of [heitmeier-chuang-axen-baayen-2024] §3.4 ([gahl-baayen-2024]
appendix). -/
theorem isEndstateTrained_submatrix_fst_iff (f : ι → ℕ) :
    IsEndstateTrained (S.submatrix (Sigma.fst : (Σ i, Fin (f i)) → ι) id)
      (C.submatrix Sigma.fst id) G ↔ IsTrained S C (fun i ↦ (f i : ℝ≥0)) G := by
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_submatrix_fst]

/-! ### Training as orthogonal projection

Through `Matrix.vec` the tables with rows `ι` and columns `κ` form a Euclidean space, whose inner
product is the trace form and in which the loss under uniform weights is the squared distance from
the observed forms to the predictions. Mapping matrices need no inner product of their own, and
frequency-informed learning reduces to this case by `isEndstateTrained_diagonal_sqrt_mul_iff`. -/

variable (κ) in
/-- The **predictions** `SG` of a mapping matrix, as a point of the Euclidean space of tables. -/
def predicted : Matrix δ κ ℝ →ₗ[ℝ] EuclideanSpace ℝ (κ × ι) where
  toFun G := WithLp.toLp 2 (S * G).vec
  map_add' G H := by rw [Matrix.mul_add]; rfl
  map_smul' c G := by rw [Matrix.mul_smul]; rfl

private theorem weightedLoss_one_eq_norm_sq :
    weightedLoss S C 1 G = ‖WithLp.toLp 2 C.vec - predicted κ S G‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type_right, weightedLoss]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [predicted, dotProduct, ← pow_two, sub_sq_comm]

private theorem isEndstateTrained_iff_forall_inner_eq_zero :
    IsEndstateTrained S C G ↔
      ∀ H, ⟪WithLp.toLp 2 C.vec - predicted κ S G, predicted κ S H⟫ = 0 := by
  have hb : BddBelow (Set.range fun w : LinearMap.range (predicted κ S) ↦
      ‖WithLp.toLp 2 C.vec - (w : EuclideanSpace ℝ (κ × ι))‖) :=
    ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  have h := (LinearMap.range (predicted κ S)).norm_eq_iInf_iff_inner_eq_zero
    (u := WithLp.toLp 2 C.vec) (LinearMap.mem_range_self _ G)
  rw [le_antisymm_iff, and_iff_left (ciInf_le hb ⟨_, LinearMap.mem_range_self _ G⟩),
    le_ciInf_iff hb] at h
  simp only [IsTrained, isMinOn_univ_iff, weightedLoss_one_eq_norm_sq,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simpa using h

/-- Endstate learning is orthogonal projection: `G` is trained exactly when its predictions are the
projection of the observed forms onto the space of all predictions. -/
theorem isEndstateTrained_iff_predicted_eq_starProjection :
    IsEndstateTrained S C G ↔ predicted κ S G =
      (LinearMap.range (predicted κ S)).starProjection (WithLp.toLp 2 C.vec) := by
  rw [isEndstateTrained_iff_forall_inner_eq_zero]
  refine ⟨fun h ↦ (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self _ G) ?_).symm, fun h H ↦ ?_⟩
  · rintro _ ⟨H, rfl⟩; exact h H
  · rw [h]; exact Submodule.starProjection_inner_eq_zero _ _ (LinearMap.mem_range_self _ H)

private theorem exists_isEndstateTrained : ∃ G, IsEndstateTrained S C G :=
  (LinearMap.mem_range.1 <| Submodule.starProjection_apply_mem
    (LinearMap.range (predicted κ S)) (WithLp.toLp 2 C.vec)).imp fun G hG ↦
      (isEndstateTrained_iff_predicted_eq_starProjection S C G).2 hG

theorem exists_isTrained : ∃ G, IsTrained S C q G := by
  classical
  exact (exists_isEndstateTrained _ _).imp fun G ↦
    (isEndstateTrained_diagonal_sqrt_mul_iff S C q G).1

/-! ### The normal equations -/

private theorem isEndstateTrained_iff_transpose_mul_eq_zero :
    IsEndstateTrained S C G ↔ Sᵀ * (S * G - C) = 0 := by
  have key (H : Matrix δ κ ℝ) :
      ⟪WithLp.toLp 2 C.vec - predicted κ S G, predicted κ S H⟫ =
        -(Hᵀ * (Sᵀ * (S * G - C))).trace := by
    change ⟪WithLp.toLp 2 (C - S * G).vec,
      (WithLp.toLp 2 (S * H).vec : EuclideanSpace ℝ _)⟫ = _
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, vec_dotProduct_vec, transpose_mul,
      Matrix.mul_assoc, ← trace_neg, ← Matrix.mul_neg, ← Matrix.mul_neg, neg_sub]
  rw [isEndstateTrained_iff_forall_inner_eq_zero]
  simp only [key, neg_eq_zero]
  exact ⟨fun h ↦ ext_iff_trace_mul_left.2 fun x ↦ by simpa using h xᵀ, fun h H ↦ by simp [h]⟩

/-- `G` is trained iff it satisfies the **normal equations** `SᵀQ(SG − C) = 0`
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_iff [DecidableEq ι] :
    IsTrained S C q G ↔ Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * (S * G - C) = 0 := by
  have hQ : diagonal (fun i ↦ √(q i : ℝ)) * diagonal (fun i ↦ √(q i : ℝ)) =
      diagonal fun i ↦ (q i : ℝ) := by
    simp [diagonal_mul_diagonal, Real.mul_self_sqrt]
  have h : (diagonal (fun i ↦ √(q i : ℝ)) * S)ᵀ *
      (diagonal (fun i ↦ √(q i : ℝ)) * S * G - diagonal (fun i ↦ √(q i : ℝ)) * C) =
      Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * (S * G - C) := by
    rw [transpose_mul, diagonal_transpose, Matrix.mul_assoc (diagonal _), ← Matrix.mul_sub,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hQ, Matrix.mul_assoc]
  rw [← isEndstateTrained_diagonal_sqrt_mul_iff, isEndstateTrained_iff_transpose_mul_eq_zero, h]

/-- When `SᵀQS` is invertible, the **closed form** `G = (SᵀQS)⁻¹SᵀQC` is trained
([gahl-baayen-2024] (A2), (A4)). -/
theorem isTrained_closedForm [DecidableEq ι] [DecidableEq δ]
    (hS : IsUnit (Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * S)) :
    IsTrained S C q ((Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * S)⁻¹ *
      (Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * C)) := by
  rw [isTrained_iff, Matrix.mul_sub, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hS), sub_self]

variable {S C q G}

theorem IsTrained.sum_smul_sub_eq_zero (hG : IsTrained S C q G) (w : (δ → ℝ) →ₗ[ℝ] ℝ) :
    ∑ i, (q i * w (S i)) • ((S * G) i - C i) = 0 := by
  classical
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ δ).surjective w
  have h : v ᵥ* (Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * (S * G - C)) = 0 := by
    rw [(isTrained_iff S C q G).1 hG, vecMul_zero]
  rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, vecMul_eq_sum] at h
  simp only [vecMul_diagonal] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [mul_comm, dotProductEquiv_apply_apply, dotProduct_comm]; rfl

theorem IsTrained.sum_smul_mul_eq_of_decodable [DecidableEq ι] (hG : IsTrained S C q G)
    {P : Finset ι} {w : (δ → ℝ) →ₗ[ℝ] ℝ} (hw : ∀ i, w (S i) = if i ∈ P then 1 else 0) :
    ∑ i ∈ P, (q i : ℝ) • (S * G) i = ∑ i ∈ P, (q i : ℝ) • C i := by
  simpa only [hw, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_mem,
    Finset.univ_inter, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] using
    hG.sum_smul_sub_eq_zero w

/-! ### Predictions -/

private theorem mul_eq_of_isEndstateTrained {G' : Matrix δ κ ℝ} (hG : IsEndstateTrained S C G)
    (hG' : IsEndstateTrained S C G') : S * G = S * G' :=
  vec_inj.1 <| WithLp.toLp_injective 2 <|
    ((isEndstateTrained_iff_predicted_eq_starProjection S C G).1 hG).trans
      ((isEndstateTrained_iff_predicted_eq_starProjection S C G').1 hG').symm

/-- All trained matrices under positive weights produce the same predicted forms `SG` on the
training events, so predictions are unique even when `G` is not. -/
theorem IsTrained.mul_eq (hq : ∀ i, 0 < q i) {G' : Matrix δ κ ℝ}
    (hG : IsTrained S C q G) (hG' : IsTrained S C q G') : S * G = S * G' := by
  classical
  have h := mul_eq_of_isEndstateTrained ((isEndstateTrained_diagonal_sqrt_mul_iff S C q G).2 hG)
    ((isEndstateTrained_diagonal_sqrt_mul_iff S C q G').2 hG')
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_assoc, diagonal_mul] at hij
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (NNReal.coe_pos.2 (hq i))).ne' hij

theorem IsTrained.vecMul_eq_of_mem_span (hq : ∀ i, 0 < q i) {G' : Matrix δ κ ℝ}
    (hG : IsTrained S C q G) (hG' : IsTrained S C q G') {s : δ → ℝ}
    (hs : s ∈ Submodule.span ℝ (Set.range S.row)) : s ᵥ* G = s ᵥ* G' := by
  classical
  have hker : Submodule.span ℝ (Set.range S.row) ≤ LinearMap.ker (toLin' (G - G')ᵀ) :=
    Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun i ↦ by
      simp only [SetLike.mem_coe, LinearMap.mem_ker, toLin'_apply, mulVec_transpose,
        Matrix.vecMul_sub, sub_eq_zero]
      exact congrFun (hG.mul_eq hq hG') i
  have h0 := hker hs
  rw [LinearMap.mem_ker, toLin'_apply, mulVec_transpose, Matrix.vecMul_sub, sub_eq_zero] at h0
  exact h0

theorem IsTrained.add_of_mul_eq_zero (hG : IsTrained S C q G) {H : Matrix δ κ ℝ}
    (hH : S * H = 0) : IsTrained S C q (G + H) := by
  have : weightedLoss S C q (G + H) = weightedLoss S C q G := by
    simp [weightedLoss, Matrix.mul_add, hH]
  simpa only [IsTrained, isMinOn_univ_iff, this] using hG

theorem IsTrained.exists_vecMul_ne [Nonempty κ] (hG : IsTrained S C q G) {s : δ → ℝ}
    (hs : s ∉ Submodule.span ℝ (Set.range S.row)) :
    ∃ G' : Matrix δ κ ℝ, IsTrained S C q G' ∧ s ᵥ* G ≠ s ᵥ* G' := by
  classical
  obtain ⟨j⟩ := ‹Nonempty κ›
  obtain ⟨φ, hφ, hφs⟩ :
      ∃ φ ∈ (Submodule.span ℝ (Set.range S.row)).dualAnnihilator, φ s ≠ 0 := by
    simpa using mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ s).mp hs
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ δ).surjective φ
  have hvec (x : δ → ℝ) : x ᵥ* vecMulVec v (Pi.single j 1 : κ → ℝ) =
      dotProductEquiv ℝ δ v x • Pi.single j 1 := by
    rw [vecMul_vecMulVec, dotProductEquiv_apply_apply, dotProduct_comm]
  have hSH : S * vecMulVec v (Pi.single j 1 : κ → ℝ) = 0 := ext_row fun i ↦ by
    rw [row_mul_eq_vecMul_row, hvec,
      (Submodule.mem_dualAnnihilator _).1 hφ _ (Submodule.subset_span ⟨i, rfl⟩), zero_smul]; rfl
  exact ⟨G + vecMulVec v (Pi.single j 1), hG.add_of_mul_eq_zero hSH,
    fun h ↦ hφs (by simpa [Matrix.vecMul_add, hvec] using h.symm)⟩

/-- The trained matrix is uniquely determined exactly when the experienced meanings span the
meaning space, the coordinate-free form of `S` having full column rank. The papers assume this
silently in writing the closed form `(SᵀS)⁻¹SᵀC`. -/
theorem existsUnique_isTrained_iff [Nonempty κ] (hq : ∀ i, 0 < q i) :
    (∃! G : Matrix δ κ ℝ, IsTrained S C q G) ↔ Submodule.span ℝ (Set.range S.row) = ⊤ := by
  classical
  refine ⟨fun ⟨G, hG, huniq⟩ ↦ Submodule.eq_top_iff'.2 fun s ↦ by_contra fun hs ↦ ?_,
    fun htop ↦ ?_⟩
  · obtain ⟨G', hG', hne⟩ := hG.exists_vecMul_ne hs
    exact hne (by rw [huniq G' hG'])
  · obtain ⟨G, hG⟩ := exists_isTrained S C q
    refine ⟨G, hG, fun G' hG' ↦ ext_row fun k ↦ ?_⟩
    simpa using hG'.vecMul_eq_of_mem_span hq hG (Submodule.eq_top_iff'.mp htop (Pi.single k 1))

/-- A form coordinate that is a linear functional of the meanings is reproduced exactly, since its
residual is then a linear functional of the meanings as well, and so orthogonal to itself. -/
theorem IsTrained.mul_apply_eq_of_decodable (hq : ∀ i, 0 < q i) (hG : IsTrained S C q G)
    {j₀ : κ} {w : (δ → ℝ) →ₗ[ℝ] ℝ} (hw : ∀ i, w (S i) = C i j₀) (i : ι) :
    (S * G) i j₀ = C i j₀ := by
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
theorem IsTrained.centerMass_vecMul_eq_of_decodable [DecidableEq ι] (hG : IsTrained S C q G)
    {P : Finset ι} {w : (δ → ℝ) →ₗ[ℝ] ℝ} (hw : ∀ i, w (S i) = if i ∈ P then 1 else 0) :
    P.centerMass (fun i ↦ (q i : ℝ)) S.row ᵥ* G = P.centerMass (fun i ↦ (q i : ℝ)) C.row := by
  have h := hG.sum_smul_mul_eq_of_decodable hw
  rw [← vecMulLinear_apply]
  simp only [Finset.centerMass, map_smul, map_sum]
  simp only [vecMulLinear_apply, row_apply', ← mul_apply_eq_vecMul, h]

/-- A mapping trained at the endstate sends the centroid of a linearly decodable set's meanings to
the centroid of its forms ([chuang-bell-tseng-baayen-2026] §3.4, [lu-chuang-baayen-2026] §4.4). -/
theorem IsEndstateTrained.centroid_vecMul_eq_of_decodable [DecidableEq ι]
    (hG : IsEndstateTrained S C G) {P : Finset ι} (hP : P.Nonempty) {w : (δ → ℝ) →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (S i) = if i ∈ P then 1 else 0) :
    P.centroid ℝ S.row ᵥ* G = P.centroid ℝ C.row := by
  simpa [P.centroid_eq_centerMass hP, Finset.centerMass, ← Finset.smul_sum, hP.card_ne_zero] using
    hG.centerMass_vecMul_eq_of_decodable hw

end

end DiscriminativeLexicon
