module

public import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Chuang, Bell, Tseng and Baayen (2026): Word-specific tonal realizations in Mandarin

The pitch contour of a Mandarin disyllabic word is usually taken to realize the lexical tones of
its syllables under constraints such as intonation, coarticulation and speech rate. Chuang, Bell,
Tseng and Baayen add the token's meaning in context as a further determinant. On the 3,778
rise–fall (T2–T4) tokens of 51 word types in Fon's corpus of spontaneous Taiwan Mandarin, a
generalized additive model with a by-word smooth beats the segmental controls combined (§2.6). A
discriminative lexicon trained on pairs of 50-sample normalized contours (§3.2) and
768-dimensional contextualized embeddings (§3.1) predicts word type from contour and contour from
embedding an order of magnitude above chance (§3.3–3.4).

The contour that the linear production map produces from a word's centroid embedding closely
resembles the average of that word's training contours (Fig. 18), and the centroid of all tokens
produces the unmodulated rise–fall contour (§3.4.2). The paper reads this as isomorphy between
the space of contours and the space of embeddings, against the dual articulation it attributes
to Martinet (§4). The file accordingly works on continuous f0 vectors rather than on discrete
tones.

## Main statements

* `ChuangEtAl2026.production_mul_comprehension_ne_one`: no linear map takes the
  fifty-dimensional contour space onto the 768-dimensional embedding space, so no comprehension
  matrix inverts production.
* `ChuangEtAl2026.production_centroid_eq_of_decodable`: a least-squares-trained production matrix
  sends the centroid of a word type's embeddings to the average of its training contours
  whenever membership in the word type is a linear functional of the embeddings.
* `ChuangEtAl2026.production_centroid_univ_eq`: the centroid of all tokens produces the
  grand-mean training contour.

## Implementation notes

* A word type is the set of tokens carrying its corpus label (§1, §2.2). Linear decodability
  idealizes the distinct word-type regions of Fig. 14.
* The additive models, the nearest-neighbour accuracies and the residual network ResLDL are not
  represented.

## References

* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal
  realizations in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [J. Fon, *A preliminary construction of Taiwan Southern Min spontaneous speech corpus*
  (2004)][fon-2004]
-/

@[expose] public section

namespace ChuangEtAl2026

open DiscriminativeLexicon Finset Matrix

/-- The fifty f0 values sampled per token at equally spaced points of normalized time
(§3.2). -/
abbrev TaiwanMandarinPitchSampleCount : ℕ := 50

/-- The dimension of CKIP's GPT-2 character vectors (§3.1). -/
abbrev CKIPGPT2HiddenDim : ℕ := 768

/-- A pitch contour consists of the fifty samples, centered by the token's mean and scaled by its
range (§3.2), so it is a shape rather than a pitch or an amplitude. -/
abbrev PitchContour : Type := FormVector TaiwanMandarinPitchSampleCount

/-- A contextualized embedding is the mean of the GPT-2 vectors of a token's two characters given
the preceding context, the current utterance up to the token and the one before it (§3.1). -/
abbrev ContextualEmbedding : Type := MeaningVector CKIPGPT2HiddenDim

/-! ### Comprehension from fifty dimensions (§3.3)

The comprehension matrix `F` predicts a `ContextualEmbedding` `cF` from a `PitchContour` `c`,
and the production matrix `G` a contour `sG` from an embedding `s` (§3.3–3.4). -/

-- §3.3.2, fn. 29
theorem comprehension_not_surjective
    (F : Matrix (Fin TaiwanMandarinPitchSampleCount) (Fin CKIPGPT2HiddenDim) ℝ) :
    ¬ Function.Surjective F.vecMulLinear := fun h ↦ by
  simpa [CKIPGPT2HiddenDim, TaiwanMandarinPitchSampleCount] using
    LinearMap.finrank_le_finrank_of_surjective (f := F.vecMulLinear) h

/-- No comprehension matrix inverts production (fn. 29). -/
theorem production_mul_comprehension_ne_one
    (G : Matrix (Fin CKIPGPT2HiddenDim) (Fin TaiwanMandarinPitchSampleCount) ℝ)
    (F : Matrix (Fin TaiwanMandarinPitchSampleCount) (Fin CKIPGPT2HiddenDim) ℝ) :
    G * F ≠ 1 := fun h ↦
  comprehension_not_surjective F fun s ↦ ⟨s ᵥ* G, by simp [vecMul_vecMul, h]⟩

/-! ### Word-centroid contours (§3.4) -/

variable {m : ℕ} {W : Type*} [DecidableEq W]
  {data : TrainingExperience m TaiwanMandarinPitchSampleCount CKIPGPT2HiddenDim}
  {G : Matrix (Fin CKIPGPT2HiddenDim) (Fin TaiwanMandarinPitchSampleCount) ℝ}

/-- If word-type membership is a linear functional of the embeddings, a least-squares production
matrix sends a word type's embedding centroid to its mean training contour (§1, §2.2, Fig. 18). -/
theorem production_centroid_eq_of_decodable (hG : IsELTrained data G) (word : Fin m → W)
    {w : W} (hw : ∃ i, word i = w) {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ}
    (hℓ : ∀ i, ℓ (data.S i) = if word i = w then 1 else 0) :
    (univ.filter (word · = w)).centroid ℝ data.S.row ᵥ* G =
      (univ.filter (word · = w)).centroid ℝ data.C.row :=
  hG.centroid_vecMul_eq_of_decodable (by simpa [filter_nonempty_iff] using hw)
    (by simpa using hℓ)

/-- If some linear functional is constant on the training embeddings, the centroid of all embeddings
produces the grand-mean contour (§3.4.2, Fig. 1). -/
theorem production_centroid_univ_eq [NeZero m] (hG : IsELTrained data G)
    {ℓ : ContextualEmbedding →ₗ[ℝ] ℝ} (hℓ : ∀ i, ℓ (data.S i) = 1) :
    univ.centroid ℝ data.S.row ᵥ* G = univ.centroid ℝ data.C.row :=
  hG.centroid_vecMul_eq_of_decodable ⟨0, mem_univ 0⟩ (by simpa using hℓ)

end ChuangEtAl2026
