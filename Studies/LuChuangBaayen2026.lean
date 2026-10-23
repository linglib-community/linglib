module

public import Linglib.Core.LinearAlgebra.AffineSpace.Centroid
public import Linglib.Processing.DiscriminativeLexicon.Training
public import Studies.ChuangEtAl2026

/-!
# Lu, Chuang and Baayen (2026): The realization of tones in spontaneous spoken Taiwan Mandarin

Lu, Chuang and Baayen survey the f0 contours of disyllabic words across the twenty tone patterns
of Taiwan Mandarin in Fon's corpus of spontaneous speech, and find that word and sense outweigh
tone pattern as predictors of the contour (§3.4). Following Chuang, Bell, Tseng and Baayen, they
fit a linear map from 768-dimensional contextualized embeddings to 100-sample normalized pitch
contours by least squares on the training tokens (§4.3), the method of Gahl and Baayen. The map
sends the centroid embedding of each tone pattern to a contour close to the one a generalized
additive model assigns the pattern (§4.4, Fig. 9).

The centroid of a tone pattern is a mean of means. The embeddings of each word type's tokens are
averaged, and these word-type centroids are averaged in turn, so that every word type weighs
equally (§4.4). Least squares fits the mean contour of every word type that is linearly decodable
from the embeddings, and linearity carries the outer average, so the map sends the pattern's
centroid embedding exactly to the same mean of means of its training contours.

The discussion (§5) answers the tone-sandhi objection on two grounds. T3-T3 and T2-T3 are
neutralized in Taiwan Mandarin, as the authors' earlier study shows, and the model predicts forms
from meanings, never forms from forms, so the tone-pattern contours emerge without the model
being told the patterns. Xu's laboratory contours match the predicted ones for several patterns
(Fig. 11).

## Main statements

* `LuChuangBaayen2026.production_centroid_centroid_eq_of_decodable`: if every word type of a tone
  pattern is linearly decodable from the embeddings, the least-squares map sends the pattern's
  centroid embedding to the centroid of its word types' mean training contours.

## Implementation notes

* A tone pattern is the set of its word types, and a word type the set of tokens carrying its
  label.
* Fig. 9 compares the predicted contours with those of the additive model, not with the averaged
  training contours, so the similarity the paper reports is approximate. The additive models and
  the nearest-neighbour accuracies are not represented.

## References

* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *The realization of tones in spontaneous spoken Taiwan
  Mandarin: a corpus-based survey and theory-driven computational modeling*
  (2026)][lu-chuang-baayen-2026]
* [Y. Lu, Y.-Y. Chuang and R. H. Baayen, *Form and meaning co-determine the realization of tone
  in Taiwan Mandarin spontaneous speech* (2024)][lu-chuang-baayen-2024]
* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [J. Fon, *A preliminary construction of Taiwan Southern Min spontaneous speech corpus*
  (2004)][fon-2004]
* [Y. Xu, *Contextual tonal variations in Mandarin* (1997)][xu-1997]
-/

@[expose] public section

namespace LuChuangBaayen2026

open DiscriminativeLexicon ChuangEtAl2026 Finset Matrix

/-- The paper samples 100 f0 values per token in normalized time, centered and scaled per
token (§4.1). -/
abbrev PitchSampleCount : ℕ := 100

/-- If every word type is trained and linearly decodable, a least-squares `G` sends a tone pattern's
centroid embedding to its types' mean contour average (§4.4, §4.2, Fig. 9,
[chuang-bell-tseng-baayen-2026]). -/
theorem production_centroid_centroid_eq_of_decodable {m : ℕ} {W : Type*} [DecidableEq W]
    {data : TrainingExperience m PitchSampleCount CKIPGPT2HiddenDim}
    {G : Matrix (Fin CKIPGPT2HiddenDim) (Fin PitchSampleCount) ℝ} (hG : IsELTrained data G)
    (word : Fin m → W) {T : Finset W} (hT : T.Nonempty) (hne : ∀ τ ∈ T, ∃ i, word i = τ)
    (hdec : ∀ τ ∈ T, ∃ ℓ : ContextualEmbedding →ₗ[ℝ] ℝ,
      ∀ i, ℓ (data.S i) = if word i = τ then 1 else 0) :
    (T.centroid ℝ fun τ ↦ (univ.filter (word · = τ)).centroid ℝ data.S.row) ᵥ* G =
      T.centroid ℝ fun τ ↦ (univ.filter (word · = τ)).centroid ℝ data.C.row := by
  rw [centroid_vecMul hT, centroid_def, centroid_def]
  refine affineCombination_congr _ (fun _ _ ↦ rfl) fun τ hτ ↦ ?_
  obtain ⟨ℓ, hℓ⟩ := hdec τ hτ
  exact hG.centroid_vecMul_eq_of_decodable (by simpa [filter_nonempty_iff] using hne τ hτ)
    (by simpa using hℓ)

end LuChuangBaayen2026
