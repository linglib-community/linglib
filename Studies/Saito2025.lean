module

public import Linglib.Processing.DiscriminativeLexicon.Training

/-!
# Saito, Tomaschek & Baayen (2025): Interaction of Frequency and Inflectional Status

This file formalizes the paper's discriminative-lexicon account of a frequency effect that
reverses with inflectional status. In tongue-position data from the Karl Eberhards Corpus of
spontaneous southern German, high-frequency non-inflected words show articulatory reduction
of the stem vowel while high-frequency inflected words do not, and the paper replaces the
binary inflectional-status predictor by the semantic support that a word's meaning lends to
its suffix triphone in a trained discriminative lexicon, which improves the tongue-position
model with one fewer degree of freedom. The model is the substrate's production matrix `G` from
the paper's word2vec meaning vectors to its triphone form vectors, and when the suffix triphone
is linearly decodable from meanings, training alone gives inflected words strictly greater
suffix support than non-inflected ones, the direction of the paper's contrast
(`semSupSuffix_lt`). The
result bears on production models with a morpheme layer such as WEAVER++
([levelt-roelofs-meyer-1999], [roelofs-1997]), since the apparent morphological-boundary
effect is carried by inflectional semantics.

## Implementation notes

The paper's positional measures, the semantic support for the vowel and suffix triphones, are
entries of the predicted form matrix `Ĉ = SG` at the two triphone columns, (3) and (4), the
substrate's `semanticSupport` at a coordinate indicator; the paper's triphone indexing is not
reproduced. The comprehension-side measures, which use the matrix `F` solving `CF = S`, and the
generalized additive models of the articulatory study are not formalized.

## References

* [saito-tomaschek-baayen-2025]
* [baayen-2019]
* [heitmeier-chuang-baayen-2026]
* [levelt-roelofs-meyer-1999]
* [roelofs-1997]
* [muller-2015]
-/

@[expose] public section

namespace Saito2025

open DiscriminativeLexicon

/-- The paper's CELEX-derived form matrix has `TriphoneCount` triphones. -/
abbrev TriphoneCount : ℕ := 14404

/-- The pretrained German word2vec embeddings of [muller-2015] have `Word2VecGermanDim`
dimensions. -/
abbrev Word2VecGermanDim : ℕ := 300

/-- When suffix triphones are linearly decodable from meanings, a trained production matrix gives
suffixed words strictly greater suffix support `Ĉ i s` (4). -/
theorem semSupSuffix_lt {m : ℕ}
    {data : TrainingExperience m TriphoneCount Word2VecGermanDim} {q : FrequencyVector m}
    {G : Matrix (Fin Word2VecGermanDim) (Fin TriphoneCount) ℝ} (hG : IsTrained data q G)
    (hq : ∀ i, 0 < q i) {s : Fin TriphoneCount} {w : MeaningVector Word2VecGermanDim →ₗ[ℝ] ℝ}
    (hw : ∀ i, w (data.S i) = data.C i s) {i k : Fin m} (hik : data.C i s < data.C k s) :
    (data.S * G) i s < (data.S * G) k s := by
  rwa [hG.mul_apply_eq_of_decodable hq hw i, hG.mul_apply_eq_of_decodable hq hw k]

end Saito2025
