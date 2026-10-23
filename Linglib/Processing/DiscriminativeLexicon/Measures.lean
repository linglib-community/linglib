module

public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Semantic support in the discriminative lexicon

This file defines the semantic support measures of a linear discriminative lexicon.

A production matrix `G` predicts the form of a meaning `s` as the row vector `ĉ = sG`. The
*semantic support* that a form vector `c` receives from `s` is the dot product `ĉ ⬝ᵥ c` of the
predicted form with `c`. Since this is linear in `s` and in `c`, it is the bilinear form of `G`.
Gahl and Baayen tabulate it over all pairs of words as the support matrix `T = ĈCᵀ` and call its
diagonal, the support a word's own cue vector receives from its meaning, *semantic support for
form*; Heitmeier, Chuang and Baayen use the same measure for lexical decision. Saito, Tomaschek
and Baayen instead read off single coordinates of `ĉ`, the support for one cue, and sum them over
a word's cues.

## Main definitions

* `semanticSupport G`: the bilinear map `(s, c) ↦ sG ⬝ᵥ c` of a production matrix `G`.

## Main results

* `semanticSupport_single`: the support for a single coordinate is the predicted value there.

## References

* [S. Gahl and R. H. Baayen, *Time and thyme again* (2024)][gahl-baayen-2024]
* [M. Saito, F. Tomaschek and R. H. Baayen, *Interaction of frequency and inflectional status*
  (2025)][saito-tomaschek-baayen-2025]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

open Matrix

noncomputable section

variable {n d : ℕ} (G : Matrix (Fin d) (Fin n) ℝ)

/-- The **semantic support** that a form vector `c` receives from a meaning `s` under a
production matrix `G` is the dot product of the predicted form `sG` with `c`, so it is the
bilinear form of `G`. -/
def semanticSupport : MeaningVector d →ₗ[ℝ] FormVector n →ₗ[ℝ] ℝ := toLinearMap₂' ℝ G

@[simp] theorem semanticSupport_apply (s : MeaningVector d) (c : FormVector n) :
    semanticSupport G s c = (s ᵥ* G) ⬝ᵥ c := by
  rw [semanticSupport, toLinearMap₂'_apply', dotProduct_mulVec]

theorem semanticSupport_single (s : MeaningVector d) (j : Fin n) :
    semanticSupport G s (Pi.single j 1) = (s ᵥ* G) j := by
  simp

end

end DiscriminativeLexicon
