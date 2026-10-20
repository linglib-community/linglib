module

public import Mathlib.Basic.Real.Basic

/-!
# The discriminative lexicon

This file sets up the linear discriminative lexicon, the linear form of the Discriminative
Lexicon Model of Baayen, Chuang, Shafaei-Bajestan and Blevins.

The model relates form and meaning by learned mappings between vector spaces rather than by an
inventory of stored, decomposed form–meaning entries. A word's form is a row vector of cue values
and its meaning a row vector of semantic dimensions, and the experienced words stack them into a
form matrix `C` and a semantic matrix `S`. In linear discriminative learning, as Heitmeier, Chuang
and Baayen call the original formulation, both mappings are matrices acting on row vectors:
comprehension predicts meanings `Ŝ = CF` and production predicts forms `Ĉ = SG`. The two
matrices are estimated separately from the same experience, at the endstate of learning, under
frequency-informed learning, or incrementally (`DiscriminativeLexicon.IsTrained`), and each
study uses the one its measures need. The deep mappings that replace or augment the linear ones,
DDL and ResLDL, are not formalized.

## Main definitions

* `FormVector n`, `MeaningVector d`: the real row vectors `Fin n → ℝ` and `Fin d → ℝ` of forms
  and meanings. A production matrix is a `Matrix (Fin d) (Fin n) ℝ`, sending a meaning `s` to
  the predicted form `s ᵥ* G`.

## Implementation notes

The mappings are the papers' matrices rather than bundled linear maps, so the studies state the
papers' equations directly; `Matrix.vecMulLinear` gives the linear map where linear algebra needs
one.

## References

* [R. H. Baayen, Y.-Y. Chuang, E. Shafaei-Bajestan and J. P. Blevins, *The discriminative
  lexicon* (2019)][baayen-2019]
* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
* [M. Heitmeier, V. Schmidt, H. P. A. Lensch and R. H. Baayen, *Is deeper always better?*
  (2025)][heitmeier-schmidt-lensch-baayen-2025]
* [Y.-Y. Chuang, M. J. Bell, Y.-H. Tseng and R. H. Baayen, *Word-specific tonal realizations
  in Mandarin* (2026)][chuang-bell-tseng-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

/-- A **form vector** has `formDim` real coordinates, one per cue or sample. -/
abbrev FormVector (formDim : ℕ) : Type := Fin formDim → ℝ

/-- A **meaning vector** has `meaningDim` real coordinates, one per semantic dimension. -/
abbrev MeaningVector (meaningDim : ℕ) : Type := Fin meaningDim → ℝ

end DiscriminativeLexicon
