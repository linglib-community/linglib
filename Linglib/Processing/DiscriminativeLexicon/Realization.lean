module

public import Linglib.Morphology.Realization
public import Linglib.Morphology.Paradigm.Analogy
public import Linglib.Processing.DiscriminativeLexicon.Coding
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The discriminative lexicon as a realization

This file presents the form table of a production matrix as a `Morphology.Realization`, so that
the discriminative lexicon stands beside Distributed Morphology, Paradigm Function Morphology and
nanosyntax on the same paradigm data.

A production matrix realizes a lexeme at a paradigm cell as the form it predicts from the cell's
meaning. Which meaning is used is the speaker's choice in Table 12.7 of Heitmeier, Chuang and
Baayen, either an empirical embedding of the word or a meaning constructed from the lexeme's
vector and the inflectional function's vector (`imputed`), the meaning of *walked* as the meaning
of *walk* plus a past-tense vector. Either way the realization is total and univalent. The model
itself posits no stems or exponents; its lexeme and inflectional function are semantic
primitives, and the realization interface is linglib's comparison device rather than the
theory's ontology. Imputed meanings are analogically regular (`Morphology.IsAnalogicallyRegular`),
the shift from *walk* to *walks* being the shift from *jump* to *jumps*, and a production matrix
carries regular meanings to regular forms, so over imputed semantics the form table is regular,
which `Studies/HeitmeierChuangBaayen2026` turns into an equivalence; over word-specific
embeddings it need not be.

## Main definitions

* `paradigm G s`: the form table of a production matrix `G` over a meaning assignment `s`.
* `realization G s`: the same table as a `Morphology.Realization`.

## Main results

* `realization_isTotal`, `realization_isUnivalent`: the realization is total and univalent.
* `isAnalogicallyRegular_imputed`: imputed meanings are analogically regular.
* `isAnalogicallyRegular_paradigm`: a production matrix preserves analogical regularity.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

open Matrix Morphology

variable {n d : ℕ} {L Cell : Type*} (G : Matrix (Fin d) (Fin n) ℝ)
  (s : L → Cell → MeaningVector d)

/-- The form table of a production matrix over a meaning assignment lists the predicted form at
the meaning of each lexeme at each cell. -/
def paradigm (l : L) (c : Cell) : FormVector n := s l c ᵥ* G

@[simp] theorem paradigm_apply (l : L) (c : Cell) : paradigm G s l c = s l c ᵥ* G := rfl

/-- A production matrix is a `Morphology.Realization` in which a lexeme at a cell is realised by
the one form it predicts. -/
def realization : Realization L Cell (FormVector n) := ⟨fun l c ↦ {paradigm G s l c}⟩

@[simp] theorem realization_realize (l : L) (c : Cell) :
    (realization G s).realize l c = {paradigm G s l c} := rfl

theorem realization_isTotal : (realization G s).IsTotal := fun _ _ ↦ Finset.singleton_nonempty _

theorem realization_isUnivalent : (realization G s).IsUnivalent := fun _ _ ↦
  (Finset.card_singleton _).le

/-- Imputed meanings are analogically regular: the shift between two cells is the difference of
their vectors for every lexeme (eqs. 1.10–1.12). -/
theorem isAnalogicallyRegular_imputed {V : Type*} [AddCommGroup V] (σ : L → V) (ε : Cell → V) :
    IsAnalogicallyRegular (imputed σ ε) := by
  rw [show imputed σ ε = _ from funext₂ (imputed_apply σ ε)]
  exact isAnalogicallyRegular_add σ ε

/-- A production matrix carries analogically regular meanings to analogically regular forms. -/
theorem isAnalogicallyRegular_paradigm {s : L → Cell → MeaningVector d}
    (h : IsAnalogicallyRegular s) : IsAnalogicallyRegular (paradigm G s) :=
  h.map G.vecMulLinear

end DiscriminativeLexicon
