module

public import Linglib.Processing.DiscriminativeLexicon.Defs
public import Linglib.Phonology.Subregular.Boundary
public import Linglib.Core.Data.List.Factors
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Form and meaning coding for the discriminative lexicon

This file defines how linguistic objects enter the discriminative lexicon, following chapters 4
and 5 of Heitmeier, Chuang and Baayen.

A form is a string of symbols. Its cues are the `n`-grams of the string padded with one
boundary symbol on each side (`#a aa ap p#`, `#aa aap ap#`), and its row of the form matrix `C`
is the indicator of those cues over the cue inventory, so `C` holds only ones and zeros. The
padding is one boundary symbol whatever the width, unlike the `k − 1` symbols of strictly local
grammars (`boundary`), so the model's trigrams are not the 3-factors of subregular phonology. A
meaning is a multiset of atomic semantic primitives, a lexeme together with its inflectional
functions, and conceptualization builds its vector as the sum of the primitives' vectors, so
that a novel inflected word is conceptualized from known primitives. Conceptualization is
additive in the multiset by construction, which is what makes a linear mapping respect
proportional analogy (`Studies/HeitmeierChuangBaayen2026`).

## Main definitions

* `cues k w`: the `k`-gram cues of the string `w`.
* `multiHot inv p`: the indicator row over an inventory `inv` of the units satisfying `p`.
* `cueVector k inv w`: the row of `C` for `w`.
* `conceptualize emb`: the additive map from primitive multisets to meaning vectors.
* `imputed σ ε`: the meaning of a lexeme at a cell, the lexeme's vector plus the cell's.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

variable {Sym : Type*}

/-! ### Form side -/

/-- The `k`-gram cues of a form are the `k`-factors of the string padded with one boundary
symbol on each side, as JudiLing's `make_cue_matrix` computes them with `grams = k`. -/
def cues (k : ℕ) (w : List Sym) : List (Augmented Sym) := (boundary 2 w).kFactors k

/-- The multiple-hot row over an inventory `inv` marks with `1` the units satisfying `p`. -/
def multiHot {N : ℕ} {α : Type*} (inv : Fin N → α) (p : α → Prop) [DecidablePred p] :
    Fin N → ℝ :=
  fun j ↦ if p (inv j) then 1 else 0

/-- The row of the form matrix `C` for the form `w` is the indicator of its cues over the cue
inventory. -/
def cueVector [DecidableEq Sym] (k : ℕ) {N : ℕ} (inv : Fin N → Augmented Sym) (w : List Sym) :
    FormVector N :=
  multiHot inv (· ∈ cues k w)

/-! ### Meaning side -/

variable {Prim V : Type*} [AddCommMonoid V]

/-- **Conceptualization** sends a multiset of semantic primitives to the sum of the primitives'
vectors, additively in the multiset. -/
def conceptualize (emb : Prim → V) : Multiset Prim →+ V :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom emb)

@[simp] theorem conceptualize_apply (emb : Prim → V) (ps : Multiset Prim) :
    conceptualize emb ps = (ps.map emb).sum := rfl

/-- Conceptualizing a lexeme with one inflectional function gives the sum of their vectors, the
imputed additive semantics of a paradigm cell (eq. 5.3). -/
@[simp] theorem conceptualize_pair {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) :
    conceptualize (Sum.elim σ ε) {Sum.inl a, Sum.inr b} = σ a + ε b := by
  simp

/-- The **imputed semantics** of a lexeme at a cell is conceptualized from the lexeme's vector
and the inflectional function's vector (eq. 5.3; the constructed meaning-to-form route of
Table 12.7, which §16.6 calls imputed embeddings for stems and exponents). -/
def imputed {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) : V :=
  conceptualize (Sum.elim σ ε) {Sum.inl a, Sum.inr b}

@[simp] theorem imputed_apply {A B : Type*} (σ : A → V) (ε : B → V) (a : A) (b : B) :
    imputed σ ε a b = σ a + ε b :=
  conceptualize_pair σ ε a b

end DiscriminativeLexicon
