module

public import Linglib.Phonology.Subregular.Boundary
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Form and meaning coding for the discriminative lexicon

This file defines how forms and meanings enter the discriminative lexicon of Heitmeier, Chuang
and Baayen. A form's cues are the `n`-grams of the string padded with one boundary symbol on each
side, one symbol whatever `n` rather than the `n − 1` of strictly local grammars (`boundary`), and
its row of the form matrix `C` is the [indicator of its cues](##cueVector). A meaning is a
multiset of semantic primitives, a lexeme with its inflectional functions and word class, and
[conceptualization](##conceptualize) sums the primitives' vectors. Conceptualizing with the rows
of a matrix `W` is [the primitives' multiple-hot row times `W`](##conceptualize_row), the form in
which vectors for the primitives are imputed from word embeddings by regression.

## References

* [M. Heitmeier, Y.-Y. Chuang and R. H. Baayen, *The Discriminative Lexicon*
  (2026)][heitmeier-chuang-baayen-2026]
-/

@[expose] public section

namespace DiscriminativeLexicon

open Matrix

/-! ### Form side -/

variable {Sym κ : Type*}

/-- The `k`-gram cues of a form are the `k`-factors of the string padded with one boundary
symbol on each side, `#aa aap ap#` for *aap* at `k = 3`, as JudiLing's `make_cue_matrix` computes
them with `grams = k` (§4.1). -/
def cues (k : ℕ) (w : List Sym) : Set (Augmented Sym) := {c | c <:+: boundary 2 w ∧ c.length = k}

instance [DecidableEq Sym] (k : ℕ) (w : List Sym) : DecidablePred (· ∈ cues k w) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The row of the form matrix `C` for the form `w` is the indicator of its cues over the cue
inventory `inv`, a multiple-hot row of ones and zeros ((4.1), (4.2), Background 4.2). -/
noncomputable def cueVector (k : ℕ) (inv : κ → Augmented Sym) (w : List Sym) : κ → ℝ :=
  (inv ⁻¹' cues k w).indicator 1

theorem cueVector_apply [DecidableEq Sym] (k : ℕ) (inv : κ → Augmented Sym) (w : List Sym)
    (j : κ) : cueVector k inv w j = if inv j ∈ cues k w then 1 else 0 := by
  split_ifs with h
  exacts [Set.indicator_of_mem h 1, Set.indicator_of_notMem h 1]

/-! ### Meaning side -/

variable {Prim A B V : Type*} [AddCommMonoid V]

/-- **Conceptualization** sends a multiset of semantic primitives to the sum of the primitives'
vectors, the meaning of *abrikozen* 'apricots' being the sum of the vectors of its lexeme, of
plurality and of being a noun ((5.3)–(5.5)). -/
def conceptualize (emb : Prim → V) : Multiset Prim →+ V :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom emb)

@[simp] theorem conceptualize_apply (emb : Prim → V) (ps : Multiset Prim) :
    conceptualize emb ps = (ps.map emb).sum := rfl

/-- Conceptualizing with the rows of `W` is the conceptualization with one-hot vectors (5.1),
which is the multiple-hot row of the matrix `L` of (5.2), times `W`. The book imputes vectors for
lexemes and inflectional functions as the rows of a `W` fitted to map `L` onto the word
embeddings (Code 5.9). -/
theorem conceptualize_row [Fintype Prim] [DecidableEq Prim] {δ : Type*} (W : Matrix Prim δ ℝ)
    (ps : Multiset Prim) : conceptualize W.row ps = conceptualize (Pi.single · 1) ps ᵥ* W := by
  induction ps using Multiset.induction_on with
  | empty => simp
  | cons p ps ih => simp_all [add_vecMul]

/-- The **imputed semantics** of a lexeme at a paradigm cell conceptualizes the lexeme together
with the cell, the sum of the lexeme's vector and the cell's ((5.3); the constructed
meaning-to-form route of Table 12.7, which §16.6 calls imputed embeddings for stems and
exponents). -/
def imputed (σ : A → V) (ε : B → V) (a : A) (b : B) : V :=
  conceptualize (Sum.elim σ ε) {Sum.inl a, Sum.inr b}

@[simp] theorem imputed_apply (σ : A → V) (ε : B → V) (a : A) (b : B) :
    imputed σ ε a b = σ a + ε b := by
  simp [imputed]

end DiscriminativeLexicon
