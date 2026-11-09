module

public import Linglib.Core.LinearAlgebra.Basis.VectorSpace
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Processing.DiscriminativeLexicon.Realization
public import Linglib.Processing.DiscriminativeLexicon.Training
public import Linglib.Processing.ErrorDrivenLearning

/-!
# Heitmeier, Chuang and Baayen (2026): The Discriminative Lexicon

This file formalizes the book's relation between linearity and regularity. Its linear
production maps handle inflectional systems with irregular forms: trained on empirical
embeddings, the English past-tense model produces 94% of the regular and 74% of the irregular
training verbs (§12.9). Meanings can instead be constructed, the meaning of *walked* as the
meaning of *walk* plus a past-tense vector (Table 12.7; conceptualization is vector addition,
(5.3)). Regularizing meanings this way gives "a reasonable approximation of a truly regular
system, and for such a system, linear mappings appear to work quite well" (§16.6, Table 16.2),
but when held-out verbs' meanings are built from the comprehended base form plus a past-tense
vector, "none of the irregular verbs was produced correctly" (§12.9).

The file states why in word-and-paradigm terms. Over imputed semantics, a lexeme vector plus an
inflectional-function vector, the form table of a linear map satisfies proportional analogy by
construction (`Morphology.IsAnalogicallyRegular`). So a table violating analogy is the paradigm
of no linear mapping and forces positive training loss, and when the lexeme and function
vectors are jointly independent a table is the paradigm of some linear mapping exactly when it
is analogically regular. Imputing the lexeme and function vectors from word embeddings by
regression, as the book does, returns [the regular table nearest the
embeddings](##isMinOn_imputed), and [the embeddings themselves exactly when they are
regular](##imputed_eq_iff_isAnalogicallyRegular), so imputation regularizes. Over word-specific
embeddings, by contrast, any table is the paradigm of some linear mapping as soon as the
embeddings are linearly independent, which fills the irregular-linear cell of Table 16.2. The English past tense at the book's letter-trigram coding
(§12.9) is the irregular table, *walk, walked* against *go, went*, with the forms taken from
the English fragment.

The file also relates the book's three ways of estimating a mapping. Incremental learning
updates the mapping at each usage event by the Widrow–Hoff rule, and the mappings of endstate
and frequency-informed learning are the matrices at which those updates cancel (§1.3, §6.2).

## Implementation notes

* The book describes endstate learning as the state incremental learning reaches after infinitely
  many epochs. At a fixed learning rate the updates cancel only in their frequency-weighted sum,
  and single events leave a matrix fixed only when it fits the experience exactly
  (`mul_eq_iff_forall_update_eq_self`).

## References

* [heitmeier-chuang-baayen-2026]
-/

@[expose] public section

namespace HeitmeierChuangBaayen2026

open DiscriminativeLexicon ErrorDrivenLearning Morphology Matrix Filter
open scoped Topology

variable {d n : ℕ} {Lexeme Cell : Type*}

/-! ### Imputed semantics -/

variable (σ : Lexeme → Fin d → ℝ) (ε : Cell → Fin d → ℝ)

/-- A table violating proportional analogy is the paradigm of no linear mapping over imputed
semantics, so irregular forms cannot be produced from constructed meanings (§12.9). -/
theorem not_exists_paradigm_eq_of_not_regular {f : ParadigmSystem Lexeme Cell (Fin n → ℝ)}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G (imputed σ ε) = f := by
  rintro ⟨G, rfl⟩
  exact hf (isAnalogicallyRegular_paradigm G (isAnalogicallyRegular_imputed σ ε))

/-! ### Interpolation -/

/-- Over linearly independent word-specific embeddings, any form table is the paradigm of some
linear mapping (Table 16.2, §12.9). -/
theorem exists_paradigm_eq_of_linearIndependent {s : ParadigmSystem Lexeme Cell (Fin d → ℝ)}
    (hs : LinearIndependent ℝ (Function.uncurry s))
    (f : ParadigmSystem Lexeme Cell (Fin n → ℝ)) :
    ∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G s = f := by
  obtain ⟨G, hG⟩ := hs.exists_linearMap_forall_apply_eq (Function.uncurry f)
  obtain ⟨G, rfl⟩ := toLinearMapRight'.surjective G
  exact ⟨G, Function.uncurry_injective (funext hG)⟩

/-- If the lexeme and inflectional-function vectors are jointly linearly independent, a table is a
linear paradigm over imputed semantics iff it is analogically regular (§16.6). -/
theorem exists_paradigm_imputed_eq_iff (hind : LinearIndependent ℝ (Sum.elim σ ε))
    (f : ParadigmSystem Lexeme Cell (Fin n → ℝ)) :
    (∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G (imputed σ ε) = f) ↔
      IsAnalogicallyRegular f := by
  refine ⟨fun ⟨G, hG⟩ ↦ hG ▸ isAnalogicallyRegular_paradigm G (isAnalogicallyRegular_imputed σ ε),
    fun hreg ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 hreg
  obtain ⟨G, hG⟩ := hind.exists_linearMap_forall_apply_eq (Sum.elim a b)
  obtain ⟨G, rfl⟩ := toLinearMapRight'.surjective G
  refine ⟨G, funext fun l ↦ funext fun c ↦ ?_⟩
  have hσ : σ l ᵥ* G = a l := hG (Sum.inl l)
  have hε : ε c ᵥ* G = b c := hG (Sum.inr c)
  simp [add_vecMul, hσ, hε, hab]

/-! ### Training on a paradigm -/

variable [Fintype Lexeme] [Fintype Cell]

/-- Irregularity forces positive training loss on a paradigm, whose semantic matrix holds the
imputed meanings and whose form matrix holds the form table, one row per lexeme and cell: no mapping
matrix fits a suppletive paradigm exactly, so every trained matrix carries residual error. -/
theorem pos_weightedLoss_of_not_regular {f : ParadigmSystem Lexeme Cell (Fin n → ℝ)}
    (hf : ¬ IsAnalogicallyRegular f) {q : Lexeme × Cell → NNReal} (hq : ∀ i, 0 < q i)
    (G : Matrix (Fin d) (Fin n) ℝ) :
    0 < weightedLoss (of (Function.uncurry (imputed σ ε))) (of (Function.uncurry f)) q G := by
  refine lt_of_le_of_ne (weightedLoss_nonneg _ _ _ _) (Ne.symm fun h0 ↦ ?_)
  refine not_exists_paradigm_eq_of_not_regular σ ε hf ⟨G, Function.uncurry_injective ?_⟩
  exact of.injective ((of_uncurry_paradigm G _).trans ((weightedLoss_eq_zero_iff _ _ _ _ hq).1 h0))

/-! ### Imputation

The book imputes vectors for lexemes and inflectional functions from word embeddings as the rows
of a mapping trained from the matrix `L` of the words' primitives onto the embeddings. -/

section Imputation

variable {ι Prim : Type*} [Fintype Prim] [DecidableEq Prim] {prims : ι → Multiset Prim}
  {S : Matrix ι (Fin d) ℝ} {q : ι → NNReal} {W : Matrix Prim (Fin d) ℝ}

/-- The matrix `L` marks each word's semantic primitives, its row conceptualizing their one-hot
vectors ((5.1), (5.2); Code 5.9). -/
def L (prims : ι → Multiset Prim) : Matrix ι Prim ℝ :=
  of fun i ↦ conceptualize (Pi.single · 1) (prims i)

@[simp] theorem L_mul_apply (prims : ι → Multiset Prim) (W : Matrix Prim (Fin d) ℝ) (i : ι) :
    (L prims * W) i = conceptualize W.row (prims i) :=
  (conceptualize_row W (prims i)).symm

-- Code 5.9
theorem forall_conceptualize_eq_iff [Fintype ι] (hq : ∀ i, 0 < q i)
    (hW : IsTrained (L prims) S q W) :
    (∀ i, conceptualize W.row (prims i) = S i) ↔
      ∃ v : Prim → Fin d → ℝ, ∀ i, conceptualize v (prims i) = S i := by
  refine ⟨fun h ↦ ⟨W.row, h⟩, fun ⟨v, hv⟩ i ↦ ?_⟩
  have hL : L prims * of v = S := ext_row fun i ↦ (L_mul_apply prims (of v) i).trans (hv i)
  rw [← L_mul_apply, hW.mul_eq hq (isTrained_of_mul_eq _ _ _ _ hL), hL]

end Imputation

theorem L_mul_eq_of_imputed [DecidableEq Lexeme] [DecidableEq Cell]
    (W : Matrix (Lexeme ⊕ Cell) (Fin d) ℝ) :
    L (fun w : Lexeme × Cell ↦ {.inl w.1, .inr w.2}) * W =
      of (Function.uncurry (imputed (W.row ∘ .inl) (W.row ∘ .inr))) := by
  ext ⟨l, c⟩ j; simp

/-- Imputing vectors for the lexemes and cells of a paradigm from its word embeddings
reconstructs the embeddings exactly iff they are analogically regular, imputed meanings being
regular by construction: imputation regularizes word meanings (Code 5.9, §16.6). -/
theorem imputed_eq_iff_isAnalogicallyRegular [DecidableEq Lexeme] [DecidableEq Cell]
    {s : ParadigmSystem Lexeme Cell (Fin d → ℝ)} {q : Lexeme × Cell → NNReal} (hq : ∀ i, 0 < q i)
    {W : Matrix (Lexeme ⊕ Cell) (Fin d) ℝ}
    (hW : IsTrained (L fun w ↦ {.inl w.1, .inr w.2}) (of (Function.uncurry s)) q W) :
    imputed (W.row ∘ .inl) (W.row ∘ .inr) = s ↔ IsAnalogicallyRegular s := by
  refine ⟨fun h ↦ h ▸ isAnalogicallyRegular_imputed _ _, fun hs ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 hs
  exact funext₂ fun l c ↦ (forall_conceptualize_eq_iff hq hW).2
    ⟨Sum.elim a b, fun ⟨l, c⟩ ↦ Eq.trans (by simp) (hab l c).symm⟩ (l, c)

/-- Imputed meanings are the analogically regular table nearest the word embeddings, in the
frequency-weighted squared distance that training minimizes: imputation gives the best regular
approximation of the embeddings (§16.6). -/
theorem isMinOn_imputed [DecidableEq Lexeme] [DecidableEq Cell]
    {s : ParadigmSystem Lexeme Cell (Fin d → ℝ)} {q : Lexeme × Cell → NNReal}
    {W : Matrix (Lexeme ⊕ Cell) (Fin d) ℝ}
    (hW : IsTrained (L fun w ↦ {.inl w.1, .inr w.2}) (of (Function.uncurry s)) q W) :
    IsMinOn (fun t : ParadigmSystem Lexeme Cell (Fin d → ℝ) ↦
        ∑ w, (q w : ℝ) * ((t w.1 w.2 - s w.1 w.2) ⬝ᵥ (t w.1 w.2 - s w.1 w.2)))
      {t | IsAnalogicallyRegular t} (imputed (W.row ∘ .inl) (W.row ∘ .inr)) := by
  have key (V : Matrix (Lexeme ⊕ Cell) (Fin d) ℝ) :
      weightedLoss (L fun w ↦ {.inl w.1, .inr w.2}) (of (Function.uncurry s)) q V =
        ∑ w, (q w : ℝ) * ((imputed (V.row ∘ .inl) (V.row ∘ .inr) w.1 w.2 - s w.1 w.2) ⬝ᵥ
          (imputed (V.row ∘ .inl) (V.row ∘ .inr) w.1 w.2 - s w.1 w.2)) := by
    rw [weightedLoss, L_mul_eq_of_imputed]; rfl
  refine isMinOn_iff.2 fun t ht ↦ ?_
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 ht
  have ht' : imputed ((of (Sum.elim a b)).row ∘ .inl) ((of (Sum.elim a b)).row ∘ .inr) = t :=
    funext₂ fun l c ↦ (imputed_apply _ _ l c).trans (hab l c).symm
  simpa only [key, ht'] using isMinOn_univ_iff.1 hW (of (Sum.elim a b))

/-! ### Incremental learning

Incremental learning updates a mapping one usage event at a time by the Widrow–Hoff rule. The
mapping matrices of endstate and frequency-informed learning are its equilibria. -/

section Incremental

variable {m : ℕ} (S : Matrix (Fin m) (Fin d) ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → NNReal)
  (G : Matrix (Fin d) (Fin n) ℝ) {η : ℝ}

-- §6.2
theorem update_example :
    update ((0.01 : ℝ) • 1) 1 ![0, 1] ![0.5, 0.5] !![1.2, -0.3; 0.4, 0.45] =
      !![1.2, -0.3; 0.401, 0.4505] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [update_apply, vecMul, dotProduct]

theorem sub_vecMul_update_smul_one (x : Fin d → ℝ) (y : Fin n → ℝ) :
    y - x ᵥ* update (η • 1) 1 x y G = (1 - η * x ⬝ᵥ x) • (y - x ᵥ* G) := by
  rw [sub_vecMul_update]
  ext j
  simp [mul_comm]

-- §6.2
theorem abs_sub_vecMul_update_lt_iff {x : Fin d → ℝ} {y : Fin n → ℝ} {j : Fin n}
    (hj : y j ≠ (x ᵥ* G) j) :
    |y j - (x ᵥ* update (η • 1) 1 x y G) j| < |y j - (x ᵥ* G) j| ↔ |1 - η * x ⬝ᵥ x| < 1 := by
  have h := congrFun (sub_vecMul_update_smul_one G x y (η := η)) j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h, abs_mul, mul_lt_iff_lt_one_left (abs_pos.2 (sub_ne_zero.2 hj))]

-- §6.2
theorem tendsto_vecMul_iterate_update_smul_one {x : Fin d → ℝ} (y : Fin n → ℝ)
    (h : |1 - η * x ⬝ᵥ x| < 1) :
    Tendsto (fun k ↦ x ᵥ* (update (η • 1) 1 x y)^[k] G) atTop (𝓝 y) :=
  tendsto_vecMul_iterate_update y G fun _ ↦ by simpa using h

/-- A mapping matrix is trained iff the frequency-weighted changes the usage events would make to it
cancel (§1.3). -/
theorem isTrained_iff_sum_update_sub_eq_zero (hη : η ≠ 0) :
    IsTrained S C q G ↔
      ∑ i, (q i : ℝ) • (update (η • 1) 1 (S i) (C i) G - G) = 0 := by
  have key : ∑ i, (q i : ℝ) • (update (η • 1) 1 (S i) (C i) G - G) =
      -η • (Sᵀ * diagonal (fun i ↦ (q i : ℝ)) * (S * G - C)) := by
    ext k j
    simp only [update_smul_one, add_sub_cancel_left, Matrix.sum_apply, Matrix.smul_apply,
      vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
    rw [mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_diagonal, transpose_apply, Matrix.sub_apply, mul_apply_eq_vecMul]
    ring
  rw [isTrained_iff, key, smul_eq_zero, neg_eq_zero, or_iff_right hη]

theorem mul_eq_iff_forall_update_eq_self (hη : η ≠ 0) (hS : ∀ i, S i ≠ 0) :
    S * G = C ↔ ∀ i, update (η • 1) 1 (S i) (C i) G = G := by
  refine ⟨fun h i ↦ update_eq_self_of_vecMul_eq _ _ (congrFun h i), fun h ↦ funext fun i ↦ ?_⟩
  rw [mul_apply_eq_vecMul]
  rcases (update_eq_self_iff ..).1 (h i) with h0 | h0
  · exact absurd (funext fun k ↦ by simpa [hη] using congrFun h0 k) (hS i)
  · exact (sub_eq_zero.1 (by simpa using h0)).symm

end Incremental

/-! ### The English past tense -/

/-- The two verbs of the book's contrast, regular *walk* and suppletive *go*, are the English
fragment's entries. -/
def verb : Fin 2 → English.Verbs.Verb := ![English.Verbs.walk, English.Verbs.go]

/-- *walk* is the first verb. -/
abbrev walk : Fin 2 := 0

/-- *go* is the second verb. -/
abbrev go : Fin 2 := 1

/-- The cells of the table are the base and past cells of the fragment's verb paradigm. -/
abbrev cells : Finset English.Verbs.Verb.Cell := {.base, .past}

/-- The base cell. -/
abbrev base : cells := ⟨.base, by decide⟩

/-- The past cell. -/
abbrev past : cells := ⟨.past, by decide⟩

/-- The letter-trigram cue inventory of the four forms; §12.9 codes forms as letter trigrams. -/
def trigram : Fin 13 → Augmented Char :=
  ![[none, some 'w', some 'a'], [some 'w', some 'a', some 'l'], [some 'a', some 'l', some 'k'],
    [some 'l', some 'k', none], [some 'l', some 'k', some 'e'], [some 'k', some 'e', some 'd'],
    [some 'e', some 'd', none], [none, some 'g', some 'o'], [some 'g', some 'o', none],
    [none, some 'w', some 'e'], [some 'w', some 'e', some 'n'], [some 'e', some 'n', some 't'],
    [some 'n', some 't', none]]

/-- The past-tense form table at the trigram coding takes each verb's form at each cell from
the fragment. -/
noncomputable def pastTense : ParadigmSystem (Fin 2) cells (Fin 13 → ℝ) := fun v c ↦
  cueVector 3 trigram ((verb v).realize c).toList

private theorem mem_cues_walk_iff (v : Fin 2) (c : English.Verbs.Verb.Cell) :
    trigram 0 ∈ cues 3 ((verb v).realize c).toList ↔ v = walk := by
  revert v c; decide +kernel

private theorem mem_cues_iff (v : Fin 2) (c : English.Verbs.Verb.Cell) :
    trigram 6 ∈ cues 3 ((verb v).realize c).toList ↔
      v = walk ∧ (c = .past ∨ c = .pastParticiple) := by
  revert v c; decide +kernel

/-- The English past tense violates proportional analogy, so no linear mapping produces it from
constructed meanings (§12.9). -/
theorem pastTense_not_regular : ¬ IsAnalogicallyRegular pastTense := fun h ↦ by
  have := congrFun (isAnalogicallyRegular_iff.1 h walk go past base) 6
  simp [pastTense, cueVector_apply, mem_cues_iff] at this

/-- The table is nonetheless analogical under arbitrary operations, each form identifying its
verb, so analogy under translations is strictly stronger. -/
example : IsAnalogical Set.univ pastTense ∧ ¬ IsAnalogicallyRegular pastTense := by
  refine ⟨isAnalogical_univ_iff.2 fun c _ ↦ Function.Injective.factorsThrough
    (fun v v' h ↦ ?_) _, pastTense_not_regular⟩
  have := congrFun h 0
  simp only [pastTense, cueVector_apply, mem_cues_walk_iff] at this
  revert this; fin_cases v <;> fin_cases v' <;> simp

end HeitmeierChuangBaayen2026
