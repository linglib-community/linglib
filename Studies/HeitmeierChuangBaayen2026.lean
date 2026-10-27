module

public import Linglib.Core.LinearAlgebra.LinearIndependent
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
is analogically regular. Over word-specific embeddings, by contrast, any table is the paradigm
of some linear mapping as soon as the embeddings are linearly independent, which fills the
irregular-linear cell of Table 16.2. The English past tense at the book's letter-trigram coding
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

variable (σ : Lexeme → MeaningVector d) (ε : Cell → MeaningVector d)

/-- A table violating proportional analogy is the paradigm of no linear mapping over imputed
semantics, so irregular forms cannot be produced from constructed meanings (§12.9). -/
theorem not_exists_paradigm_eq_of_not_regular {f : ParadigmSystem Lexeme Cell (FormVector n)}
    (hf : ¬ IsAnalogicallyRegular f) :
    ¬ ∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G (imputed σ ε) = f := by
  rintro ⟨G, rfl⟩
  exact hf (isAnalogicallyRegular_paradigm G (isAnalogicallyRegular_imputed σ ε))

/-! ### Interpolation -/

/-- Over linearly independent word-specific embeddings, any form table is the paradigm of some
linear mapping (Table 16.2, §12.9). -/
theorem exists_paradigm_eq_of_linearIndependent {s : ParadigmSystem Lexeme Cell (MeaningVector d)}
    (hs : LinearIndependent ℝ (Function.uncurry s))
    (f : ParadigmSystem Lexeme Cell (FormVector n)) :
    ∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G s = f := by
  obtain ⟨G, hG⟩ := hs.exists_linearMap_apply_eq (Function.uncurry f)
  obtain ⟨G, rfl⟩ := toLinearMapRight'.surjective G
  exact ⟨G, funext fun l ↦ funext fun c ↦ hG (l, c)⟩

/-- If the lexeme and inflectional-function vectors are jointly linearly independent, a table is a
linear paradigm over imputed semantics iff it is analogically regular (§16.6). -/
theorem exists_paradigm_imputed_eq_iff (hind : LinearIndependent ℝ (Sum.elim σ ε))
    (f : ParadigmSystem Lexeme Cell (FormVector n)) :
    (∃ G : Matrix (Fin d) (Fin n) ℝ, paradigm G (imputed σ ε) = f) ↔
      IsAnalogicallyRegular f := by
  refine ⟨fun ⟨G, hG⟩ ↦ hG ▸ isAnalogicallyRegular_paradigm G (isAnalogicallyRegular_imputed σ ε),
    fun hreg ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := isAnalogicallyRegular_iff_exists_add.1 hreg
  obtain ⟨G, hG⟩ := hind.exists_linearMap_apply_eq (Sum.elim a b)
  obtain ⟨G, rfl⟩ := toLinearMapRight'.surjective G
  refine ⟨G, funext fun l ↦ funext fun c ↦ ?_⟩
  have hσ : σ l ᵥ* G = a l := hG (Sum.inl l)
  have hε : ε c ᵥ* G = b c := hG (Sum.inr c)
  simp [add_vecMul, hσ, hε, hab]

/-! ### Training on a paradigm -/

variable [Fintype Lexeme] [Fintype Cell]

/-- A paradigm is a training experience whose semantic matrix holds the imputed meanings and
whose form matrix holds the form table, one row per lexeme and cell. -/
noncomputable def paradigmExperience (f : ParadigmSystem Lexeme Cell (FormVector n)) :
    TrainingExperience (Fintype.card (Lexeme × Cell)) n d :=
  let e := (Fintype.equivFin (Lexeme × Cell)).symm
  ⟨of (Function.uncurry (imputed σ ε) ∘ e), of (Function.uncurry f ∘ e)⟩

/-- Irregularity forces positive training loss, since no mapping matrix fits a suppletive
paradigm exactly and so every trained matrix carries residual error. -/
theorem pos_weightedLoss_of_not_regular {f : ParadigmSystem Lexeme Cell (FormVector n)}
    (hf : ¬ IsAnalogicallyRegular f) {q : FrequencyVector (Fintype.card (Lexeme × Cell))}
    (hq : ∀ i, 0 < q i) (G : Matrix (Fin d) (Fin n) ℝ) :
    0 < weightedLoss (paradigmExperience σ ε f) q G := by
  refine lt_of_le_of_ne (weightedLoss_nonneg _ _ _) (Ne.symm fun h0 ↦ ?_)
  have hint := (weightedLoss_eq_zero_iff _ _ _ hq).1 h0
  refine not_exists_paradigm_eq_of_not_regular σ ε hf
    ⟨G, funext fun l ↦ funext fun c ↦ funext fun j ↦ ?_⟩
  simpa [paradigmExperience, mul_apply, vecMul, dotProduct] using
    congrFun (congrFun hint ((Fintype.equivFin (Lexeme × Cell)) (l, c))) j

/-! ### Incremental learning

Incremental learning updates a mapping one usage event at a time by the Widrow–Hoff rule. The
mapping matrices of endstate and frequency-informed learning are its equilibria. -/

section Incremental

variable {m : ℕ} (data : TrainingExperience m n d) (q : FrequencyVector m)
  (G : Matrix (Fin d) (Fin n) ℝ) {η : ℝ}

-- §6.2
theorem update_example :
    update ((0.01 : ℝ) • 1) 1 ![0, 1] ![0.5, 0.5] !![1.2, -0.3; 0.4, 0.45] =
      !![1.2, -0.3; 0.401, 0.4505] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [update_apply, vecMul, dotProduct]

theorem sub_vecMul_update_smul_one (x : MeaningVector d) (y : FormVector n) :
    y - x ᵥ* update (η • 1) 1 x y G = (1 - η * x ⬝ᵥ x) • (y - x ᵥ* G) := by
  rw [sub_vecMul_update]
  ext j
  simp [mul_comm]

-- §6.2
theorem abs_sub_vecMul_update_lt_iff {x : MeaningVector d} {y : FormVector n} {j : Fin n}
    (hj : y j ≠ (x ᵥ* G) j) :
    |y j - (x ᵥ* update (η • 1) 1 x y G) j| < |y j - (x ᵥ* G) j| ↔ |1 - η * x ⬝ᵥ x| < 1 := by
  have h := congrFun (sub_vecMul_update_smul_one G x y (η := η)) j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [h, abs_mul, mul_lt_iff_lt_one_left (abs_pos.2 (sub_ne_zero.2 hj))]

-- §6.2
theorem tendsto_vecMul_iterate_update_smul_one {x : MeaningVector d} (y : FormVector n)
    (h : |1 - η * x ⬝ᵥ x| < 1) :
    Tendsto (fun k ↦ x ᵥ* (update (η • 1) 1 x y)^[k] G) atTop (𝓝 y) :=
  tendsto_vecMul_iterate_update y G fun _ ↦ by simpa using h

/-- A mapping matrix is trained iff the frequency-weighted changes the usage events would make to it
cancel (§1.3). -/
theorem isTrained_iff_sum_update_sub_eq_zero (hη : η ≠ 0) :
    IsTrained data q G ↔
      ∑ i, (q i : ℝ) • (update (η • 1) 1 (data.S i) (data.C i) G - G) = 0 := by
  have key : ∑ i, (q i : ℝ) • (update (η • 1) 1 (data.S i) (data.C i) G - G) =
      -η • (data.Sᵀ * q.Q * (data.S * G - data.C)) := by
    ext k j
    simp only [update_smul_one, add_sub_cancel_left, Matrix.sum_apply, Matrix.smul_apply,
      vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
    rw [mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [FrequencyVector.Q, mul_diagonal, transpose_apply, Matrix.sub_apply, mul_apply_eq_vecMul]
    ring
  rw [isTrained_iff, key, smul_eq_zero, neg_eq_zero, or_iff_right hη]

theorem mul_eq_iff_forall_update_eq_self (hη : η ≠ 0) (hS : ∀ i, data.S i ≠ 0) :
    data.S * G = data.C ↔ ∀ i, update (η • 1) 1 (data.S i) (data.C i) G = G := by
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
def pastTense : ParadigmSystem (Fin 2) cells (FormVector 13) := fun v c ↦
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
  simp [pastTense, cueVector, multiHot, mem_cues_iff] at this

/-- The table is nonetheless analogical under arbitrary operations, each form identifying its
verb, so analogy under translations is strictly stronger. -/
example : IsAnalogical Set.univ pastTense ∧ ¬ IsAnalogicallyRegular pastTense := by
  refine ⟨isAnalogical_univ_iff.2 fun c _ ↦ Function.Injective.factorsThrough
    (fun v v' h ↦ ?_) _, pastTense_not_regular⟩
  have := congrFun h 0
  simp only [pastTense, cueVector, multiHot, mem_cues_walk_iff] at this
  revert this; fin_cases v <;> fin_cases v' <;> simp

end HeitmeierChuangBaayen2026
