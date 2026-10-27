module

public import Linglib.Core.LinearAlgebra.Matrix.StarProjection
public import Linglib.Processing.DiscriminativeLexicon.Coding
public import Linglib.Processing.DiscriminativeLexicon.Measures
public import Linglib.Processing.DiscriminativeLexicon.Training
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Gahl and Baayen (2024): Time and Thyme Again

Gahl had found that the more frequent of two homophones, such as *time* against *thyme*, tends to
be shorter in speech. Gahl and Baayen recast this with a discriminative lexicon, linear maps
between semantic vectors and triphone vectors with no stored words, so frequency cannot be a
property of a word. It splits instead into practice, frequency-informed learning of the
production map, and contextual independence, the share of a word's predictability in an
utterance that it owes to itself. The duration models are not formalized; the paper's two worked
examples are.

## Implementation notes

* The paper fits only the production matrix `G`, so the toy lexicons are their mapping matrices.
* The paper estimates the corpus-scale word-to-word map with the Rescorla–Wagner rule, which is
  not formalized; `W` is the pseudoinverse solution it uses for the toy corpus.

## References

* [gahl-baayen-2024]
* [gahl-2008]
* [baayen-2019]
* [heitmeier-chuang-axen-baayen-2024]
-/

@[expose] public section

namespace GahlBaayen2024

open DiscriminativeLexicon Matrix

noncomputable section

/-! ### The toy lexicon -/

/-- The toy lexicon uses five phones, with `i` standing for the paper's `ɪ` and the diphthong
written as the two phones `a ɪ`. -/
inductive Phone
  | t | l | a | i | m
  deriving DecidableEq

/-- The toy words *time*, *lime* and *thyme* are spelled as phone strings, the two homophones
sharing a string. -/
def word : Fin 3 → List Phone := ![[.t, .a, .i, .m], [.l, .a, .i, .m], [.t, .a, .i, .m]]

/-- The six triphones of (2) are listed in the paper's column order `#ta taɪ aɪm ɪm# #la laɪ`. -/
def triphone : Fin 6 → Augmented Phone :=
  ![[none, some .t, some .a], [some .t, some .a, some .i], [some .a, some .i, some .m],
    [some .i, some .m, none], [none, some .l, some .a], [some .l, some .a, some .i]]

/-- Each row of the form matrix `C` of (2) is the word's triphone indicator, the DLM's cue coding
at width 3. -/
def toyForms (i : Fin 3) : FormVector 6 := cueVector 3 triphone (word i)

-- (2)
theorem toyForms_eq :
    toyForms = ![![1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0]] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [toyForms, cueVector, multiHot, Matrix.cons_val_two]

/-- The semantic vectors of (1) give *time*, *lime* and *thyme* two arbitrary dimensions. -/
def semanticVectors : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1 / 10, 3 / 10; 6 / 10, 2 / 10; 11 / 10, 6 / 10]

/-- The toy lexicon pairs the semantic matrix `S` of (1) with the triphone matrix `C` of (2). -/
def toy : TrainingExperience 3 6 2 where
  S := semanticVectors.map (Rat.castHom ℝ)
  C := Matrix.of toyForms

/-- *time* is the first row of the toy lexicon. -/
abbrev time : Fin 3 := 0

/-- *lime* is the second row of the toy lexicon. -/
abbrev lime : Fin 3 := 1

/-- *thyme* is the third row of the toy lexicon. -/
abbrev thyme : Fin 3 := 2

/-- *time*, *lime* and *thyme* have token frequencies 100, 10 and 1 (A3). -/
def freq : FrequencyVector 3 := ![100, 10, 1]

/-! The arithmetic of the toy lexicon is decided over `ℚ` and cast into `ℝ`. -/

private def ratC : Matrix (Fin 3) (Fin 6) ℚ :=
  Matrix.of fun i j ↦ if triphone j ∈ cues 3 (word i) then 1 else 0

private def ratQ : Matrix (Fin 3) (Fin 3) ℚ := diagonal ![100, 10, 1]

private theorem toy_S : toy.S = semanticVectors.map (Rat.castHom ℝ) := rfl

private theorem toy_C : toy.C = ratC.map (Rat.castHom ℝ) := by
  ext i j; simp [toy, ratC, toyForms, cueVector, multiHot, apply_ite]

private theorem freq_Q : freq.Q = ratQ.map (Rat.castHom ℝ) := by
  rw [FrequencyVector.Q, ratQ, diagonal_map (map_zero _)]
  congr 1; funext i; fin_cases i <;> simp [freq]

-- `(SᵀS)⁻¹` and `(SᵀQS)⁻¹`, with determinants `1181 / 10⁴` and `16543 / 500`.
private def ratGramInv : Matrix (Fin 2) (Fin 2) ℚ :=
  (10000 / 1181 : ℚ) • !![49 / 100, -81 / 100; -81 / 100, 158 / 100]

private def ratGramInvQ : Matrix (Fin 2) (Fin 2) ℚ :=
  (500 / 16543 : ℚ) • !![976 / 100, -486 / 100; -486 / 100, 581 / 100]

-- The endstate mapping is (4), which the paper prints to two decimals.
private def ratG : Matrix (Fin 2) (Fin 6) ℚ := (1181 : ℚ)⁻¹ •
  !![-1410, -1410, -90, -90, 1320, 1320; 4500, 4500, 2800, 2800, -1700, -1700]

private def ratGFIL : Matrix (Fin 2) (Fin 6) ℚ := (16543 : ℚ)⁻¹ •
  !![-20190, -20190, 4230, 4230, 24420, 24420; 61920, 61920, 53150, 53150, -8770, -8770]

/-! ### Endstate and frequency-informed learning

The paper fits only the production side of the model, a mapping matrix acting on row vectors,
`ĉ = sG`. -/

/-- The endstate mapping `G` of (4) is the closed form `(SᵀS)⁻¹SᵀC` of (A2). -/
def endstateG : Matrix (Fin 2) (Fin 6) ℝ := (toy.Sᵀ * toy.S)⁻¹ * (toy.Sᵀ * toy.C)

/-- The frequency-informed mapping is the closed form `(SᵀQS)⁻¹SᵀQC` of the normal equations
of (A4) at the frequencies `freq`. -/
def frequencyInformedG : Matrix (Fin 2) (Fin 6) ℝ :=
  (toy.Sᵀ * freq.Q * toy.S)⁻¹ * (toy.Sᵀ * freq.Q * toy.C)

private theorem gramS_mul_inv : toy.Sᵀ * toy.S * ratGramInv.map (Rat.castHom ℝ) = 1 := by
  have h : semanticVectorsᵀ * semanticVectors * ratGramInv = 1 := by decide +kernel
  rw [toy_S, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem gramSQ_mul_inv :
    toy.Sᵀ * freq.Q * toy.S * ratGramInvQ.map (Rat.castHom ℝ) = 1 := by
  have h : semanticVectorsᵀ * ratQ * semanticVectors * ratGramInvQ = 1 := by decide +kernel
  rw [toy_S, freq_Q, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, h,
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem endstateG_eq : endstateG = ratG.map (Rat.castHom ℝ) := by
  have h : ratGramInv * (semanticVectorsᵀ * ratC) = ratG := by decide +kernel
  rw [endstateG, inv_eq_right_inv gramS_mul_inv, toy_S, toy_C, ← transpose_map,
    ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem frequencyInformedG_eq : frequencyInformedG = ratGFIL.map (Rat.castHom ℝ) := by
  have h : ratGramInvQ * (semanticVectorsᵀ * ratQ * ratC) = ratGFIL := by decide +kernel
  rw [frequencyInformedG, inv_eq_right_inv gramSQ_mul_inv, toy_S, toy_C, freq_Q,
    ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem endstateG_isELTrained : IsELTrained toy endstateG :=
  isELTrained_closedForm toy
    ((isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse gramS_mul_inv))

theorem frequencyInformedG_isTrained : IsTrained toy freq frequencyInformedG :=
  isTrained_closedForm toy freq
    ((isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse gramSQ_mul_inv))

/-! ### Semantic support for form -/

section

variable {m n d : ℕ} (G : Matrix (Fin d) (Fin n) ℝ) (data : TrainingExperience m n d)

/-- The support matrix `T = ĈCᵀ` of (A5), with `Ĉ = SG`, tabulates the support each word's form
(column) receives from each word's meaning (row). -/
def supportMatrix : Matrix (Fin m) (Fin m) ℝ := data.S * G * data.Cᵀ

theorem supportMatrix_apply (i k : Fin m) :
    supportMatrix G data i k = semanticSupport G (data.S i) (data.C k) := by
  rw [supportMatrix, mul_apply, semanticSupport_apply, ← mul_apply_eq_vecMul]
  rfl

/-- *Semantic support for form* is the diagonal of `T`, the support a word's form receives from
its own meaning. -/
def semanticSupportForForm : Fin m → ℝ := (supportMatrix G data).diag

end

private theorem supportMatrix_endstateG :
    supportMatrix endstateG toy = (semanticVectors * ratG * ratCᵀ).map (Rat.castHom ℝ) := by
  rw [supportMatrix, endstateG_eq, toy_S, toy_C, ← transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul]

private theorem supportMatrix_frequencyInformedG : supportMatrix frequencyInformedG toy =
    (semanticVectors * ratGFIL * ratCᵀ).map (Rat.castHom ℝ) := by
  rw [supportMatrix, frequencyInformedG_eq, toy_S, toy_C, ← transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul]

/-- At the endstate *thyme*'s meaning supports its form more than *time*'s does, 4.623 against
3.455 (Table 1). -/
theorem semanticSupportForForm_endstate_time_lt_thyme :
    semanticSupportForForm endstateG toy time < semanticSupportForForm endstateG toy thyme := by
  have h : (semanticVectors * ratG * ratCᵀ) time time <
      (semanticVectors * ratG * ratCᵀ) thyme thyme := by decide +kernel
  simp only [semanticSupportForForm, diag_apply, supportMatrix_endstateG, map_apply,
    Rat.coe_castHom, Rat.cast_lt]
  exact h

/-- Under frequency-informed learning the paper reads support for form off the fitted values
`√Q S G` of the `√Q`-scaled regression, paired with the words' own triphone vectors (A7). -/
def semanticSupportForFormFIL (i : Fin 3) : ℝ :=
  semanticSupport frequencyInformedG ((toy.sqrtScale freq).S i) (toy.C i)

theorem semanticSupportForFormFIL_eq_sqrt_mul (i : Fin 3) :
    semanticSupportForFormFIL i =
      √(freq i) * semanticSupportForForm frequencyInformedG toy i := by
  simp [semanticSupportForFormFIL, semanticSupportForForm, supportMatrix_apply]

/-- Under practice *time* overtakes *thyme*, 39.805 against 6.225 (Table 1), reversing the
endstate order. -/
theorem semanticSupportForFormFIL_thyme_lt_time :
    semanticSupportForFormFIL thyme < semanticSupportForFormFIL time := by
  have h : (semanticVectors * ratGFIL * ratCᵀ) thyme thyme <
      10 * (semanticVectors * ratGFIL * ratCᵀ) time time := by decide +kernel
  have h100 : √100 = 10 := by rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [semanticSupportForFormFIL_eq_sqrt_mul, semanticSupportForForm, diag_apply,
    supportMatrix_frequencyInformedG, map_apply, Rat.coe_castHom]
  simpa [freq, h100, thyme, Matrix.cons_val_two] using (Rat.cast_lt (K := ℝ)).2 h

/-- The words *time* and *thyme* share a form row, but the endstate mapping predicts distinct forms
for them (appendix A3, Fig. A2). -/
theorem endstate_separates_homophones :
    toy.C time = toy.C thyme ∧ (toy.S * endstateG) time ≠ (toy.S * endstateG) thyme := by
  have h : (semanticVectors * ratG) time 0 ≠ (semanticVectors * ratG) thyme 0 := by
    decide +kernel
  refine ⟨rfl, ?_⟩
  rw [endstateG_eq, toy_S, ← Matrix.map_mul]
  exact fun h' ↦ h (Rat.cast_injective (congrFun h' 0))

/-! ### Contextual independence

A word-to-word map `W` with `UW = U` predicts every word of an utterance from all the words in
it, and the diagonal of `W` is the share of that prediction a word owes to itself. -/

/-- The toy corpus has nine words. -/
inductive Word
  | my | time | is | short | good | fragrant | thyme | lime | bad
  deriving DecidableEq

/-- The five toy utterances of (5). -/
def utterance : Fin 5 → List Word :=
  ![[.my, .time, .is, .short], [.my, .good, .time], [.my, .fragrant, .thyme],
    [.my, .lime, .is, .bad], [.my, .lime, .is, .good]]

/-- The columns of `U` and `W` list the words in the paper's order. -/
def vocabulary : Fin 9 → Word :=
  ![.my, .time, .is, .short, .good, .fragrant, .thyme, .lime, .bad]

/-- The utterance-by-word matrix `U` multiple-hot encodes each utterance over the vocabulary. -/
def U : Matrix (Fin 5) (Fin 9) ℝ := Matrix.of fun i ↦ multiHot vocabulary (· ∈ utterance i)

/-! The arithmetic of the toy corpus is decided over `ℤ` and cast into `ℝ`. -/

private def intU : Matrix (Fin 5) (Fin 9) ℤ :=
  Matrix.of fun i j ↦ if vocabulary j ∈ utterance i then 1 else 0

private theorem U_eq_map : U = intU.map (Int.castRingHom ℝ) := by
  ext i j; simp [U, intU, multiHot, apply_ite]

/-- The word-to-word map `W` of (6) is `U⁺U = Uᵀ(UUᵀ)⁻¹U`, the pseudoinverse solution of
`UW = U` (A8). -/
def W : Matrix (Fin 9) (Fin 9) ℝ := Uᵀ * (U * Uᵀ)⁻¹ * U

-- The adjugate of `UUᵀ`, whose determinant is `71`.
private def intAdjGram : Matrix (Fin 5) (Fin 5) ℤ :=
  !![33, -20, -1, -15, 5;
     -20, 53, -8, 22, -31;
     -1, -8, 28, -6, 2;
     -15, 22, -6, 52, -41;
     5, -31, 2, -41, 61]

-- (6) over the common denominator `71`, which the paper prints to two decimals.
private def intW : Matrix (Fin 9) (Fin 9) ℤ :=
  !![41, 18, 10, 2, 12, 15, 15, 8, 12;
     18, 46, -6, 13, 7, -9, -9, -19, 7;
     10, -6, 44, 23, -4, -5, -5, 21, -4;
     2, 13, 23, 33, -15, -1, -1, -10, -15;
     12, 7, -4, -15, 52, -6, -6, 11, -19;
     15, -9, -5, -1, -6, 28, 28, -4, -6;
     15, -9, -5, -1, -6, 28, 28, -4, -6;
     8, -19, 21, -10, 11, -4, -4, 31, 11;
     12, 7, -4, -15, -19, -6, -6, 11, 52]

private theorem gramU_mul_inv :
    U * Uᵀ * ((71 : ℝ)⁻¹ • intAdjGram.map (Int.castRingHom ℝ)) = 1 := by
  have h : intU * intUᵀ * intAdjGram = 71 • 1 := by decide +kernel
  rw [Matrix.mul_smul, U_eq_map, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

private theorem W_eq_conjTranspose : W = Uᴴ * (U * Uᴴ)⁻¹ * U := by
  rw [conjTranspose_eq_transpose_of_trivial]; rfl

private theorem isUnit_det_gramU : IsUnit (U * Uᴴ).det := by
  rw [conjTranspose_eq_transpose_of_trivial]; exact isUnit_det_of_right_inverse gramU_mul_inv

private theorem W_eq : W = (71 : ℝ)⁻¹ • intW.map (Int.castRingHom ℝ) := by
  have h : intUᵀ * intAdjGram * intU = intW := by decide +kernel
  rw [W, inv_eq_right_inv gramU_mul_inv, Matrix.mul_smul, Matrix.smul_mul, U_eq_map,
    ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]

-- (7), (8)
theorem U_mul_W : U * W = U := by
  rw [W_eq_conjTranspose]; exact mul_conjTranspose_mul_inv_mul isUnit_det_gramU

theorem isStarProjection_W : IsStarProjection W := by
  rw [W_eq_conjTranspose]; exact isStarProjection_conjTranspose_mul_inv_mul isUnit_det_gramU

/-- Regressing the words of each utterance on themselves, as the paper does for the toy corpus,
does not determine `W`, since the identity, the "ideal solution" of (A9), is trained as well. -/
theorem not_existsUnique_isELTrained :
    ¬ ∃! G, IsELTrained (⟨U, U⟩ : TrainingExperience 5 9 9) G := by
  rintro ⟨G, -, hG⟩
  refine absurd (congrFun (congrFun ((hG W (isTrained_of_mul_eq _ _ _ U_mul_W)).trans
    (hG 1 (isTrained_of_mul_eq _ _ _ (Matrix.mul_one U))).symm) 0) 0) ?_
  rw [W_eq]; norm_num [intW]

-- (6)
theorem le_diag_W (i j : Fin 9) : W j i ≤ W i i := by
  have h : ∀ i j : Fin 9, intW j i ≤ intW i i := by decide +kernel
  rw [W_eq]
  simp only [Matrix.smul_apply, Matrix.map_apply, eq_intCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Int.cast_le.2 (h i j)) (by norm_num)

open scoped MatrixOrder in
/-- The diagonal of `W` lies in `[0, 1]`, the "proportions" of §3.2, because `W` is an
orthogonal projection. -/
theorem diag_W_mem_Icc (i : Fin 9) : W i i ∈ Set.Icc 0 1 :=
  ⟨(nonneg_iff_posSemidef.1 isStarProjection_W.nonneg).diag_nonneg,
    sub_nonneg.1 <| by
      simpa using (nonneg_iff_posSemidef.1 isStarProjection_W.one_sub_nonneg).diag_nonneg (i := i)⟩

/-- The contextual-independence measure of (9) is `Cind = (log(1/d))^{1/4}`, a log against the
right skew of the diagonal values and a power to finish it. -/
def cind (d : ℝ) : ℝ := Real.log (1 / d) ^ (1 / 4 : ℝ)

-- (0, 1), Fig. 2
theorem strictAntiOn_cind : StrictAntiOn cind (Set.Ioo 0 1) := fun a ha b hb hab ↦ by
  unfold cind
  refine Real.rpow_lt_rpow (Real.log_nonneg ?_)
    (Real.log_lt_log (one_div_pos.mpr hb.1) (one_div_lt_one_div_of_lt ha.1 hab)) (by norm_num)
  rw [le_div_iff₀ hb.1]; linarith [hb.2]

end

end GahlBaayen2024
