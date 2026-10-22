module

public import Linglib.Morphology.Paradigm.Analogy
public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Core.InformationTheory.Entropy
public import Mathlib.Data.Fintype.Pi

/-!
# Paradigm complexity: implicative structure and entropy over cells

This file gives the two faces of the paradigm cell filling problem over a `ParadigmSystem`.
The qualitative face is categorical: a set of cells *predicts* another when the forms filling it
determine the form filling the target across the inflection classes
(`Function.FactorsThrough`), a *principal-part set* predicts every cell, and a system is
*vocabularly clear* ([carstairs-mccarthy-2010]) when every single cell is. Enumerative
complexity is counted by the realizations of each cell: their product bounds the number of
distinct paradigms, and *paradigm economy* bounds the classes by the most varied cell.

The quantitative face is `Core/InformationTheory/Entropy.lean` applied to the data: under a
probability measure `μ` on the classes — uniform in every computation of
[ackerman-malouf-2013], type frequencies in its general definitions — the cell `c` is the
random variable `(M · c)`, so declension entropy is `Hm[μ]`, cell entropy is `H[(M · c) ; μ]`,
and the conditional entropy of one cell given another is `H[(M · c₁) | (M · c₂) ; μ]`. Only
the average over ordered pairs of distinct cells, [ackerman-malouf-2013]'s I-complexity, needs
a definition. The two faces meet at zero: under the uniform measure, one cell predicts another
iff the conditional entropy vanishes, and a system is vocabularly clear iff its average
conditional entropy is zero.

## Main declarations

* `ParadigmSystem.Predicts`, `ParadigmSystem.IsPrincipalPartSet`,
  `ParadigmSystem.IsVocabularClear`: the implicative relations.
* `ParadigmSystem.realizations`, `ParadigmSystem.maxRealizations`,
  `ParadigmSystem.ParadigmEconomy`: enumerative counts and the paradigm economy principle.
* `ParadigmSystem.avgCondEntropy`: the average conditional entropy of one cell given another.
* `ParadigmSystem.cellForm`: the form at a cell valued in the cell's realizations, through which
  the entropy statements hold for any type of forms.

## Main statements

* `ParadigmSystem.predicts_iff_condEntropy_eq_zero`,
  `ParadigmSystem.isVocabularClear_iff_avgCondEntropy_eq_zero`: prediction is zero conditional
  entropy, and vocabular clarity is zero average conditional entropy, under the uniform measure.
* `ParadigmSystem.avgCondEntropy_le_measureEntropy`: the average conditional entropy is at most
  the declension entropy.
* `ParadigmSystem.isVocabularClear_iff_isAnalogical`: vocabular clarity is analogy under
  arbitrary operations (`Morphology.IsAnalogical`).

## References

* [ackerman-malouf-2013]
* [bonami-beniamine-2016]
* [carstairs-mccarthy-2010]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace Morphology

namespace ParadigmSystem

variable {D Cell Form : Type*}

/-! ### Implicative structure -/

/-- A set of cells `S` predicts cell `j` when the form at `j` factors through the forms at
`S`, so that any two classes agreeing on every cell of `S` agree at `j`. -/
def Predicts (M : ParadigmSystem D Cell Form) (S : Finset Cell) (j : Cell) : Prop :=
  (M · j).FactorsThrough fun d ↦ S.restrict (M d)

/-- A principal-part set predicts every cell. -/
def IsPrincipalPartSet (M : ParadigmSystem D Cell Form) (S : Finset Cell) : Prop :=
  ∀ j, M.Predicts S j

/-- A system is vocabularly clear when every cell on its own predicts every cell, so that each
realization identifies the class ([carstairs-mccarthy-2010] via [ackerman-malouf-2013]). -/
def IsVocabularClear (M : ParadigmSystem D Cell Form) : Prop := ∀ c, M.IsPrincipalPartSet {c}

variable {M : ParadigmSystem D Cell Form} {S T : Finset Cell} {c j : Cell}

theorem predicts_iff :
    M.Predicts S j ↔ ∀ d d', (∀ c ∈ S, M d c = M d' c) → M d j = M d' j := by
  simp [Predicts, Function.FactorsThrough, funext_iff, Finset.restrict]

/-- One cell predicts another iff the form at the latter factors through the form at the
former. -/
theorem predicts_singleton_iff : M.Predicts {c} j ↔ (M · j).FactorsThrough (M · c) := by
  simp [predicts_iff, Function.FactorsThrough]

theorem Predicts.mono (hST : S ⊆ T) (h : M.Predicts S j) : M.Predicts T j :=
  predicts_iff.2 fun d d' hag ↦ predicts_iff.1 h d d' fun c hc ↦ hag c (hST hc)

theorem predicts_of_mem (hj : j ∈ S) : M.Predicts S j :=
  predicts_iff.2 fun _ _ hag ↦ hag j hj

section Counting

variable (M) [Fintype D] [DecidableEq Form]

instance : Decidable (M.Predicts S j) := decidable_of_iff _ predicts_iff.symm

instance [Fintype Cell] : Decidable (M.IsPrincipalPartSet S) :=
  inferInstanceAs (Decidable (∀ j, M.Predicts S j))

instance [Fintype Cell] : Decidable M.IsVocabularClear :=
  inferInstanceAs (Decidable (∀ c, M.IsPrincipalPartSet {c}))

/-! ### Enumerative counts -/

/-- The forms realizing cell `c`. -/
def realizations (c : Cell) : Finset Form := Finset.univ.image (M · c)

/-- The form at the cell `c`, valued in the cell's realizations. -/
def cellForm (c : Cell) (d : D) : M.realizations c :=
  ⟨M d c, Finset.mem_image_of_mem _ (Finset.mem_univ d)⟩

instance [Nonempty D] (c : Cell) : Nonempty (M.realizations c) :=
  let ⟨d⟩ := ‹Nonempty D›; ⟨M.cellForm c d⟩

theorem factorsThrough_cellForm_iff :
    (M.cellForm c).FactorsThrough (M.cellForm j) ↔ (M · c).FactorsThrough (M · j) :=
  forall₂_congr fun _ _ ↦ by simp [cellForm, Subtype.ext_iff]

variable [Fintype Cell]

/-- The largest number of rival realizations of a single cell. -/
def maxRealizations : ℕ := Finset.univ.sup fun c ↦ (M.realizations c).card

/-- A system is paradigm-economical when it has no more classes than rival realizations of
its most varied cell ([carstairs-mccarthy-2010]). -/
def ParadigmEconomy : Prop := Fintype.card D ≤ M.maxRealizations

instance : Decidable M.ParadigmEconomy := inferInstanceAs (Decidable (_ ≤ _))

/-- The distinct paradigms of the system are bounded by the product of the realizations of the
cells. -/
theorem card_image_le_prod_card_realizations [DecidableEq D] [DecidableEq Cell] :
    (Finset.univ.image M).card ≤ ∏ c, (M.realizations c).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_le_card_of_injOn id (fun p hp ↦ ?_) (Set.injOn_id _)
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hp
  exact Finset.mem_coe.2 (Fintype.mem_piFinset.2 fun c ↦ Finset.mem_image_of_mem _ (by simp))

end Counting

/-! ### Entropy

The entropy face is Core notation applied to the data: `Hm[μ]` is the declension entropy,
`H[(M · c) ; μ]` the cell entropy, `H[(M · c₁) | (M · c₂) ; μ]` the conditional entropy of one
cell given another. Only the average needs a definition. -/

section Entropy

variable [MeasurableSpace D] [MeasurableSpace Form] {c₁ c₂ : Cell}

section Average

variable [Fintype Cell] [DecidableEq Cell]

variable (M) in
/-- The average conditional entropy of one cell given another, over ordered pairs of distinct
cells, is [ackerman-malouf-2013]'s I-complexity. -/
noncomputable def avgCondEntropy (μ : Measure D) : ℝ :=
  (∑ c₁, ∑ c₂ ∈ Finset.univ.erase c₁, H[(M · c₁) | (M · c₂) ; μ]) /
    (Fintype.card Cell * (Fintype.card Cell - 1) : ℕ)

theorem avgCondEntropy_nonneg (μ : Measure D) : 0 ≤ M.avgCondEntropy μ :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ condEntropy_nonneg _ _ _)
    (Nat.cast_nonneg _)

end Average

variable [Fintype D] [MeasurableSingletonClass Form] [DecidableEq Form]

/-- A cell with at most one realization has zero entropy. -/
theorem entropy_eq_zero_of_card_realizations_le_one (μ : Measure D)
    [IsProbabilityMeasure μ] (h : (M.realizations c).card ≤ 1) : H[(M · c) ; μ] = 0 := by
  rcases isEmpty_or_nonempty D with hD | ⟨⟨d₀⟩⟩
  · exact absurd (measure_univ (μ := μ)) (by simp [Set.univ_eq_empty_iff.2 hD])
  · have : (M · c) = fun _ ↦ M d₀ c :=
      funext fun d ↦ Finset.card_le_one.1 h _ (Finset.mem_image_of_mem _ (Finset.mem_univ d)) _
        (Finset.mem_image_of_mem _ (Finset.mem_univ d₀))
    rw [this, entropy_const]

variable [MeasurableSingletonClass D]

/-- The forms at two cells carry the same conditional entropy valued in the cells' realizations,
which are finite whatever the type of forms. -/
theorem condEntropy_cellForm (μ : Measure D) :
    H[M.cellForm c₁ | M.cellForm c₂ ; μ] = H[(M · c₁) | (M · c₂) ; μ] := by
  have hval : MeasurableEmbedding (Subtype.val : M.realizations c₂ → Form) :=
    MeasurableEmbedding.subtype_coe (M.realizations c₂).measurableSet
  rw [← condEntropy_comp_of_injective (M.cellForm c₂) μ (measurable_of_finite _)
    measurable_subtype_coe Subtype.val_injective,
    ← condEntropy_comp_right_of_measurableEmbedding _ μ (measurable_of_finite _) hval]
  rfl

/-- A predicted cell has zero conditional entropy given its predictor, whatever the class
probabilities. -/
theorem condEntropy_eq_zero_of_predicts (μ : Measure D) [IsProbabilityMeasure μ]
    (h : M.Predicts {c₂} c₁) : H[(M · c₁) | (M · c₂) ; μ] = 0 := by
  have := nonempty_of_isProbabilityMeasure μ
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff _).1
    ((M.factorsThrough_cellForm_iff).2 (predicts_singleton_iff.1 h))
  rw [← condEntropy_cellForm, hf]
  exact condEntropy_comp_self μ (measurable_of_finite _) f

/-- Under the uniform measure on the classes, one cell predicts another exactly when the
conditional entropy of the second given the first vanishes. -/
theorem predicts_iff_condEntropy_eq_zero [Nonempty D] :
    M.Predicts {c₂} c₁ ↔ H[(M · c₁) | (M · c₂) ; uniformOn (Set.univ : Set D)] = 0 := by
  have := isProbabilityMeasure_uniformOn (Set.finite_univ (α := D)) Set.univ_nonempty
  rw [← condEntropy_cellForm, condEntropy_eq_zero_iff _ (measurable_of_finite _)
    (measurable_of_finite _), predicts_singleton_iff, ← M.factorsThrough_cellForm_iff,
    Function.factorsThrough_iff]
  simp only [uniformOn_univ_ae_iff, funext_iff, Function.comp_apply]

variable [Fintype Cell] [DecidableEq Cell]

/-- The average conditional entropy is at most the declension entropy ("guessing a lexeme's
declension on the basis of a single word form can never be harder than guessing the declension
with no information at all", [ackerman-malouf-2013]). -/
theorem avgCondEntropy_le_measureEntropy (μ : Measure D) [IsProbabilityMeasure μ] :
    M.avgCondEntropy μ ≤ Hm[μ] := by
  have hle : ∑ c₁, ∑ c₂ ∈ Finset.univ.erase c₁, H[(M · c₁) | (M · c₂) ; μ] ≤
      (Fintype.card Cell * (Fintype.card Cell - 1) : ℕ) * Hm[μ] :=
    calc _ ≤ ∑ c₁ : Cell, ((Finset.univ.erase c₁).card : ℝ) * Hm[μ] :=
          Finset.sum_le_sum fun c₁ _ ↦ by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_le_sum fun c₂ _ ↦ condEntropy_cellForm (M := M) μ ▸
              (condEntropy_le_entropy μ (measurable_of_finite _) (measurable_of_finite _)).trans
                (entropy_le_measureEntropy μ _)
      _ = _ := by simp [Finset.card_erase_of_mem, mul_assoc]
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card Cell * (Fintype.card Cell - 1))).eq_or_lt
    with h0 | hpos
  · rw [avgCondEntropy, ← h0, div_zero]
    exact measureEntropy_nonneg μ
  · rw [avgCondEntropy, div_le_iff₀ hpos, mul_comm]
    exact hle

theorem avgCondEntropy_eq_zero_of_isVocabularClear (μ : Measure D)
    [IsProbabilityMeasure μ] (h : M.IsVocabularClear) : M.avgCondEntropy μ = 0 := by
  rw [avgCondEntropy, Finset.sum_eq_zero, zero_div]
  exact fun c₁ _ ↦ Finset.sum_eq_zero fun c₂ _ ↦
    condEntropy_eq_zero_of_predicts μ (h c₂ c₁)

/-- Vocabular clarity is zero average conditional entropy under the uniform measure
([ackerman-malouf-2013]: "average conditional entropy, as a consequence, should be zero"). -/
theorem isVocabularClear_iff_avgCondEntropy_eq_zero [Nonempty D] :
    M.IsVocabularClear ↔ M.avgCondEntropy (uniformOn Set.univ) = 0 := by
  have := isProbabilityMeasure_uniformOn (Set.finite_univ (α := D)) Set.univ_nonempty
  refine ⟨avgCondEntropy_eq_zero_of_isVocabularClear _, fun h c j ↦ ?_⟩
  rcases eq_or_ne j c with rfl | hne
  · exact predicts_of_mem (Finset.mem_singleton_self j)
  · have hn : 1 < Fintype.card Cell := Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨j, c, hne⟩⟩
    have hsum : ∑ c₁, ∑ c₂ ∈ Finset.univ.erase c₁,
        H[(M · c₁) | (M · c₂) ; uniformOn (Set.univ : Set D)] = 0 :=
      (div_eq_zero_iff.1 h).resolve_right
        (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun c₁ _ ↦ Finset.sum_nonneg
      fun c₂ _ ↦ condEntropy_nonneg _ _ _).1 hsum j (Finset.mem_univ j)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun c₂ _ ↦ condEntropy_nonneg _ _ _).1 hterm c
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ c⟩)
    exact predicts_iff_condEntropy_eq_zero.2 this

end Entropy

/-- A system is vocabularly clear iff its classes are analogical under arbitrary operations, so
analogy under any class of operations makes it vocabularly clear. -/
theorem isVocabularClear_iff_isAnalogical : M.IsVocabularClear ↔ IsAnalogical Set.univ M := by
  simp [IsVocabularClear, IsPrincipalPartSet, predicts_singleton_iff, isAnalogical_univ_iff]

end ParadigmSystem

end Morphology
