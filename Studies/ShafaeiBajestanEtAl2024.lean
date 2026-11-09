module

public import Linglib.Morphology.Paradigm.Analogy
public import Linglib.Processing.DiscriminativeLexicon.Training
public import Linglib.Syntax.Number.Basic

/-!
# Shafaei-Bajestan, Moradipour-Tari, Uhrig and Baayen (2024): The pluralization palette

Shafaei-Bajestan, Moradipour-Tari, Uhrig and Baayen find in word embeddings that the shift from
a singular's meaning to its plural's varies with the noun's semantic class. Their CosClassAvg
adds to a singular the average shift of its class, where 3CosAvg adds one average shift to every
noun. CosClassAvg is [proportional analogy within each semantic
class](##isAnalogicallyRegular_domRestrict_cosClassAvg), and one analogy for all nouns [exactly
when the class shifts coincide](##isAnalogicallyRegular_cosClassAvg_iff). Its class shifts are
[the least-squares shifts](##isEndstateTrained_classShift), so in sample [its squared error is at
most that of any single shift](##sum_cosClassAvg_le), 3CosAvg's and the bare singular's included.

## Implementation notes

* Embeddings are vectors `Fin d → ℝ`, and a squared distance is a difference's dot product with
  itself, as in `DiscriminativeLexicon.weightedLoss`.
* The nouns are the evaluated singular–plural pairs, the 11,749 found in WordNet (§4.2), over
  which the 411 class shifts are averaged (§4.3), so CosClassAvg's shifts are fitted to the pairs
  they predict. `sum_cosClassAvg_le` compares them with any single shift, whichever pairs
  3CosAvg's was averaged over (§4.1 averages over all 14,699).
* CosClassAvg's predictions omit the lexeme-specific and noise terms the paper adds to its plural
  semantic function (p. 389), which no class-level model recovers.

## TODO

* FRACSS (§5.1) maps singulars to plurals by the matrix `(XᵀX)⁻¹XᵀY`, endstate training of the
  plurals on the singulars (`DiscriminativeLexicon.isTrained_closedForm`); it is not stated here.

## References

* [shafaei-bajestan-moradipour-tari-uhrig-baayen-2024]
-/

@[expose] public section

namespace ShafaeiBajestanEtAl2024

open DiscriminativeLexicon Matrix Morphology

noncomputable section

variable {Noun K : Type*} [Fintype Noun] [DecidableEq K] {d : ℕ}
  (sg pl : Matrix Noun (Fin d) ℝ) (κ : Noun → K)

/-- The average shift vector of a semantic class is the mean of its nouns' individual shift
vectors, each a plural's embedding minus its singular's ((5); §4.3). -/
def classShift (k : K) : Fin d → ℝ :=
  ((Finset.univ.filter (κ · = k)).card : ℝ)⁻¹ • ∑ l ∈ Finset.univ.filter (κ · = k), (pl l - sg l)

/-- CosClassAvg predicts a noun's plural as its singular plus the average shift of its semantic
class (§4.3). -/
def cosClassAvg (l : Noun) : Fin d → ℝ := sg l + classShift sg pl κ (κ l)

/-- 3CosAvg predicts every plural as its singular plus the one average shift vector ((3), (5)),
CosClassAvg with a single class. -/
abbrev threeCosAvg : Noun → Fin d → ℝ := cosClassAvg sg pl fun _ ↦ ()

/-! ### Proportional analogy -/

/-- The cells of the table are the singular and the plural. -/
abbrev cells : Finset Number := {.singular, .plural}

/-- The table of each noun's singular and predicted plural. -/
def table (sg pred : Noun → Fin d → ℝ) : ParadigmSystem Noun cells (Fin d → ℝ) :=
  fun l c ↦ if c.1 = .singular then sg l else pred l

/-- CosClassAvg is proportional analogy within each semantic class: on a class, its table of
singulars and predicted plurals shifts every noun by the same vector (§4.3). -/
theorem isAnalogicallyRegular_domRestrict_cosClassAvg (k : K) :
    IsAnalogicallyRegular ((κ ⁻¹' {k}).domRestrict (table sg (cosClassAvg sg pl κ))) :=
  (forall_isAnalogicallyRegular_domRestrict_iff κ).2
    ⟨sg, fun k c ↦ if c.1 = .singular then 0 else classShift sg pl κ k, fun l c ↦ by
      by_cases h : c.1 = .singular <;> simp [table, cosClassAvg, h]⟩ k

/-- CosClassAvg is one proportional analogy for all nouns, a single semantic function as 3CosAvg
is, exactly when its class shifts coincide; plural semantics that varies with the class departs
from a symbolic plural (p. 389). -/
theorem isAnalogicallyRegular_cosClassAvg_iff :
    IsAnalogicallyRegular (table sg (cosClassAvg sg pl κ)) ↔
      ∀ l l', classShift sg pl κ (κ l) = classShift sg pl κ (κ l') := by
  rw [isAnalogicallyRegular_iff]
  refine ⟨fun h l l' ↦ ?_, fun h l l' ⟨c, hc⟩ ⟨c', hc'⟩ ↦ ?_⟩
  · simpa [table, cosClassAvg] using h l l' ⟨.plural, by decide⟩ ⟨.singular, by decide⟩
  · simp only [cells, Finset.mem_insert, Finset.mem_singleton] at hc hc'
    rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> simp [table, cosClassAvg, h l l']

theorem isAnalogicallyRegular_threeCosAvg : IsAnalogicallyRegular (table sg (threeCosAvg sg pl)) :=
  (isAnalogicallyRegular_cosClassAvg_iff ..).2 fun _ _ ↦ rfl

/-- Two nouns of different classes whose plurals shift by `1` and by `2`: CosClassAvg is not one
analogy for both. -/
example : ¬ IsAnalogicallyRegular (table (0 : Matrix (Fin 2) (Fin 1) ℝ)
    (cosClassAvg 0 !![1; 2] id)) := by
  rw [isAnalogicallyRegular_cosClassAvg_iff]
  intro h
  have := congrFun (h 0 1) 0
  norm_num [classShift, Finset.filter_eq'] at this

/-! ### Least squares -/

/-- The one-hot cue of each noun's semantic class. -/
def classCue : Matrix Noun K ℝ := of fun l ↦ Pi.single (κ l) 1

omit [Fintype Noun] in
@[simp] theorem classCue_mul_apply [Fintype K] (G : Matrix K (Fin d) ℝ) (l : Noun) :
    (classCue κ * G) l = G (κ l) := by
  funext j; simp [classCue, mul_apply, Pi.single_apply]

theorem weightedLoss_classCue [Fintype K] (t : K → Fin d → ℝ) :
    weightedLoss (classCue κ) (pl - sg) 1 (of t) =
      ∑ l, (sg l + t (κ l) - pl l) ⬝ᵥ (sg l + t (κ l) - pl l) := by
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h : (classCue κ * of t - (pl - sg)) l = sg l + t (κ l) - pl l := by
    funext j; simp [classCue, mul_apply, Pi.single_apply]; ring
  rw [Pi.one_apply, NNReal.coe_one, one_mul, h]

/-- The class shifts are the least-squares shifts: they form the endstate-trained mapping from the
nouns' semantic-class cues to their shift vectors, the discriminative lexicon's estimate. -/
theorem isEndstateTrained_classShift [Fintype K] :
    IsEndstateTrained (classCue κ) (pl - sg) (of (classShift sg pl κ)) := by
  classical
  obtain ⟨G, hG⟩ := exists_isTrained (classCue κ) (pl - sg) 1
  have hrow (l : Noun) : classShift sg pl κ (κ l) = G (κ l) := by
    set P := Finset.univ.filter (κ · = κ l)
    have hP : (P.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨l, by simp [P]⟩)
    have h := hG.sum_smul_mul_eq_of_decodable (P := P) (w := LinearMap.proj (κ l)) fun i ↦ by
      simp [classCue, P, Pi.single_apply, eq_comm]
    simp only [Pi.one_apply, NNReal.coe_one, one_smul, classCue_mul_apply] at h
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℝ] at h
    exact (inv_smul_eq_iff₀ hP).2 h.symm
  have hSG : classCue κ * of (classShift sg pl κ) = classCue κ * G :=
    ext_row fun l ↦
      (classCue_mul_apply κ _ l).trans ((hrow l).trans (classCue_mul_apply κ G l).symm)
  simpa only [IsTrained, isMinOn_univ_iff, weightedLoss, hSG] using hG

/-- In sample, CosClassAvg's summed squared distance to the observed plurals is at most that of
adding any single shift to every singular, 3CosAvg's and Only-B's unshifted singular included:
the ordering of Fig. 10's distance panel holds of the summed squares by construction. -/
theorem sum_cosClassAvg_le [Fintype K] (t : Fin d → ℝ) :
    ∑ l, (cosClassAvg sg pl κ l - pl l) ⬝ᵥ (cosClassAvg sg pl κ l - pl l) ≤
      ∑ l, (sg l + t - pl l) ⬝ᵥ (sg l + t - pl l) := by
  have h := isMinOn_univ_iff.1 (isEndstateTrained_classShift sg pl κ) (of fun _ ↦ t)
  rwa [weightedLoss_classCue, weightedLoss_classCue] at h

end

end ShafaeiBajestanEtAl2024
