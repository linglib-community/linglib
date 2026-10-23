module

public import Linglib.Processing.ErrorDrivenLearning

/-!
# Ellis (2006): Selective Attention and Transfer Phenomena in L2 Acquisition

Ellis argues that the grammatical forms adult second-language learners fail to acquire are the
ones associative learning predicts they will not attend to. His central case is past time
reference. A tense inflection is low in salience and is usually accompanied by a temporal adverb
that marks the same meaning, as in Terrell's *Hier nous sommes allés au cinéma*, where *hier*
makes the auxiliary and the participle redundant. Under the Rescorla–Wagner rule the cues of an
utterance share one prediction error, and two of the mechanisms Ellis names follow. A learner to
whom both cues are new divides the association between them by salience, so the adverb
overshadows the inflection. A learner whose cues already predict the outcome, as a
second-language learner's adverb does, has no error left to divide, so the inflection is blocked
however much input follows.

## Main statements

* `overshadowing`, `tendsto_strength`: learned together from nothing, the more salient cue is
  the stronger after every utterance, and in the limit each cue holds its salience's share of
  the outcome.
* `blocking`: for a learner whose cues already predict the outcome, utterances pairing adverb
  and inflection leave every association unchanged.

## Implementation notes

* The rule is `ErrorDrivenLearning.update` on the utterance in which both cues are present.
  Ellis describes it in a companion article.
* Only the Rescorla–Wagner account is formalised. Ellis also explains blocking by the
  probabilistic contrast model of Cheng and Holyoak and by learned inattention, under which a
  blocked cue is harder to learn afterwards.

## References

* [N. C. Ellis, *Selective attention and transfer phenomena in L2 acquisition*
  (2006)][ellis-2006]
* [P. W. Cheng and K. J. Holyoak, *Adaptive systems as intuitive statisticians*
  (1995)][cheng-holyoak-1995]
* [R. A. Rescorla and A. R. Wagner, *A theory of Pavlovian conditioning*
  (1972)][rescorla-wagner-1972]
-/

@[expose] public section

namespace Ellis2006

open ErrorDrivenLearning Matrix Filter Finset
open scoped Topology

/-- The temporal adverb and the tense inflection are the two cues to past time reference. -/
inductive Cue | adverb | inflection
  deriving DecidableEq, Fintype

variable {κ : Type*} (α : Cue → ℝ) (β lam : κ → ℝ) (j : κ)

private theorem one_dotProduct_cue (v : Cue → ℝ) : 1 ⬝ᵥ v = v .adverb + v .inflection := by
  rw [one_dotProduct, show (univ : Finset Cue) = {.adverb, .inflection} from rfl,
    sum_pair (by decide)]

/-! ### Overshadowing -/

theorem iterate_update_zero_apply (n : ℕ) (c : Cue) :
    (update α β 1 lam)^[n] 0 c j =
      α c * (lam j * β j * ∑ k ∈ range n, (1 - (α .adverb + α .inflection) * β j) ^ k) := by
  simp [iterate_update_apply, one_dotProduct_cue]

variable {α β lam j}

/-- When two cues jointly predict an outcome the less salient one is overshadowed, so after every
utterance the inflection is the weaker cue. -/
theorem overshadowing (hα : α .inflection < α .adverb) (hβ : 0 < β j) (hlam : 0 < lam j)
    (h : (α .adverb + α .inflection) * β j < 2) {n : ℕ} (hn : n ≠ 0) :
    (update α β 1 lam)^[n] 0 .inflection j < (update α β 1 lam)^[n] 0 .adverb j := by
  simp only [iterate_update_zero_apply]
  exact mul_lt_mul_of_pos_right hα (mul_pos (mul_pos hlam hβ) (geom_sum_pos' (by linarith) hn))

theorem tendsto_strength (c : Cue) (h : |1 - (α .adverb + α .inflection) * β j| < 1) :
    Tendsto (fun n ↦ (update α β 1 lam)^[n] 0 c j) atTop
      (𝓝 (α c / (α .adverb + α .inflection) * lam j)) := by
  simpa [one_dotProduct_cue] using tendsto_iterate_update_apply (α := α) (x := 1) (y := lam) 0 c
    (by simpa [one_dotProduct_cue] using h)

/-! ### Blocking -/

theorem blocking {V : Matrix Cue κ ℝ} (hV : V .adverb + V .inflection = lam) (n : ℕ) :
    (update α β 1 lam)^[n] V = V := by
  refine Function.iterate_fixed (update_eq_self_of_vecMul_eq α β ?_) n
  ext j
  simp [vecMul, one_dotProduct_cue, ← hV]

theorem inflection_pos (hα : 0 < α .inflection) (hβ : 0 < β j) (hlam : 0 < lam j)
    (h : (α .adverb + α .inflection) * β j < 2) {n : ℕ} (hn : n ≠ 0) :
    0 < (update α β 1 lam)^[n] 0 .inflection j := by
  rw [iterate_update_zero_apply]
  exact mul_pos hα (mul_pos (mul_pos hlam hβ) (geom_sum_pos' (by linarith) hn))

end Ellis2006
