module

public import Linglib.Pragmatics.RSA.QUD
public import Linglib.Semantics.Attitudes.Factivity
public import Linglib.Core.Probability.Kernel.Posterior

/-!
# Scontras and Tonhauser (2025): Projection without Lexically-Specified Presupposition

Scontras and Tonhauser model the projection of the complement of *know* from under negation
without a lexical presupposition. A world settles whether Cole believes the complement and
whether it is true, *know* is factive and *think* is not, and the two questions of the
experiments ask whether Cole believes the complement and whether it is true. A literal listener
interprets the utterance within the speaker's private assumptions, a set of worlds, and answers
the question (`L0`). The speaker is informative about the answer and pays a cost that doubles for
the complex utterances (`S1`). The pragmatic listener, who hears the utterance and the question,
inverts the speaker jointly over worlds and assumptions (`L1`), as in the model of Qing, Goodman
and Lassiter.

## Implementation notes

* The paper's literal listener carries a world prior, but in the released model the literal
  listener draws worlds uniformly within the assumption set and the world prior enters at the
  pragmatic listener alone. The file follows the released model, whose predictions the paper
  reports, and this is what makes the prior effect a theorem. The listener's prior puts the
  actual world in the assumption set, as the released model does.
* The world prior is a parameter, in the theorems a product of a belief prior and a complement
  prior. The paper's is such a product, the complement twice as likely as not or half as likely.
  The prior over assumption sets is a parameter, and the paper's is that of Qing, Goodman and
  Lassiter.
* A simple utterance costs `k` and a complex one `2 * k`, the paper's cost of a simple utterance
  doubled.

## TODO

* The sizes of the utterance and question effects are computations at the paper's parameters and
  are not stated.
* The revised model of the paper's fourth section, which backs off toward the prior by the
  divergence of the posterior from it, and the experiments' ratings are not formalized.

## References

* [scontras-tonhauser-2025]
* [qing-goodman-lassiter-2016]
* [kao-etal-2014-hyperbole]
* [degen-tonhauser-2021]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Factivity
open scoped ENNReal

namespace ScontrasTonhauser2025

/-- The utterances of (3) are *Cole knows that C*, *Cole doesn't know that C*, *Cole thinks
that C*, *Cole doesn't think that C*, *C* and *not C*. -/
inductive Utt
  | knowPos | knowNeg | thinkPos | thinkNeg | cPos | cNeg
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨fun _ ↦ trivial⟩

/-- A complex utterance embeds the complement under an attitude verb. -/
def Utt.Complex (u : Utt) : Prop := u ≠ .cPos ∧ u ≠ .cNeg

instance : DecidablePred Utt.Complex := fun u ↦ inferInstanceAs (Decidable (u ≠ .cPos ∧ u ≠ .cNeg))

/-! ### Semantics and questions -/

/-- In the literal meanings (4), *know* is factive and *think* is not, and the simple
utterances assert the complement or its negation. -/
def literal : Utt → World → Prop
  | .knowPos => World.Knows
  | .knowNeg => (¬ World.Knows ·)
  | .thinkPos => World.Thinks
  | .thinkNeg => (¬ World.Thinks ·)
  | .cPos => (·.complement = true)
  | .cNeg => (·.complement = false)

instance (u : Utt) : DecidablePred (literal u) := by cases u <;> unfold literal <;> infer_instance

/-- The extension of an utterance. -/
def sem (u : Utt) : Finset World := Finset.univ.filter (literal u)

theorem sem_thinkNeg_ssubset_sem_knowNeg : sem .thinkNeg ⊂ sem .knowNeg := by decide

/-- The cell of a world under a question holds the worlds giving the same answer. -/
def cell (q : Question) (w : World) : Finset World :=
  Finset.univ.filter fun w' ↦ q.answer w' = q.answer w

theorem cell_preimage (q : Question) (w : World) : q.answer ⁻¹' {q.answer w} = ↑(cell q w) := by
  ext w'
  simp [cell]

/-! ### The literal listener within an assumption set (5) -/

/-- The literal listener within an assumption set (5) samples a world of the set at which the
utterance is true and returns its answer to the question. -/
noncomputable def L0 (A : Finset World) (q : Question) : Kernel Utt Bool :=
  (listener (Measure.count.restrict ↑A) (truthful fun u ↦ (↑(sem u) : Set World))).map q.answer

instance (A : Finset World) (q : Question) : IsFiniteKernel (L0 A q) :=
  inferInstanceAs (IsFiniteKernel (Kernel.map _ _))

/-- The literal listener counts the worlds of the assumption set at which the utterance is true
and the question's answer is the world's, over those at which the utterance is true. -/
def l0 (A : Finset World) (q : Question) (u : Utt) (w : World) : ℕ × ℕ :=
  (((A ∩ sem u).filter (· ∈ cell q w)).card, (A ∩ sem u).card)

theorem L0_apply (A : Finset World) (q : Question) (u : Utt) (w : World) :
    L0 A q u {q.answer w} = ((l0 A q u w).1 : ℝ≥0∞) / (l0 A q u w).2 := by
  have e1 : (↑(sem u) : Set World) ∩ ↑A = ↑(A ∩ sem u) := by ext; simp [and_comm]
  have e2 : (↑(sem u) : Set World) ∩ ↑(cell q w) ∩ ↑A = ↑((A ∩ sem u).filter (· ∈ cell q w)) := by
    ext; simp; tauto
  rw [L0, listener_truthful_map_apply_singleton, cell_preimage,
    Measure.restrict_apply .of_discrete, Measure.restrict_apply .of_discrete, e1, e2,
    Measure.count_apply_finset, Measure.count_apply_finset, l0]

theorem L0_knowNeg_eq_thinkNeg {A : Finset World} (hA : A ⊆ sem .cPos) (q : Question) :
    L0 A q .knowNeg = L0 A q .thinkNeg := by
  have h : A ∩ sem .knowNeg = A ∩ sem .thinkNeg := by
    ext w
    obtain ⟨b, c⟩ := w
    simp only [Finset.mem_inter, sem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨hw, hl⟩ <;> refine ⟨hw, ?_⟩ <;>
      have hc := (Finset.mem_filter.mp (hA hw)).2 <;>
      revert hc hl <;> cases b <;> cases c <;> decide
  refine Measure.ext_of_singleton fun b ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, q.answer w = b := by cases q <;> exact ⟨⟨b, b⟩, rfl⟩
  rw [L0_apply, L0_apply, l0, l0, h]

/-- Under the belief question, a speaker who assumes the complement answers fully with negated
*know* at a world in which Cole does not believe the complement. -/
theorem L0_knowNeg_bel_eq_one {A : Finset World} (hA : A ⊆ sem .cPos) {w : World} (hw : w ∈ A)
    (hb : w.believes = false) : L0 A .belief .knowNeg {Question.answer .belief w} = 1 := by
  rw [L0_apply, l0, Finset.filter_true_of_mem]
  · refine ENNReal.div_self ?_ (ENNReal.natCast_ne_top _)
    refine Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, ?_⟩⟩).ne'
    obtain ⟨b, c⟩ := w
    have hc := (Finset.mem_filter.mp (hA hw)).2
    simp only [World.believes] at hb
    subst hb
    revert hc
    cases c <;> decide
  · intro w' hw'
    obtain ⟨hw'A, hl⟩ := Finset.mem_inter.mp hw'
    have hc := (Finset.mem_filter.mp (hA hw'A)).2
    obtain ⟨b, c⟩ := w'
    obtain ⟨b₀, c₀⟩ := w
    simp only [World.believes] at hb
    subst hb
    simp only [cell, Question.answer, Finset.mem_filter, Finset.mem_univ, true_and]
    revert hc hl
    cases b <;> cases c <;> cases c₀ <;> decide

theorem L0_univ_bel_thinkNeg {w : World} (hb : w.believes = false) :
    L0 Finset.univ .belief .thinkNeg {Question.answer .belief w} = 1 := by
  obtain ⟨b, c⟩ := w
  simp only [World.believes] at hb
  subst hb
  rw [L0_apply,
    show l0 Finset.univ .belief .thinkNeg ⟨false, c⟩ = (2, 2) from by cases c <;> decide]
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem L0_univ_bel_knowNeg {w : World} (hb : w.believes = false) :
    L0 Finset.univ .belief .knowNeg {Question.answer .belief w} = 2 / 3 := by
  obtain ⟨b, c⟩ := w
  simp only [World.believes] at hb
  subst hb
  rw [L0_apply,
    show l0 Finset.univ .belief .knowNeg ⟨false, c⟩ = (2, 3) from by cases c <;> decide]
  norm_num

/-! ### The speaker (6) -/

/-- A simple utterance costs `k` and a complex one twice that (6). -/
def cost (k : ℝ) (u : Utt) : ℝ := if u.Complex then 2 * k else k

/-- The speaker within an assumption set (6) knows her world's answer to the question and is
informative about the literal listener's belief about it at rationality `α`, less the cost. -/
noncomputable def S1 (α k : ℝ) (A : Finset World) (q : Question) (w : World) : Measure Utt :=
  speaker α (cost k) (L0 A q) Measure.dirac (q.answer w)

instance (α k : ℝ) (A : Finset World) (q : Question) (w : World) :
    IsFiniteMeasure (S1 α k A q w) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

variable (α k : ℝ)

/-- A speaker who assumes the complement produces negated *know* and negated *think* alike
under either question, since they are equally informative and equally costly. -/
theorem S1_knowNeg_eq_thinkNeg {A : Finset World} (hA : A ⊆ sem .cPos) (q : Question) (w : World) :
    S1 α k A q w {.knowNeg} = S1 α k A q w {.thinkNeg} := by
  rw [S1, speaker_dirac_apply_singleton, speaker_dirac_apply_singleton, L0_knowNeg_eq_thinkNeg hA]
  rfl

/-- Without assumptions, a speaker addressing the belief question at a world in which Cole does
not believe the complement prefers negated *think* to negated *know*, since the stronger
utterance is the more informative. -/
theorem S1_univ_bel_knowNeg_lt_thinkNeg (hα : 0 < α) {w : World} (hb : w.believes = false) :
    (S1 α k Finset.univ .belief w).real {.knowNeg} <
      (S1 α k Finset.univ .belief w).real {.thinkNeg} := by
  have hc : cost k .thinkNeg = 2 * k := ite_eq_left (by decide)
  have hc' : cost k .knowNeg = 2 * k := ite_eq_left (by decide)
  rw [S1, speaker_dirac_real_singleton_lt_iff hα.le
      ⟨.thinkNeg, by rw [L0_univ_bel_thinkNeg hb]; exact one_ne_zero⟩, hc, hc',
    ENNReal.mul_lt_mul_iff_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top,
    L0_univ_bel_thinkNeg hb, L0_univ_bel_knowNeg hb, ENNReal.one_rpow, ← ENNReal.one_rpow α]
  refine ENNReal.rpow_lt_rpow ?_ hα
  rw [ENNReal.div_lt_iff (Or.inl three_ne_zero) (Or.inl (ENNReal.ofNat_ne_top)), one_mul]
  norm_num

/-- Under the belief question the speaker's choice depends on the world only through Cole's
belief, as the question's cells do. -/
theorem S1_bel_congr (A : Finset World) {w w' : World} (h : w.believes = w'.believes) :
    S1 α k A .belief w = S1 α k A .belief w' := by
  rw [S1, S1, show Question.answer .belief w = Question.answer .belief w' from h]

/-! ### The pragmatic listener (7) -/

/-- The listener's prior weighs a world with an assumption set containing it by the world prior
and the assumption prior. -/
noncomputable def pairPrior (μ : Measure World) (ν : Measure (Finset World)) :
    Measure (World × Finset World) :=
  (μ.prod ν).restrict {p | p.1 ∈ p.2}

variable (μ : Measure World) (ν : Measure (Finset World))

theorem pairPrior_singleton [SFinite ν] (w : World) (A : Finset World) :
    pairPrior μ ν {(w, A)} = if w ∈ A then μ {w} * ν {A} else 0 := by
  rw [pairPrior, Measure.restrict_apply (measurableSet_singleton _)]
  split_ifs with h
  · rw [Set.inter_eq_self_of_subset_left (s := ({(w, A)} : Set (World × Finset World)))
        (Set.singleton_subset_iff.mpr h),
      ← Set.singleton_prod_singleton, Measure.prod_prod]
  · rw [(Set.singleton_inter_eq_empty (a := (w, A))
        (s := {p : World × Finset World | p.1 ∈ p.2})).mpr h, measure_empty]

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (pairPrior μ ν) :=
  inferInstanceAs (IsFiniteMeasure ((μ.prod ν).restrict _))

/-- The pragmatic listener (7) hears the utterance under a known question and inverts the
speaker within each assumption set, over pairs of a world and an assumption set. -/
noncomputable def L1 (q : Question) : Kernel Utt (World × Finset World) :=
  listener (pairPrior μ ν) fun p ↦ S1 α k p.2 q p.1

theorem pairPrior_real [IsFiniteMeasure μ] [IsFiniteMeasure ν] (w : World) (A : Finset World) :
    (pairPrior μ ν).real {(w, A)} = if w ∈ A then μ.real {w} * ν.real {A} else 0 := by
  rw [measureReal_def, pairPrior_singleton]
  split_ifs <;> simp [measureReal_def, ENNReal.toReal_mul]

/-! ### The prior effect (2b) -/

section PriorEffect

variable (β γ : Measure Bool) (q : Question) (u : Utt)

/-- The listener's evidence for a value of the complement is the speaker's production of the
utterance at the worlds with that value, weighted by the belief prior and by the assumption
prior over the assumption sets containing them. It does not depend on the complement prior. -/
noncomputable def cWeight (c : Bool) : ℝ :=
  ∑ b, ∑ A, if ⟨b, c⟩ ∈ A then β.real {b} * ν.real {A} * (S1 α k A q ⟨b, c⟩).real {u} else 0

theorem cWeight_nonneg (c : Bool) : 0 ≤ cWeight α k ν β q u c :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by
    split_ifs
    · exact mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
    · exact le_rfl

private theorem sum_pairs (f : World × Finset World → ℝ) :
    ∑ p, f p = ∑ b, ∑ c, ∑ A, f (⟨b, c⟩, A) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

private theorem sum_pairs_c (f : World × Finset World → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : World × Finset World ↦ p.1.complement = true), f p
      = ∑ b, ∑ A, f (⟨b, true⟩, A) := by
  rw [Finset.sum_filter, sum_pairs]
  simp

variable [IsProbabilityMeasure β] [IsProbabilityMeasure γ] [IsProbabilityMeasure ν]

private theorem sum_real :
    ∑ p, (pairPrior (β.prod γ) ν).real {p} * (S1 α k p.2 q p.1).real {u}
      = γ.real {true} * cWeight α k ν β q u true + γ.real {false} * cWeight α k ν β q u false := by
  rw [sum_pairs, Finset.sum_comm, Fintype.sum_bool]
  simp only [pairPrior_real, Measure.prod_real_singleton, cWeight,
    Finset.mul_sum, mul_ite, mul_zero, ite_mul, zero_mul]
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun A _ ↦ ?_ <;>
    split_ifs <;> first | rfl | ring

-- fn. 11
theorem L1_c_real :
    (L1 α k (β.prod γ) ν q u).real {p | p.1.complement = true}
      = γ.real {true} * cWeight α k ν β q u true
        / (γ.real {true} * cWeight α k ν β q u true
          + γ.real {false} * cWeight α k ν β q u false) := by
  have hE : ({p : World × Finset World | p.1.complement = true} : Set _)
      = ↑(Finset.univ.filter fun p : World × Finset World ↦ p.1.complement = true) := by ext; simp
  rw [L1, hE, listener_real_finset, sum_real, sum_pairs_c]
  simp only [pairPrior_real, Measure.prod_real_singleton, cWeight,
    Finset.mul_sum, mul_ite, mul_zero, ite_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun A _ ↦ ?_
  split_ifs <;> first | rfl | ring

private theorem real_false_eq (ρ : Measure Bool) [IsProbabilityMeasure ρ] :
    ρ.real {false} = 1 - ρ.real {true} := by
  have h := probReal_univ (μ := ρ)
  rw [← Finset.coe_univ, ← sum_measureReal_singleton, Fintype.sum_bool] at h
  linarith

/-- The posterior probability of the complement rises with its prior probability (2b). -/
theorem L1_c_mono (γ' : Measure Bool) [IsProbabilityMeasure γ']
    (h : γ.real {true} ≤ γ'.real {true}) :
    (L1 α k (β.prod γ) ν q u).real {p | p.1.complement = true}
      ≤ (L1 α k (β.prod γ') ν q u).real {p | p.1.complement = true} := by
  have ha := cWeight_nonneg α k ν β q u true
  have hb := cWeight_nonneg α k ν β q u false
  have hx : 0 ≤ γ.real {true} := measureReal_nonneg
  have hx' : γ'.real {true} ≤ 1 := measureReal_le_one
  rw [L1_c_real, L1_c_real, real_false_eq γ, real_false_eq γ']
  set x := γ.real {true}
  set x' := γ'.real {true}
  set a := cWeight α k ν β q u true
  set b := cWeight α k ν β q u false
  have hd : 0 ≤ x * a + (1 - x) * b := by nlinarith
  have hd' : 0 ≤ x' * a + (1 - x') * b := by nlinarith
  rcases hd.eq_or_lt with hd | hd
  · rw [← hd, div_zero]
    exact div_nonneg (mul_nonneg (hx.trans h) ha) hd'
  rcases hd'.eq_or_lt with hd' | hd'
  · rw [show x * a = 0 by nlinarith, zero_div]
    exact div_nonneg (mul_nonneg (hx.trans h) ha) hd'.le
  · rw [div_le_div_iff₀ hd hd']
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 h)]

end PriorEffect

end ScontrasTonhauser2025
