module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Core.Probability.WeightOfEvidence
public import Linglib.Semantics.Focus.Particles

/-!
# Merin (1999): Information, Relevance, and Social Decisionmaking

Merin measures the relevance of a proposition `E` to a proposition `H` at issue by the logarithm
of the likelihood ratio, `log (μ[E | H] / μ[E | Hᶜ])`, the amount `E` adds to the logarithm of
the odds of `H`. That is `ProbabilityTheory.weightOfEvidence μ H E`, and this file formalizes the
paper's applications of it to *or*, *but*, *even* and *also*.

*Scalar implicature.* The paper licenses *X if not indeed Y* in a context when `Y` is more
relevant than `X`, and `X` positively so, to one side of the issue. When `A` and `B` are
independent on each side of the issue and each has positive finite relevance, the conjunction is
more relevant than either and than the disjunction, which is still positively relevant, so
*A (or B), if not indeed A and B* is licensed. The exclusive disjunction can then be negatively
relevant or irrelevant, and the disjunction can be as relevant as a disjunct, so that
*A or B, if not indeed A* is not licensed; these are shown on small models with counting
measures.

*But and even.* *A but B* needs an issue to which `A` is positively relevant and `B` and `A ∧ B`
negatively, and *A CONJ even(B)* one to which `A` is positively relevant and `B` more so; with one
issue for both they clash on the sign of `B`. For `A` and `B` independent on each side of the
issue, `B` is less probable given `A` than otherwise exactly when their relevance to the issue has
opposite nonzero signs. With `Bᶜ` as the issue that independence holds of any `A` and `B`, and `B`
is negatively relevant, infinitely relevant to the other side, unexpected given a positively
relevant `A`, and additive with it. A prior on which no instance of a predicate lowers the
probability of another then excludes *Qa but Qb*.

*Also.* A proposition is presupposed when conditioning on it changes nothing, equivalently when
it has probability one; it is then irrelevant to every open issue and its relevance adds to that of
any other proposition. The antecedent of *also* must have been relevant before it was presupposed,
so it cannot be the focus's own instance, cannot be properly accommodated, and is not a prima
facie cause of its host.

## Implementation notes

* Relevance is `ProbabilityTheory.weightOfEvidence`, an extended real that is `0` for a
  proposition of probability zero, as the paper stipulates after Carnap. A context is a measure
  and the proposition at issue, and that the issue is open is the pair of hypotheses `μ H ≠ 0`
  and `μ Hᶜ ≠ 0` where a statement needs them; the paper's sign of relevance is `SignType.sign`.
* Independence on each side of the issue is `IndepSet` at the measures conditioned on `H` and on
  `Hᶜ`.
* The earlier state of the definition of topic-anaphoric salience is a second measure with the
  same issue; that it is the last one before the antecedent became presupposed is not modelled.
* The second clause of the prediction for *A (or B), if not indeed A and B* is formalized with
  the conjunction as `Y`.

## TODO

* That the disjunction is more relevant than the exclusive disjunction.
* The paper's definitions of protentive speaker meaning and of claims and implicatures as sets of
  relevant propositions, with the results stated for them.

## References

* [merin-1999-relevance]
* [anscombre-ducrot-1977]
* [karttunen-peters-1979]
* [kay-1990]
* [francescotti-1995]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace Merin1999a

variable {W : Type*} [MeasurableSpace W]

/-! ### Relevance for independent confirmers -/

section Confirmers

variable {μ : Measure W} {H a b : Set W}

/-- The antecedent of Theorem 6: `A` and `B` are independent given `H` and given its complement
(Definition 9), and each has positive finite relevance to `H`. -/
structure IndepConfirmers (μ : Measure W) (H a b : Set W) : Prop where
  indep : IndepSet a b μ[|H]
  indep_compl : IndepSet a b μ[|Hᶜ]
  pos_left : 0 < weightOfEvidence μ H a
  pos_right : 0 < weightOfEvidence μ H b
  lt_top_left : weightOfEvidence μ H a < ⊤
  lt_top_right : weightOfEvidence μ H b < ⊤

private theorem cond_compl_ne_zero (hp : 0 < weightOfEvidence μ H a)
    (ht : weightOfEvidence μ H a < ⊤) : μ[a | Hᶜ] ≠ 0 := fun h₀ ↦
  ht.ne (weightOfEvidence_eq_top_iff.2
    ⟨(h₀ ▸ weightOfEvidence_pos_iff.1 hp).ne_bot, h₀⟩)

private lemma max_div_gt_or_div (pAH pBH pAnH pBnH : ℝ)
    (h1 : 0 < pAnH) (h2 : 0 < pBnH)
    (h3 : pAnH < pAH) (h4 : pBnH < pBH)
    (h5 : pAnH < 1) (h6 : pBnH < 1)
    (_h7 : pAH ≤ 1) (h8 : pBH ≤ 1) :
    max (pAH / pAnH) (pBH / pBnH) >
      (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) ∧
    (pAH + pBH - pAH * pBH) / (pAnH + pBnH - pAnH * pBnH) > 1 := by
  have hden_pos : pAnH + pBnH - pAnH * pBnH > 0 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [gt_iff_lt, max_def]; split
    · rename_i hge
      rw [div_lt_div_iff₀ hden_pos h2]
      have h_cross := (div_le_div_iff₀ h1 h2).mp hge
      nlinarith [mul_pos (mul_pos h2 (show (0:ℝ) < pBH by linarith))
        (show pAH - pAnH > 0 from by linarith)]
    · rename_i hlt; push Not at hlt
      rw [div_lt_div_iff₀ hden_pos h1]
      have h_cross := (div_le_div_iff₀ h2 h1).mp (le_of_lt hlt)
      nlinarith [mul_pos (mul_pos h1 (show (0:ℝ) < pAH by linarith))
        (show pBH - pBnH > 0 from by linarith)]
  · rw [gt_iff_lt, one_lt_div hden_pos]
    nlinarith

-- Theorem 6a for a pair of probability measures and two events independent under both
theorem likelihoodRatio_bounds {P Q : Measure W} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hbm : MeasurableSet b) (h₁ : IndepSet a b P) (h₂ : IndepSet a b Q)
    (ha : 1 < P a / Q a) (hb : 1 < P b / Q b) (hQa : Q a ≠ 0) (hQb : Q b ≠ 0) :
    max (P a / Q a) (P b / Q b) < P (a ∩ b) / Q (a ∩ b) ∧
      P (a ∪ b) / Q (a ∪ b) < max (P a / Q a) (P b / Q b) ∧ 1 < P (a ∪ b) / Q (a ∪ b) := by
  have hlt {s : Set W} (hs : 1 < P s / Q s) (h0 : Q s ≠ 0) : Q.real s < P.real s :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 <| by
      simpa using (ENNReal.lt_div_iff_mul_lt (.inl h0) (.inl (measure_ne_top _ _))).1 hs
  have hfin {s : Set W} (h0 : Q s ≠ 0) : P s / Q s ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) h0
  have hQu : Q (a ∪ b) ≠ 0 := fun h0 ↦ hQa (measure_mono_null subset_union_left h0)
  have hA := hlt ha hQa
  have hB := hlt hb hQb
  have harith := max_div_gt_or_div _ _ _ _ (ENNReal.toReal_pos hQa (measure_ne_top _ _))
    (ENNReal.toReal_pos hQb (measure_ne_top _ _)) hA hB (hA.trans_le measureReal_le_one)
    (hB.trans_le measureReal_le_one) measureReal_le_one measureReal_le_one
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁.measure_inter_eq_mul, h₂.measure_inter_eq_mul,
      ENNReal.mul_div_mul_comm (.inr (measure_ne_top _ _)) (.inl (measure_ne_top _ _)),
      max_lt_iff]
    exact ⟨by simpa using ENNReal.mul_lt_mul_right (zero_lt_one.trans ha).ne' (hfin hQa) hb,
      by simpa using ENNReal.mul_lt_mul_left (zero_lt_one.trans hb).ne' (hfin hQb) ha⟩
  · rw [← ENNReal.toReal_lt_toReal (hfin hQu) (max_ne_top (hfin hQa) (hfin hQb)),
      ENNReal.toReal_max (hfin hQa) (hfin hQb), ENNReal.toReal_div, ENNReal.toReal_div,
      ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, h₁.measureReal_union hbm,
      h₂.measureReal_union hbm]
    exact harith.1
  · rw [← ENNReal.toReal_lt_toReal ENNReal.one_ne_top (hfin hQu), ENNReal.toReal_one,
      ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, h₁.measureReal_union hbm,
      h₂.measureReal_union hbm]
    exact harith.2

/-- Theorem 6a: for independent finite confirmers `A` and `B` of `H`, the conjunction is more
relevant than either, and the disjunction is less relevant than the more relevant of the two and
still positively relevant. -/
theorem IndepConfirmers.max_lt_inter_and_union_lt_max [IsFiniteMeasure μ]
    (hbm : MeasurableSet b) (h : IndepConfirmers μ H a b) :
    max (weightOfEvidence μ H a) (weightOfEvidence μ H b) < weightOfEvidence μ H (a ∩ b) ∧
      weightOfEvidence μ H (a ∪ b) < max (weightOfEvidence μ H a) (weightOfEvidence μ H b) ∧
      0 < weightOfEvidence μ H (a ∪ b) := by
  have hQa := cond_compl_ne_zero h.pos_left h.lt_top_left
  have hQb := cond_compl_ne_zero h.pos_right h.lt_top_right
  have hPa := weightOfEvidence_pos_iff.1 h.pos_left
  have hPb := weightOfEvidence_pos_iff.1 h.pos_right
  have hH : μ H ≠ 0 := fun h₀ ↦ by simp [cond_eq_zero_of_meas_eq_zero h₀] at hPa
  have hH' : μ Hᶜ ≠ 0 := fun h₀ ↦ hQa (by simp [cond_eq_zero_of_meas_eq_zero h₀])
  have := cond_isProbabilityMeasure hH
  have := cond_isProbabilityMeasure hH'
  have ha₀ : μ a ≠ 0 := fun h₀ ↦ hQa (cond_absolutelyContinuous h₀)
  have hb₀ : μ b ≠ 0 := fun h₀ ↦ hQb (cond_absolutelyContinuous h₀)
  have hu₀ : μ (a ∪ b) ≠ 0 := fun h₀ ↦ ha₀ (measure_mono_null subset_union_left h₀)
  have hi₀ : μ (a ∩ b) ≠ 0 := fun h₀ ↦ by
    have := cond_absolutelyContinuous (μ := μ) (s := H) h₀
    rw [h.indep.measure_inter_eq_mul, mul_eq_zero] at this
    exact this.elim (fun h' ↦ (h' ▸ hPa).ne_bot rfl) fun h' ↦ (h' ▸ hPb).ne_bot rfl
  have one_lt {e : Set W} (he : μ[e | Hᶜ] < μ[e | H]) : 1 < μ[e | H] / μ[e | Hᶜ] := by
    rwa [ENNReal.lt_div_iff_mul_lt (.inr ENNReal.one_ne_top) (.inr one_ne_zero), one_mul]
  have key := likelihoodRatio_bounds hbm h.indep h.indep_compl (one_lt hPa) (one_lt hPb) hQa hQb
  rw [weightOfEvidence_of_measure_ne_zero ha₀, weightOfEvidence_of_measure_ne_zero hb₀,
    weightOfEvidence_of_measure_ne_zero hu₀, weightOfEvidence_of_measure_ne_zero hi₀,
    ← ENNReal.log_monotone.map_max, ENNReal.log_lt_log_iff, ENNReal.log_lt_log_iff,
    ENNReal.zero_lt_log_iff]
  exact key

/-! ### Scalar implicature -/

/-- Hypothesis 3: the condition a context must meet for *X if not indeed Y*, that `X` is
positively relevant, and `Y` more so, to `H` or to its complement. The schema is acceptable iff
every context in which `X` and `Y` are independent on each side of the issue with finite
relevance meets it. -/
def IfNotIndeed (μ : Measure W) (H x y : Set W) : Prop :=
  (0 < weightOfEvidence μ H x ∧ weightOfEvidence μ H x < weightOfEvidence μ H y) ∨
    (0 < weightOfEvidence μ Hᶜ x ∧ weightOfEvidence μ Hᶜ x < weightOfEvidence μ Hᶜ y)

-- Prediction 2
theorem IndepConfirmers.ifNotIndeed_inter [IsFiniteMeasure μ] (hbm : MeasurableSet b)
    (h : IndepConfirmers μ H a b) :
    IfNotIndeed μ H (a ∪ b) (a ∩ b) ∧ IfNotIndeed μ H a (a ∩ b) :=
  have ⟨hi, hu, hu₀⟩ := h.max_lt_inter_and_union_lt_max hbm
  ⟨.inl ⟨hu₀, hu.trans hi⟩, .inl ⟨h.pos_left, (le_max_left _ _).trans_lt hi⟩⟩

end Confirmers

/-! Under the counting measure on a finite type the two sides of an issue are uniform measures,
and conditional probabilities are proportions. -/

section Count

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  {s t u : Set V}

private theorem cond_count_real (s t : Set V) :
    (Measure.count[|s]).real t = (s ∩ t).ncard / s.ncard :=
  uniformOn_real_apply s t

private theorem cond_count_lt_iff {s' t' : Set V} :
    Measure.count[t | s] < Measure.count[t' | s'] ↔
      ((s ∩ t).ncard / s.ncard : ℝ) < (s' ∩ t').ncard / s'.ncard := by
  rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, cond_count_real, cond_count_real]

private theorem cond_count_ne_zero (h : (s ∩ t).Nonempty) : Measure.count[t | s] ≠ 0 :=
  (uniformOn_ne_zero_iff (toFinite s)).2 h

private theorem likelihoodRatio_count_lt_iff (ht : (sᶜ ∩ t).Nonempty) (hu : (sᶜ ∩ u).Nonempty) :
    Measure.count[t | s] / Measure.count[t | sᶜ] < Measure.count[u | s] / Measure.count[u | sᶜ] ↔
      ((s ∩ t).ncard / s.ncard : ℝ) / ((sᶜ ∩ t).ncard / sᶜ.ncard) <
        (s ∩ u).ncard / s.ncard / ((sᶜ ∩ u).ncard / sᶜ.ncard) := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (measure_ne_top _ _) (cond_count_ne_zero ht))
      (ENNReal.div_ne_top (measure_ne_top _ _) (cond_count_ne_zero hu)),
    ENNReal.toReal_div, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, cond_count_real, cond_count_real, cond_count_real,
    cond_count_real]

end Count

/-! #### Theorem 6b -/

/-- The worlds of the first countermodel: at `issue`, the only world where `H` holds, `A` and `B`
both hold; at `off a b`, `A` holds iff `a` and `B` iff `b`. -/
inductive World₁ where
  | issue
  | off (a b : Bool)
  deriving DecidableEq, Fintype

instance : MeasurableSpace World₁ := ⊤
instance : DiscreteMeasurableSpace World₁ := ⟨fun _ ↦ trivial⟩

/-- Whether `A` holds at a world of the first countermodel. -/
def World₁.a : World₁ → Bool
  | .issue => true
  | .off a _ => a

/-- Whether `B` holds at a world of the first countermodel. -/
def World₁.b : World₁ → Bool
  | .issue => true
  | .off _ b => b

private abbrev H₁ : Set World₁ := {w | w = .issue}
private abbrev A₁ : Set World₁ := {w | w.a}
private abbrev B₁ : Set World₁ := {w | w.b}

private theorem ncard₁ :
    H₁.ncard = 1 ∧ H₁ᶜ.ncard = 4 ∧ (H₁ ∩ A₁).ncard = 1 ∧ (H₁ᶜ ∩ A₁).ncard = 2 ∧
      (H₁ ∩ B₁).ncard = 1 ∧ (H₁ᶜ ∩ B₁).ncard = 2 ∧ (H₁ ∩ (A₁ ∩ B₁)).ncard = 1 ∧
      (H₁ᶜ ∩ (A₁ ∩ B₁)).ncard = 1 ∧ (H₁ ∩ (A₁ ∆ B₁)).ncard = 0 ∧
      (H₁ᶜ ∩ (A₁ ∆ B₁)).ncard = 2 := by
  simp only [Set.symmDiff_def, Set.ncard_eq_toFinset_card']
  decide

private theorem indepConfirmers₁ : IndepConfirmers .count H₁ A₁ B₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := ncard₁
  refine ⟨(indepSet_uniformOn_iff H₁).2 ?_, (indepSet_uniformOn_iff H₁ᶜ).2 ?_,
    weightOfEvidence_pos_iff.2 (cond_count_lt_iff.2 ?_),
    weightOfEvidence_pos_iff.2 (cond_count_lt_iff.2 ?_),
    weightOfEvidence_lt_top (cond_count_ne_zero ⟨.off true false, by simp [World₁.a]⟩),
    weightOfEvidence_lt_top (cond_count_ne_zero ⟨.off false true, by simp [World₁.b]⟩)⟩
  · rw [h7, h1, h3, h5]
  · rw [h8, h2, h4, h6]
  · rw [h1, h2, h3, h4]; norm_num
  · rw [h1, h2, h5, h6]; norm_num

-- Theorem 6b, first clause
theorem exists_weightOfEvidence_symmDiff_neg :
    ∃ (μ : Measure World₁) (H a b : Set World₁),
      IndepConfirmers μ H a b ∧ weightOfEvidence μ H (a ∆ b) < 0 := by
  refine ⟨_, _, _, _, indepConfirmers₁,
    (weightOfEvidence_neg_iff .of_discrete).2 (cond_count_lt_iff.2 ?_)⟩
  obtain ⟨h1, h2, -, -, -, -, -, -, h9, h10⟩ := ncard₁
  rw [h1, h2, h9, h10]; norm_num

/-- The worlds of the second countermodel: at `issue a`, where `H` holds, `A` holds iff `a` and
`B` holds; at `off i b`, `A` holds iff `i = 0` and `B` iff `b`. -/
inductive World₂ where
  | issue (a : Bool)
  | off (i : Fin 3) (b : Bool)
  deriving DecidableEq, Fintype

instance : MeasurableSpace World₂ := ⊤
instance : DiscreteMeasurableSpace World₂ := ⟨fun _ ↦ trivial⟩

/-- Whether `H` holds at a world of the second countermodel. -/
def World₂.h : World₂ → Bool
  | .issue _ => true
  | .off _ _ => false

/-- Whether `A` holds at a world of the second countermodel. -/
def World₂.a : World₂ → Bool
  | .issue a => a
  | .off i _ => i = 0

/-- Whether `B` holds at a world of the second countermodel. -/
def World₂.b : World₂ → Bool
  | .issue _ => true
  | .off _ b => b

private abbrev H₂ : Set World₂ := {w | w.h}
private abbrev A₂ : Set World₂ := {w | w.a}
private abbrev B₂ : Set World₂ := {w | w.b}

private theorem ncard₂ :
    H₂.ncard = 2 ∧ H₂ᶜ.ncard = 6 ∧ (H₂ ∩ A₂).ncard = 1 ∧ (H₂ᶜ ∩ A₂).ncard = 2 ∧
      (H₂ ∩ B₂).ncard = 2 ∧ (H₂ᶜ ∩ B₂).ncard = 3 ∧ (H₂ ∩ (A₂ ∩ B₂)).ncard = 1 ∧
      (H₂ᶜ ∩ (A₂ ∩ B₂)).ncard = 1 ∧ (H₂ ∩ (A₂ ∪ B₂)).ncard = 2 ∧
      (H₂ᶜ ∩ (A₂ ∪ B₂)).ncard = 4 ∧ (H₂ ∩ (A₂ ∆ B₂)).ncard = 1 ∧
      (H₂ᶜ ∩ (A₂ ∆ B₂)).ncard = 3 := by
  simp only [Set.symmDiff_def, Set.ncard_eq_toFinset_card']
  decide

private theorem indepConfirmers₂ : IndepConfirmers .count H₂ A₂ B₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := ncard₂
  refine ⟨(indepSet_uniformOn_iff H₂).2 ?_, (indepSet_uniformOn_iff H₂ᶜ).2 ?_,
    weightOfEvidence_pos_iff.2 (cond_count_lt_iff.2 ?_),
    weightOfEvidence_pos_iff.2 (cond_count_lt_iff.2 ?_),
    weightOfEvidence_lt_top (cond_count_ne_zero ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩),
    weightOfEvidence_lt_top (cond_count_ne_zero ⟨.off 1 true, by simp [World₂.h, World₂.b]⟩)⟩
  · rw [h7, h1, h3, h5]
  · rw [h8, h2, h4, h6]
  · rw [h1, h2, h3, h4]; norm_num
  · rw [h1, h2, h5, h6]; norm_num

-- Theorem 6b, second clause
theorem exists_not_weightOfEvidence_symmDiff_neg :
    ∃ (μ : Measure World₂) (H a b : Set World₂),
      IndepConfirmers μ H a b ∧ ¬ weightOfEvidence μ H (a ∆ b) < 0 := by
  refine ⟨_, _, _, _, indepConfirmers₂, fun h ↦ ?_⟩
  obtain ⟨h1, h2, -, -, -, -, -, -, -, -, h11, h12⟩ := ncard₂
  have := cond_count_lt_iff.1 ((weightOfEvidence_neg_iff .of_discrete).1 h)
  rw [h1, h2, h11, h12] at this
  norm_num at this

/-- Prediction 1: independent finite confirmers need not license *A or B, if not indeed A*, since
neither condition of Hypothesis 3 need hold (Theorem 6b, third clause). -/
theorem exists_not_ifNotIndeed_union :
    ∃ (μ : Measure World₂) (H a b : Set World₂),
      IndepConfirmers μ H a b ∧ ¬ IfNotIndeed μ H (a ∪ b) a := by
  refine ⟨_, _, _, _, indepConfirmers₂, ?_⟩
  obtain ⟨h1, h2, h3, h4, -, -, -, -, h9, h10, -⟩ := ncard₂
  have hu : (H₂ᶜ ∩ (A₂ ∪ B₂)).Nonempty := ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩
  have ha : (H₂ᶜ ∩ A₂).Nonempty := ⟨.off 0 false, by simp [World₂.h, World₂.a]⟩
  have hne {e : Set World₂} (he : (H₂ᶜ ∩ e).Nonempty) : Measure.count e ≠ 0 :=
    (Measure.count_ne_zero_iff.2 (he.mono inter_subset_right))
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · rw [weightOfEvidence_lt_weightOfEvidence_iff (hne hu) (hne ha),
      likelihoodRatio_count_lt_iff hu ha, h1, h2, h3, h4, h9, h10] at h
    norm_num at h
  · have := cond_count_lt_iff.1 (weightOfEvidence_pos_iff.1 h)
    rw [compl_compl, h1, h2, h9, h10] at this
    norm_num at this

/-! ### *But* and *even* -/

section But

variable {μ : Measure W} {H a b : Set W}

/-- Hypothesis 4: *A but B* is felicitous only if, for the issue `H`, `A` is positively relevant
and `B` and `A ∧ B` negatively relevant. -/
def ButFelicitous (μ : Measure W) (H a b : Set W) : Prop :=
  0 < weightOfEvidence μ H a ∧ weightOfEvidence μ H b < 0 ∧ weightOfEvidence μ H (a ∩ b) < 0

/-- Hypothesis 5: *A CONJ even(B)* with VP-focus is felicitous only if, for an issue `H` other
than `B`, `A` is positively relevant to `H` and `B` more relevant than `A`: the scalar
presupposition of *even* with relevance for likelihood, over the one alternative `A`. -/
def EvenFelicitous (μ : Measure W) (H a b : Set W) : Prop :=
  H ≠ b ∧ 0 < weightOfEvidence μ H a ∧
    Focus.evenPresup (fun e ↦ OrderDual.toDual (weightOfEvidence μ H e)) b {a}

/-- Prediction 3: with one issue for both, no sentence is felicitous as *A but B* and as
*A CONJ even(B)*. -/
theorem not_butFelicitous_and_evenFelicitous (μ : Measure W) (H a b : Set W) :
    ¬ (ButFelicitous μ H a b ∧ EvenFelicitous μ H a b) := by
  rintro ⟨⟨-, hb, -⟩, -, ha, he⟩
  exact lt_irrefl _ ((ha.trans (OrderDual.toDual_lt_toDual.mp (he a rfl))).trans hb)

private theorem mul_neg_iff_sign {x y : ℝ} :
    x * y < 0 ↔ SignType.sign x = -SignType.sign y ∧ SignType.sign y ≠ 0 := by
  rw [← sign_eq_neg_one_iff, sign_mul]
  generalize SignType.sign x = s
  generalize SignType.sign y = t
  revert s t
  decide

/-- Theorem 8: for `A` and `B` independent given `H` and given its complement, `B` is less
probable given `A` than otherwise exactly when the relevance of `A` and of `B` to `H` have
opposite nonzero signs. -/
theorem cond_lt_iff_sign_eq_neg [IsProbabilityMeasure μ] (hH : MeasurableSet H)
    (ha : MeasurableSet a) (hcH : μ H ≠ 0) (hcH' : μ Hᶜ ≠ 0) (h : IndepSet a b μ[|H])
    (h' : IndepSet a b μ[|Hᶜ]) (ha₀ : μ a ≠ 0) :
    μ[b | a] < μ b ↔
      SignType.sign (weightOfEvidence μ H a) = -SignType.sign (weightOfEvidence μ H b) ∧
        SignType.sign (weightOfEvidence μ H b) ≠ 0 := by
  have hp : 0 < μ.real H * μ.real Hᶜ :=
    mul_pos (ENNReal.toReal_pos hcH (measure_ne_top _ _))
      (ENNReal.toReal_pos hcH' (measure_ne_top _ _))
  rw [sign_weightOfEvidence hH, sign_weightOfEvidence hH, ← mul_neg_iff_sign,
    ← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def, cond_real_apply μ ha b,
    div_lt_iff₀ (show 0 < μ.real a from ENNReal.toReal_pos ha₀ (measure_ne_top _ _)), ← sub_neg,
    mul_comm (μ.real b),
    measureReal_inter_sub_mul_of_indepSet_cond hH hcH hcH' h h', mul_assoc]
  exact ⟨fun h ↦ neg_of_mul_neg_right h hp.le, mul_neg_of_pos_of_neg hp⟩

-- Theorem 9
theorem indepSet_cond_compl_self [IsFiniteMeasure μ] (ha : MeasurableSet a)
    (hb : MeasurableSet b) : IndepSet a b μ[|bᶜ] ∧ IndepSet a b μ[|bᶜᶜ] :=
  ⟨indepSet_of_measure_eq_zero_right ha hb (by simp [cond_apply hb.compl]),
    indepSet_of_measure_compl_eq_zero_right ha hb (by simp [cond_apply hb])⟩

-- Theorem 10 (a)
theorem weightOfEvidence_compl_self_neg [IsFiniteMeasure μ] (hb : MeasurableSet b)
    (hb₀ : μ b ≠ 0) : weightOfEvidence μ bᶜ b < 0 := by
  rw [weightOfEvidence_neg_iff hb.compl, compl_compl, cond_apply_self hb₀ (measure_ne_top _ _),
    cond_apply hb.compl, compl_inter_self, measure_empty, mul_zero]
  exact zero_lt_one

-- Theorem 10 (b)
theorem weightOfEvidence_compl_lt_compl_compl [IsFiniteMeasure μ] (hb : MeasurableSet b)
    (hab : μ (a ∩ b) ≠ 0) :
    weightOfEvidence μ bᶜ a < weightOfEvidence μ bᶜᶜ b ∧
      weightOfEvidence μ bᶜ a < weightOfEvidence μ bᶜᶜ (a ∩ b) := by
  have hb₀ : μ b ≠ 0 := fun h ↦ hab (measure_mono_null inter_subset_right h)
  have hnull (e : Set W) (he : e ⊆ b) : μ[e | bᶜ] = 0 := by
    rw [cond_apply hb.compl, disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right he),
      measure_empty, mul_zero]
  have hne (e : Set W) (he : μ (b ∩ e) ≠ 0) : μ[e | b] ≠ 0 := by
    rw [cond_apply hb]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) he
  have hfin : weightOfEvidence μ bᶜ a < ⊤ :=
    weightOfEvidence_lt_top (by rw [compl_compl]; exact hne a (by rwa [inter_comm]))
  have htop (e : Set W) (he : e ⊆ b) (he₀ : μ (b ∩ e) ≠ 0) : weightOfEvidence μ bᶜᶜ e = ⊤ :=
    weightOfEvidence_eq_top_iff.2 (by rw [compl_compl]; exact ⟨hne e he₀, hnull e he⟩)
  rw [htop b subset_rfl (by rwa [inter_self]),
    htop (a ∩ b) inter_subset_right (by rwa [inter_eq_right.2 inter_subset_right])]
  exact ⟨hfin, hfin⟩

-- Theorem 10 (c)
theorem cond_lt_of_weightOfEvidence_compl_pos [IsProbabilityMeasure μ] (ha : MeasurableSet a)
    (hb : MeasurableSet b) (hpos : 0 < weightOfEvidence μ bᶜ a) (hab : μ (a ∩ b) ≠ 0) :
    μ[b | a] < μ b := by
  have ha₀ : μ a ≠ 0 := fun h ↦ hab (measure_mono_null inter_subset_left h)
  have hb₀ : μ b ≠ 0 := fun h ↦ hab (measure_mono_null inter_subset_right h)
  have hbc : μ bᶜ ≠ 0 := fun h ↦ by
    simpa [cond_eq_zero_of_meas_eq_zero h] using weightOfEvidence_pos_iff.1 hpos
  have hi := indepSet_cond_compl_self (μ := μ) ha hb
  rw [cond_lt_iff_sign_eq_neg hb.compl ha hbc (by rwa [compl_compl]) hi.1 hi.2 ha₀,
    sign_pos hpos, sign_neg (weightOfEvidence_compl_self_neg hb hb₀)]
  decide

-- Theorem 10 (d)
theorem weightOfEvidence_compl_inter [IsFiniteMeasure μ] (ha : MeasurableSet a)
    (hb : MeasurableSet b) (hab : μ (a ∩ b) ≠ 0) :
    weightOfEvidence μ bᶜ (a ∩ b) = weightOfEvidence μ bᶜ a + weightOfEvidence μ bᶜ b :=
  have hi := indepSet_cond_compl_self (μ := μ) ha hb
  weightOfEvidence_inter hi.1 hi.2 hab

/-- Definition 10: the prior satisfies non-negative instantial relevance for a predicate `Q` when
no instance `Qa` makes another instance `Qb` less probable. -/
def NonnegInstantialRelevance {E : Type*} (μ : Measure W) (Q : E → Set W) : Prop :=
  ∀ i j, μ (Q j) ≤ μ[|Q i] (Q j)

-- Corollary 11, Theorem 8
theorem not_butFelicitous_of_nonnegInstantialRelevance {E : Type*} [IsProbabilityMeasure μ]
    {Q : E → Set W} (hQ : NonnegInstantialRelevance μ Q) {i j : E} (hH : MeasurableSet H)
    (hm : MeasurableSet (Q i)) (hcH : μ H ≠ 0) (hcH' : μ Hᶜ ≠ 0)
    (h : IndepSet (Q i) (Q j) μ[|H]) (h' : IndepSet (Q i) (Q j) μ[|Hᶜ]) (hi : μ (Q i) ≠ 0) :
    ¬ ButFelicitous μ H (Q i) (Q j) := fun hbut ↦
  (hQ i j).not_gt ((cond_lt_iff_sign_eq_neg hH hm hcH hcH' h h' hi).2
    (by rw [sign_pos hbut.1, sign_neg hbut.2.1]; decide))

-- Corollary 11, Theorem 9
theorem not_butFelicitous_compl {E : Type*} [IsProbabilityMeasure μ] {Q : E → Set W}
    (hQ : NonnegInstantialRelevance μ Q) {i j : E} (hmi : MeasurableSet (Q i))
    (hmj : MeasurableSet (Q j)) (hi : μ (Q i) ≠ 0) (hj : μ (Q j) ≠ 0) (hjc : μ (Q j)ᶜ ≠ 0) :
    ¬ ButFelicitous μ (Q j)ᶜ (Q i) (Q j) :=
  have hind := indepSet_cond_compl_self (μ := μ) hmi hmj
  not_butFelicitous_of_nonnegInstantialRelevance hQ hmj.compl hmi hjc (by rwa [compl_compl])
    hind.1 hind.2 hi

end But

/-! ### *Also* -/

section Also

variable {μ μ₀ : Measure W} {H a b d e : Set W}

/-- Definition 12: `A` is presupposed when conditioning on `A` changes no probability. -/
def IsPresupposed (μ : Measure W) (a : Set W) : Prop :=
  μ[|a] = μ

theorem isPresupposed_iff [IsProbabilityMeasure μ] (ha : MeasurableSet a) :
    IsPresupposed μ a ↔ μ a = 1 := by
  constructor
  · intro h
    have h0 : μ a ≠ 0 := fun h0 ↦ by
      have := congrArg (· Set.univ) h
      simp [cond_eq_zero_of_meas_eq_zero h0] at this
    calc μ a = μ[|a] a := by rw [h]
      _ = 1 := cond_apply_self h0 (measure_ne_top _ _)
  · intro h1
    rw [IsPresupposed, cond_congr_set (ae_eq_univ.2 ((prob_compl_eq_zero_iff ha).2 h1)),
      cond_univ]

theorem IsPresupposed.cond_eq_one [IsProbabilityMeasure μ] {s : Set W} (h : IsPresupposed μ a)
    (ha : MeasurableSet a) (hs : MeasurableSet s) (h0 : μ s ≠ 0) : μ[a | s] = 1 := by
  rw [cond_apply hs, measure_inter_conull ((prob_compl_eq_zero_iff ha).mpr
    ((isPresupposed_iff ha).mp h)), ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]

theorem IsPresupposed.weightOfEvidence_eq_zero [IsProbabilityMeasure μ] (h : IsPresupposed μ a)
    (ha : MeasurableSet a) (hH : MeasurableSet H) (hcH : μ H ≠ 0) (hcH' : μ Hᶜ ≠ 0) :
    weightOfEvidence μ H a = 0 := by
  rw [weightOfEvidence_eq_zero_iff hH, h.cond_eq_one ha hH hcH, h.cond_eq_one ha hH.compl hcH']

-- Fact 17
theorem IsPresupposed.weightOfEvidence_inter [IsProbabilityMeasure μ] (h : IsPresupposed μ a)
    (ha : MeasurableSet a) (hH : MeasurableSet H) (hcH : μ H ≠ 0) (hcH' : μ Hᶜ ≠ 0)
    (b : Set W) :
    weightOfEvidence μ H (a ∩ b) = weightOfEvidence μ H a + weightOfEvidence μ H b := by
  have hc := (prob_compl_eq_zero_iff ha).mpr ((isPresupposed_iff ha).mp h)
  rw [h.weightOfEvidence_eq_zero ha hH hcH hcH', zero_add]
  exact weightOfEvidence_congr (Filter.inter_eventuallyEqSet_right.2
    ((measure_eq_zero_iff_ae_notMem.1 hc).mono fun x hx _ ↦ not_not.1 hx))

/-- Definition 13: `D` is topic-anaphorically salient for `E` when `E` is relevant to the issue,
`D` is presupposed, and in an earlier state `μ₀`, where `D` was not yet presupposed, `D` was
relevant to the issue. -/
structure TopicAnaphoricallySalient (μ₀ μ : Measure W) (H d e : Set W) : Prop where
  relevant : weightOfEvidence μ H e ≠ 0
  presupposed : IsPresupposed μ d
  lt_one : μ₀ d < 1
  wasRelevant : weightOfEvidence μ₀ H d ≠ 0

/-- Hypothesis 8, *(and) also*: also(b, B) is felicitous only if `Ba` is topic-anaphorically
salient for `Bb` and `Ba` had, when it was relevant, the sign of relevance `Bb` has now. -/
def AlsoFelicitous (μ₀ μ : Measure W) (H ba bb : Set W) : Prop :=
  TopicAnaphoricallySalient μ₀ μ H ba bb ∧
    SignType.sign (weightOfEvidence μ₀ H ba) = SignType.sign (weightOfEvidence μ H bb)

/-- Hypothesis 8, *but also*: the signs are opposite. -/
def ButAlsoFelicitous (μ₀ μ : Measure W) (H ba bb : Set W) : Prop :=
  TopicAnaphoricallySalient μ₀ μ H ba bb ∧
    SignType.sign (weightOfEvidence μ₀ H ba) = -SignType.sign (weightOfEvidence μ H bb)

/-- Corollary 15: the antecedent of *also* is not the focus's own instance, which would be
presupposed and so irrelevant. -/
theorem TopicAnaphoricallySalient.ne {E : Type*} [IsProbabilityMeasure μ] {B : E → Set W}
    {i j : E} (h : TopicAnaphoricallySalient μ₀ μ H (B i) (B j)) (hm : MeasurableSet (B i))
    (hH : MeasurableSet H) (hcH : μ H ≠ 0) (hcH' : μ Hᶜ ≠ 0) : i ≠ j := by
  rintro rfl
  exact h.relevant (h.presupposed.weightOfEvidence_eq_zero hm hH hcH hcH')

/-- Partial Definition 14: `φ` is properly accommodable only if it is contingent and irrelevant
to the issue. -/
def ProperlyAccommodable (μ : Measure W) (H φ : Set W) : Prop :=
  0 < μ φ ∧ μ φ < 1 ∧ weightOfEvidence μ H φ = 0

theorem TopicAnaphoricallySalient.not_properlyAccommodable
    (h : TopicAnaphoricallySalient μ₀ μ H d e) : ¬ ProperlyAccommodable μ₀ H d :=
  fun hacc ↦ h.wasRelevant hacc.2.2

/-- Partial Definition 15: `A` has prima facie causal responsibility for `B` only if `A` makes
`B` more probable. -/
def PrimaFacieCause (μ : Measure W) (a b : Set W) : Prop :=
  μ b < μ[|a] b

-- Corollary 16
theorem IsPresupposed.not_primaFacieCause (h : IsPresupposed μ a) (b : Set W) :
    ¬ PrimaFacieCause μ a b := by
  rw [PrimaFacieCause, h]
  exact lt_irrefl _

-- Prediction 4
theorem AlsoFelicitous.not_primaFacieCause {ba bb : Set W} (h : AlsoFelicitous μ₀ μ H ba bb) :
    ¬ PrimaFacieCause μ ba bb :=
  h.1.presupposed.not_primaFacieCause bb

end Also

end Merin1999a
