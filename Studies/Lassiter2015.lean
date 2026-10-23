module

public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Logic.ComparativeProbability.Content
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Degree.Comparison
public import Studies.HollidayIcard2013
public import Studies.Yalcin2010
public import Linglib.Data.Examples.Lassiter2015
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Lassiter (2015): Epistemic comparison, models of uncertainty, and the disjunction puzzle

Lassiter traces the disjunction puzzle, that *φ is as likely as ψ* and *φ is as likely as χ*
entail *φ is as likely as ψ or χ* under Kratzer's comparative possibility, to Lewis's lift, by
which the likelihood of a disjunction is that of its likeliest disjunct. Kratzer's revised lift
keeps the puzzle for disjoint alternatives, and Holliday and Icard's m-lifting avoids it but,
under Kratzer's *must*, refutes Yalcin's V6. A probability scale refutes the puzzle; symmetric
fuzzy measures refute it too but also refute V13, which qualitative additivity restores. Three
bridges from Kratzer's *must* to a probabilistic *likely* each fail, and the paper ends with
three probabilistic replacements for the auxiliaries.

## Main results

* `disjunction_puzzle`, `lottery_collapse`: §1.1, the puzzle and its lottery iteration.
* `revised_escapes_collapse`, `revised_disjoint_puzzle`, `revised_countermodel_overlap`: §1.4.
* `mLift_refutes_V6`: §1.5, the m-lifting against (35), which the l-lifting validates under the
  same *must* (`Yalcin2010.kratzer_V6`).
* `prob_refutes_rightUnion`, `prob_rightUnion_of_half`, `lottery_bound`: §2.1.
* `fuzzy_refutes_V13`, `QualAddMeasure.eq_zero_of_union_le`: §2.2, (48) and (49).
* `bridge1_disjoint_puzzle`, `bridge1_thin_margin`, `bridge2_refutes_V6`, `bridge3_refutes_V6`:
  §3.
* `moreLikely_might`, `weak_refutes_moreLikely_might`: §4.

## Implementation notes

* Kratzer's *must* is human necessity over the empty base, as in Yalcin's study
  (`Yalcin2010.must`).
* The world-ordering countermodels share three worlds, the first alone best, with masses `0.4`,
  `0.3`, `0.3`; BR3 holds there by Holliday and Icard's footnote-13 lemma.
* Probabilities are mathlib probability measures on a discrete space, compared on their real
  values; the models of §2.1 and §3 are finite sums of Dirac measures.
* The strong and weak auxiliaries are the positive forms of the probability scale,
  the preimages of `Set.Ici` for *must* and of `Set.Ioi` for *might*, with
  thresholds `1` and `θ < 1`.
* The ratio-modifier argument of §2.2 and the open problems of §4 are recorded as examples
  only.

## References

* [lassiter-2015]
* [kratzer-1991]
* [kratzer-2012]
* [lewis-1973]
* [halpern-1997]
* [halpern-2003]
* [holliday-icard-2013]
* [yalcin-2010]
* [hamblin-1959]
* [von-fintel-gillies-2010]
-/

@[expose] public section

namespace Lassiter2015

open ComparativeProbability Modality MeasureTheory ProbabilityTheory

variable {W : Type*}

/-! ### §1.1 The disjunction puzzle and the lottery -/

/-- The puzzle (11) is the right-union property, which Lewis's lift has, as Halpern shows. -/
theorem disjunction_puzzle (r : W → W → Prop) : RightUnion (LewisLift r) :=
  rightUnion_lewisLift

/-- Iterating the puzzle over the other ticket holders, whose winnings exhaust Sam's losing,
makes Sam as likely to win as not, as in (13)–(14). -/
theorem lottery_collapse {r : Set W → Set W → Prop} (hJ : RightUnion r) {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) {win : Set W} {wins : ι → Set W}
    (hcover : (⋃ i ∈ s, wins i) = winᶜ) (h : ∀ i ∈ s, r win (wins i)) : r win winᶜ :=
  hcover ▸ hJ.biUnion hs h

/-! ### §1.4 Kratzer's revised comparative possibility -/

section Revised

variable (r : W → W → Prop)

/-- The revised lift of (30) lets a proposition be as likely as its negation without being as
likely as everything, escaping Yalcin's collapse, since it is as likely as the whole space only
when the space is exhausted. -/
theorem kratzerLift_univ_iff (A : Set W) : KratzerLift r A Set.univ ↔ A = Set.univ :=
  kratzerLift_univ_iff' r A

/-- Over two indiscriminate worlds `{0}` is as likely as its complement but not as
everything. -/
theorem revised_escapes_collapse :
    ¬EquiprobabilityCollapse (KratzerLift fun _ _ : Fin 2 ↦ True) := by
  intro h
  have := h {0} Set.univ fun ⟨_, _, hall⟩ ↦ (hall 0 ⟨rfl, fun h ↦ h rfl⟩).2 trivial
  rw [kratzerLift_univ_iff] at this
  exact absurd (this ▸ Set.mem_univ 1) (by simp)

/-- In a countermodel to the puzzle for the revised lift, (31) of Appendix B, a world of one
alternative outside the first proposition fails to dominate a world the first proposition shares
with the other alternative. -/
theorem revised_countermodel_overlap {A B C : Set W} (hB : KratzerLift r A B)
    (hC : KratzerLift r A C) (hn : ¬KratzerLift r A (B ∪ C)) :
    (∃ u ∈ B \ A, ∃ v ∈ A ∩ C, ¬(r u v ∧ ¬r v u)) ∨
      ∃ u ∈ C \ A, ∃ v ∈ A ∩ B, ¬(r u v ∧ ¬r v u) := by
  simp only [KratzerLift, not_not] at hn
  obtain ⟨u, ⟨huBC, huA⟩, hall⟩ := hn
  rcases huBC with huB | huC
  · left
    refine ⟨u, ⟨huB, huA⟩, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hB ⟨u, ⟨huB, huA⟩, fun v ⟨hvA, hvB⟩ ↦ by
      by_cases hvC : v ∈ C
      · exact hnone v ⟨hvA, hvC⟩
      · exact hall v ⟨hvA, fun h ↦ h.elim hvB hvC⟩⟩
  · right
    refine ⟨u, ⟨huC, huA⟩, ?_⟩
    by_contra hnone
    push Not at hnone
    exact hC ⟨u, ⟨huC, huA⟩, fun v ⟨hvA, hvC⟩ ↦ by
      by_cases hvB : v ∈ B
      · exact hnone v ⟨hvA, hvB⟩
      · exact hall v ⟨hvA, fun h ↦ h.elim hvB hvC⟩⟩

/-- With the alternatives made disjoint, as in the lottery, the puzzle is valid for the revised
lift, (32) of Appendix C. -/
theorem revised_disjoint_puzzle {A B C : Set W} (hB : Disjoint A B) (hC : Disjoint A C)
    (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) : KratzerLift r A (B ∪ C) :=
  kratzerLift_rightUnion_of_disjoint r hB hC hAB hAC

end Revised

/-! ### §1.5 The m-lifting under Kratzer's *must* -/

theorem best_not_probably_of_ncard_lt [Finite W] (r : W → W → Prop) {A : Set W}
    (h : A.ncard < Aᶜ.ncard) : ¬Probably (MatchingLift r) A :=
  fun hp ↦ absurd hp.1.ncard_le (not_le.2 h)

/-- The ordering source of §1.5 and §3 makes the first of three worlds the sole best one. -/
def bestFirst : Set (Fin 3 → Prop) := {(· = 0)}

theorem bestFirst_le (v u : Fin 3) : (v ≤[bestFirst] u) ↔ (u = 0 → v = 0) := by
  simp [bestFirst, Preorder.ofCriteria_le_iff]

theorem must_best : Yalcin2010.must bestFirst {0} 0 :=
  (Yalcin2010.must_iff _ _ _).2 fun _ ↦ ⟨0, (bestFirst_le _ _).2 fun _ ↦ rfl,
    fun _ hz ↦ (bestFirst_le _ _).1 hz rfl⟩

/-- Under Kratzer's *must* the m-lifting refutes (35), Yalcin's V6. The sole best world is
necessary but not likelier than its complement, since one world matches no injection from
two. -/
theorem mLift_refutes_V6 :
    ¬MustToProbably (MatchingLift (premisePreorder bestFirst).le)
      (Yalcin2010.must bestFirst · 0) :=
  fun h ↦ best_not_probably_of_ncard_lt _ (by
    have : ({0} : Set (Fin 3))ᶜ = {1, 2} := by ext x; fin_cases x <;> simp
    rw [this, Set.ncard_singleton, Set.ncard_pair (by decide)]; decide) (h _ must_best)

/-! ### §2.1 Scales of probability -/

/-- Three disjoint alternatives with masses `0.4`, `0.3`, `0.3` refute the puzzle for
probability, as in (46). -/
noncomputable def skewed : Measure (Fin 3) :=
  ∑ i, ENNReal.ofReal (![4 / 10, 3 / 10, 3 / 10] i) • Measure.dirac i

private theorem skewed_nonneg (i : Fin 3) : 0 ≤ (![4 / 10, 3 / 10, 3 / 10] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num

instance : IsProbabilityMeasure skewed :=
  Measure.isProbabilityMeasure_sum_ofReal_smul_dirac skewed_nonneg
    (by simp [Fin.sum_univ_three]; norm_num)

theorem skewed_real (A : Set (Fin 3)) :
    skewed.real A = ∑ i, A.indicator ![4 / 10, 3 / 10, 3 / 10] i :=
  Measure.sum_ofReal_smul_dirac_real_apply skewed_nonneg A

theorem prob_refutes_rightUnion : ¬RightUnion skewed.inducedGe := by
  intro h
  have := h {0} {1} {2}
    (by simp [Measure.inducedGe_iff_real, skewed_real, Set.indicator_apply]; norm_num)
    (by simp [Measure.inducedGe_iff_real, skewed_real, Set.indicator_apply]; norm_num)
  simp [Measure.inducedGe_iff_real, skewed_real, Fin.sum_univ_three, Set.indicator_apply] at this
  norm_num at this

section Probability

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]

/-- The premises are compatible with the conclusion, since when the first proposition holds at
least half the mass, any alternatives outside it together weigh no more. -/
theorem prob_rightUnion_of_half {A B C : Set W} (hA : 1 / 2 ≤ P.real A) (hB : B ⊆ Aᶜ)
    (hC : C ⊆ Aᶜ) : P.real (B ∪ C) ≤ P.real A := by
  have h1 := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  have h2 : P.real (B ∪ C) ≤ P.real Aᶜ := measureReal_mono (Set.union_subset hB hC)
  linarith

end Probability

/-- In the fair lottery a holder of at most `k` of `n` tickets wins with probability at most
`k / n` and loses with probability at least `(n - k) / n`. -/
theorem lottery_bound {n k : ℕ} [NeZero n] {A : Set (Fin n)} (h : A.ncard ≤ k) :
    (uniformOn (Set.univ : Set (Fin n))).real A ≤ k / n ∧
      ((n : ℝ) - k) / n ≤ (uniformOn (Set.univ : Set (Fin n))).real Aᶜ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hA : (uniformOn (Set.univ : Set (Fin n))).real A ≤ k / n := by
    rw [uniformOn_univ_real_apply, Fintype.card_fin]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) hn.le
  refine ⟨hA, ?_⟩
  rw [probReal_compl_eq_one_sub .of_discrete, sub_div, div_self hn.ne']
  linarith

/-! ### §2.2 Symmetric fuzzy measures and equal shares -/

/-- A symmetric fuzzy measure (47) is normalized, symmetric under complement, and monotone. -/
structure SymmetricFuzzyMeasure (W : Type*) where
  /-- `mu A` is the measure of `A`. -/
  mu : Set W → ℝ
  mu_univ : mu Set.univ = 1
  symm : ∀ A, mu A + mu Aᶜ = 1
  mono : ∀ ⦃A B⦄, A ⊆ B → mu A ≤ mu B

/-- Under a symmetric fuzzy measure `A` is at least as likely as `B` when it measures at least
as much. -/
def SymmetricFuzzyMeasure.likelihood (μ : SymmetricFuzzyMeasure W) (A B : Set W) : Prop :=
  μ.mu B ≤ μ.mu A

/-- Every probability measure is a symmetric fuzzy measure, through its real values. -/
noncomputable def SymmetricFuzzyMeasure.ofMeasure [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (P : Measure W) [IsProbabilityMeasure P] : SymmetricFuzzyMeasure W :=
  ⟨P.real, probReal_univ, fun A ↦ probReal_add_probReal_compl .of_discrete,
    fun _ _ h ↦ measureReal_mono h⟩

open scoped Classical in
/-- In the scenario of (48) Sam may go to school (`1`), more likely to the movies (`0`), or
elsewhere (`2`), and the movies alone measure `0.6`, as much as the movies or school. -/
noncomputable def cutClass : SymmetricFuzzyMeasure (Fin 3) where
  mu A := if 0 ∈ A then (if 1 ∈ A then (if 2 ∈ A then 1 else 6 / 10) else
      (if 2 ∈ A then 8 / 10 else 6 / 10))
    else (if 1 ∈ A then (if 2 ∈ A then 4 / 10 else 2 / 10) else (if 2 ∈ A then 4 / 10 else 0))
  mu_univ := by simp
  symm A := by
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A <;> by_cases h2 : 2 ∈ A <;>
      simp [h0, h1, h2] <;> norm_num
  mono A B h := by
    by_cases a0 : 0 ∈ A <;> by_cases a1 : 1 ∈ A <;> by_cases a2 : 2 ∈ A <;>
      by_cases b0 : 0 ∈ B <;> by_cases b1 : 1 ∈ B <;> by_cases b2 : 2 ∈ B <;>
      simp only [a0, a1, a2, b0, b1, b2, ite_true, ite_false] <;>
      first
        | exact absurd (h a0) b0
        | exact absurd (h a1) b1
        | exact absurd (h a2) b2
        | norm_num

/-- Symmetric fuzzy measures refute V13. Under `cutClass` going to the movies is exactly as
likely as going to school or to the movies, although going to school is possible (48). -/
theorem fuzzy_refutes_V13 : ¬StrictDisjunctionIntro cutClass.likelihood := fun h ↦
  (h {1} {0} ⟨by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass],
    by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass]⟩).2
    (by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass])

/-- Qualitative additivity, (49) added to (47), gives V13, so a proposition as likely as a
disjunction it is part of leaves the other disjunct no mass, and (48) forces school out. -/
theorem QualAddMeasure.eq_zero_of_union_le (m : QualAddMeasure ℝ W) {A B : Set W}
    (h : m (A ∪ B) ≤ m A) : m (B \ A) = 0 :=
  have : m.inducedGe ⊥ (B \ A) := strictDisjunctionIntro_iff.1 strictDisjunctionIntro B A
    (show m (B ∪ A) ≤ m A by rwa [Set.union_comm])
  le_antisymm (le_of_le_of_eq this m.mu_empty) (m.nonneg _)

/-! ### §3 Bridging rules -/

section Bridges

variable (r : W → W → Prop) [MeasurableSpace W] (P : Measure W)

/-- BR1 (57) requires the revised lift to constrain probability. -/
def Bridge1 : Prop := ∀ A B, KratzerLift r A B → P B ≤ P A

/-- BR2 (59) requires the world order to constrain probability on singletons. -/
def Bridge2 : Prop := ∀ u v, r u v → P {v} ≤ P {u}

/-- BR3 (61) requires the m-lifting to constrain probability. -/
def Bridge3 : Prop := ∀ A B, MatchingLift r A B → P B ≤ P A

/-- BR1 reimports the puzzle for disjoint alternatives ordered by the revised lift (58). -/
theorem bridge1_disjoint_puzzle (h : Bridge1 r P) {A B C : Set W} (hB : Disjoint A B)
    (hC : Disjoint A C) (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) :
    P (B ∪ C) ≤ P A :=
  h _ _ (kratzerLift_rightUnion_of_disjoint r hB hC hAB hAC)

/-- BR2 makes the m-lifting sound for the measure, by Holliday and Icard's footnote 13, so BR3
follows from BR2 when the order agrees with the measure. -/
theorem bridge3_of_agree [Fintype W] [MeasurableSingletonClass W]
    (h : ∀ v u, r v u ↔ P {u} ≤ P {v}) : Bridge3 r P :=
  fun _ _ hAB ↦ HollidayIcard2013.measure_le_of_matchingLift P r h hAB

end Bridges

/-- In the three-world model of §3, with masses `0.4`, `0.3`, `0.3`, BR2 holds, yet under
Kratzer's *must* V6 fails, since the necessary best world is less likely than its
complement. -/
theorem bridge2_refutes_V6 :
    Bridge2 (premisePreorder bestFirst).le skewed ∧
      ¬MustToProbably skewed.inducedGe (Yalcin2010.must bestFirst · 0) := by
  refine ⟨fun u v huv ↦ (Measure.inducedGe_iff_real skewed).2 ?_, fun hV6 ↦ ?_⟩
  · rw [bestFirst_le] at huv
    rw [skewed_real, skewed_real]
    fin_cases u <;> fin_cases v <;> simp at huv ⊢ <;> norm_num
  · have h := (hV6 _ must_best).1
    simp [Measure.inducedGe_iff_real, skewed_real, Fin.sum_univ_three, Set.indicator_apply] at h
    norm_num at h

/-- The same model satisfies BR3, since the order agrees with the measure on singletons, so
BR3 too allows a necessary proposition to be less likely than its negation. -/
theorem bridge3_refutes_V6 :
    Bridge3 (premisePreorder bestFirst).le skewed ∧
      ¬MustToProbably skewed.inducedGe (Yalcin2010.must bestFirst · 0) :=
  ⟨bridge3_of_agree _ _ fun v u ↦ by
      rw [bestFirst_le, ← Measure.inducedGe, Measure.inducedGe_iff_real, skewed_real,
        skewed_real]
      fin_cases u <;> fin_cases v <;> simp <;> norm_num,
    bridge2_refutes_V6.2⟩

/-- `thin` is the two-world model of §3, with masses `0.5001` and `0.4999`. -/
noncomputable def thin : Measure (Fin 2) :=
  ∑ i, ENNReal.ofReal (![5001 / 10000, 4999 / 10000] i) • Measure.dirac i

private theorem thin_nonneg (i : Fin 2) :
    0 ≤ (![5001 / 10000, 4999 / 10000] : Fin 2 → ℝ) i := by
  fin_cases i <;> norm_num

instance : IsProbabilityMeasure thin :=
  Measure.isProbabilityMeasure_sum_ofReal_smul_dirac thin_nonneg
    (by simp [Fin.sum_univ_two]; norm_num)

theorem thin_real (A : Set (Fin 2)) :
    thin.real A = ∑ i, A.indicator ![5001 / 10000, 4999 / 10000] i :=
  Measure.sum_ofReal_smul_dirac_real_apply thin_nonneg A

/-- `bestFirst₂` makes the first of two worlds the best. -/
def bestFirst₂ : Set (Fin 2 → Prop) := {(· = 0)}

/-- In `thin` BR1 holds and the sole best world is necessary, yet it is only barely likelier
than its negation, so BR1 cannot deliver *much more likely*. -/
theorem bridge1_thin_margin :
    Bridge1 (premisePreorder bestFirst₂).le thin ∧ Yalcin2010.must bestFirst₂ {0} 0 ∧
      thin.real {0} < 5002 / 10000 := by
  have hle : ∀ v u : Fin 2, (v ≤[bestFirst₂] u) ↔ (u = 0 → v = 0) := fun v u ↦ by
    simp [bestFirst₂, Preorder.ofCriteria_le_iff]
  have hsets : ∀ A : Set (Fin 2), A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := fun A ↦ by
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A
    · right; right; right; ext x; fin_cases x <;> simp [h0, h1]
    · right; left; ext x; fin_cases x <;> simp [h0, h1]
    · right; right; left; ext x; fin_cases x <;> simp [h0, h1]
    · left; ext x; fin_cases x <;> simp [h0, h1]
  refine ⟨fun A B hAB ↦ (Measure.inducedGe_iff_real thin).2 ?_, ?_, ?_⟩
  · rw [thin_real, thin_real]
    rcases hsets A with rfl | rfl | rfl | rfl <;> rcases hsets B with rfl | rfl | rfl | rfl <;>
      simp [KratzerLift, hle, Fin.sum_univ_two] at hAB ⊢ <;> norm_num at hAB ⊢
  · exact (Yalcin2010.must_iff _ _ _).2 fun _ ↦
      ⟨0, (hle _ _).2 fun _ ↦ rfl, fun _ hz ↦ (hle _ _).1 hz rfl⟩
  · simp [thin_real]
    norm_num

/-! ### §4 Probability and the epistemic auxiliaries -/

section Auxiliaries

variable [MeasurableSpace W] (P : Measure W)

/-- *Must* as a quantifier over the epistemic space, Kratzer's auxiliary with an empty ordering
source, holds of the whole space. -/
def quantMust (A : Set W) : Prop := A = Set.univ

/-- The probabilistic *must* with threshold `θ` holds when `Pr(A) ≥ θ`; it is strong at
`θ = 1` and weak below. -/
def probMust (θ : ℝ) (A : Set W) : Prop := A ∈ P.real ⁻¹' Set.Ici θ

/-- The dual *might* holds when `Pr(A) > 1 - θ`. -/
def probMight (θ : ℝ) (A : Set W) : Prop := A ∈ P.real ⁻¹' Set.Ioi (1 - θ)

variable [IsProbabilityMeasure P]

/-- Under the quantificational auxiliaries a necessary proposition has all the mass, the
largest possible margin over its negation, as (56) requires. -/
theorem quantMust_prob {A : Set W} (h : quantMust A) : P A = 1 ∧ P Aᶜ = 0 := by
  subst h; simp

theorem probMust_one_iff (A : Set W) : probMust P 1 A ↔ P.real A = 1 :=
  ⟨fun h ↦ le_antisymm measureReal_le_one h, fun h ↦ h.ge⟩

theorem probMight_iff_not_probMust_compl [DiscreteMeasurableSpace W] (θ : ℝ) (A : Set W) :
    probMight P θ A ↔ ¬ probMust P θ Aᶜ := by
  change 1 - θ < P.real A ↔ ¬ θ ≤ P.real Aᶜ
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  rw [not_le]
  constructor <;> intro h <;> linarith

/-- Under the strong probabilistic auxiliaries, what is more likely than something might be,
since it has positive mass (64). -/
theorem moreLikely_might {A B : Set W} (h : Strict P.inducedGe A B) : probMight P 1 A := by
  have hlt := h.2
  rw [Measure.inducedGe_iff_real, not_le] at hlt
  have := measureReal_nonneg (μ := P) (s := B)
  show 1 - 1 < P.real A
  linarith

/-- Under a weak *might* two astronomically unlikely teams can be ordered without either being
a live possibility (65). -/
theorem weak_refutes_moreLikely_might :
    ∃ P : Measure (Fin 100), IsProbabilityMeasure P ∧ ∃ A B : Set (Fin 100),
      Strict P.inducedGe A B ∧ ¬probMight P (9 / 10) A := by
  have hpair : ({0, 1} : Set (Fin 100)).ncard = 2 := Set.ncard_pair (by decide)
  refine ⟨uniformOn Set.univ, inferInstance, {0, 1}, {0}, ⟨?_, ?_⟩, ?_⟩
  · exact measure_mono (Set.singleton_subset_iff.2 (by simp))
  · rw [Measure.inducedGe, uniformOn_univ_le_iff, hpair, Set.ncard_singleton]
    omega
  · simp only [probMight, Set.mem_preimage, Set.mem_Ioi,
      uniformOn_univ_real_apply, hpair, Fintype.card_fin, not_lt]
    norm_num

end Auxiliaries

end Lassiter2015
