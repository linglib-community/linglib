module

public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Logic.ComparativeProbability.Content
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.Probability.UniformOn
public import Linglib.Semantics.Modality.Necessity
public import Studies.HollidayIcard2013
public import Studies.Kratzer2012
public import Studies.Yalcin2010
public import Linglib.Data.Examples.Lassiter2015
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FinCases

/-!
# Lassiter (2015): Epistemic comparison, models of uncertainty, and the disjunction puzzle

This file formalizes a fair lottery in which Sam holds as many tickets as anyone else, the
likelihood orders that compare its outcomes, and the semantics for the epistemic auxiliaries that
go with them. Every order that validates the modified disjunction puzzle, as Lewis's and Kratzer's
lifts of a world order do, infers from *Sam is as likely to win as anyone else* that Sam is as
likely to win as not; the lottery's probability measure makes the first true and the second false.

## Main statements

* `lottery_collapse`: an order validating the modified disjunction puzzle infers (14) from (4).
* `lottery_rows`: the fair lottery decides the paper's lottery sentences as judged.
* `not_exists_lift`: no lift of a world order fixes the order of every measure agreeing with it.
* `not_mustToProbably_of_ncard_lt`: under Kratzer's *must* the m-lifting refutes (35) whenever
  fewer than half the worlds are best.
* `probMust_one_iff_humanNecessity`: at threshold one the probabilistic *must* is the
  quantificational one over the worlds of positive probability.

## Implementation notes

* Kratzer's *must* is human necessity over the empty modal base, as in `Yalcin2010.must`.
* The lottery has a million tickets, the holder `n` holding tickets `2n` and `2n + 1`: Sam is `0`,
  Mary `1`, Sue `2`, and Tom, Alice, Bob, Hank and Murray `3` to `7`.
* The injection of the m-lifting, (34) and (60), has `φ ∩ ⋂f(w)` as codomain, not as image.
* Probabilities are mathlib probability measures on a discrete space, compared on their real
  values.

## Errata

* p. 674: when the world order is not connected, the best worlds need not strictly dominate their
  complement under the revised lift (`not_strict_kratzerLift_bestWorlds`).

## References

* [lassiter-2015]
* [kratzer-1991]
* [kratzer-2012]
* [lewis-1973]
* [halpern-1997]
* [holliday-icard-2013]
* [yalcin-2010]
-/

@[expose] public section

namespace Lassiter2015

open ComparativeProbability Modality MeasureTheory ProbabilityTheory

variable {W : Type*}

/-! ### §1.1 The lottery -/

/-- The million tickets of the lottery. -/
abbrev Ticket := Fin 1000000

/-- `wins s` is the proposition that a holder in `s` wins, holder `n` holding tickets `2n` and
`2n + 1`. -/
def wins (s : Set ℕ) : Set Ticket := {t | t.val / 2 ∈ s}

/-- The fair lottery draws every ticket with the same probability. -/
noncomputable abbrev lottery : Measure Ticket := uniformOn Set.univ

theorem lottery_inducedGe_iff {A B : Set Ticket} : lottery.inducedGe A B ↔ B.ncard ≤ A.ncard :=
  uniformOn_univ_le_iff

theorem ncard_wins_zero : (wins {0}).ncard = 2 := by
  have : wins {0} = ↑({⟨0, by norm_num⟩, ⟨1, by norm_num⟩} : Finset Ticket) := by
    ext t
    simp only [wins, Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff, Fin.ext_iff]
    omega
  rw [this, Set.ncard_coe_finset]
  rfl

theorem ncard_wins_le (n : ℕ) : (wins {n}).ncard ≤ 2 := by
  have h : Set.MapsTo Fin.val (wins {n}) {2 * n, 2 * n + 1} := fun t ht ↦ by
    simp only [wins, Set.mem_ofPred_eq, Set.mem_singleton_iff] at ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  exact (Set.ncard_le_ncard_of_injOn _ h Fin.val_injective.injOn).trans
    ((Set.ncard_insert_le _ _).trans (by simp))

theorem ncard_wins_one_two : (wins {1, 2}).ncard = 4 := by
  have : wins {1, 2} = ↑({2, 3, 4, 5} : Finset Ticket) := by
    ext t
    simp only [wins, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Finset.coe_insert, Finset.coe_singleton, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
    omega
  rw [this, Set.ncard_coe_finset]
  rfl

theorem lottery_four : ∀ n ≠ 0, lottery.inducedGe (wins {0}) (wins {n}) := fun n _ ↦
  lottery_inducedGe_iff.2 (ncard_wins_zero ▸ ncard_wins_le n)

theorem lottery_not_nine : ¬lottery.inducedGe (wins {0}) (wins {1, 2}) := by
  rw [lottery_inducedGe_iff, ncard_wins_zero, ncard_wins_one_two]
  omega

theorem lottery_not_fourteen : ¬lottery.inducedGe (wins {0}) (wins {0})ᶜ := by
  rw [lottery_inducedGe_iff, Set.ncard_compl, ncard_wins_zero]
  simp

/-- The fair lottery makes (4) and the conjunctive reading of (5) true, and (2b), (8), (9), (12)
and (33c) false. -/
theorem lottery_rows :
    (lottery.inducedGe (wins {0}) (wins {0})ᶜ ↔
      Examples.ex2b.feature? "truthValue" = some "true") ∧
    ((∀ n ≠ 0, lottery.inducedGe (wins {0}) (wins {n})) ↔
      Examples.ex4.feature? "truthValue" = some "true") ∧
    (lottery.inducedGe (wins {0}) (wins {1}) ∧ lottery.inducedGe (wins {0}) (wins {2}) ↔
      Examples.ex5.feature? "truthValue" = some "true") ∧
    (lottery.inducedGe (wins {0}) (wins {1, 2}) ↔
      Examples.ex8.feature? "truthValue" = some "true") ∧
    (lottery.inducedGe (wins {0}) (wins {1, 2}) ↔
      Examples.ex9.feature? "truthValue" = some "true") ∧
    (lottery.inducedGe (wins {0}) (wins (Set.Icc 1 7)) ↔
      Examples.ex12.feature? "truthValue" = some "true") ∧
    (lottery.inducedGe (wins {0}) (wins {1, 2}) ↔
      Examples.ex33c.feature? "truthValue" = some "true") := by
  have h12 : ¬lottery.inducedGe (wins {0}) (wins (Set.Icc 1 7)) := fun h ↦
    lottery_not_nine ((lottery_inducedGe_iff.2 (Set.ncard_le_ncard fun t ht ↦ by
      simp only [wins, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_Icc] at ht ⊢
      omega)).trans h)
  exact ⟨iff_of_false lottery_not_fourteen (by decide), iff_of_true lottery_four (by decide),
    iff_of_true ⟨lottery_four 1 one_ne_zero, lottery_four 2 two_ne_zero⟩ (by decide),
    iff_of_false lottery_not_nine (by decide), iff_of_false lottery_not_nine (by decide),
    iff_of_false h12 (by decide), iff_of_false lottery_not_nine (by decide)⟩

theorem lottery_wins_le (n : ℕ) :
    lottery.real (wins {n}) ≤ 2 / 1000000 ∧ 999998 / 1000000 ≤ lottery.real (wins {n})ᶜ := by
  have h : lottery.real (wins {n}) ≤ 2 / 1000000 := by
    rw [uniformOn_univ_real_apply, Fintype.card_fin]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ncard_wins_le n) (by norm_num)
  refine ⟨h, ?_⟩
  rw [probReal_compl_eq_one_sub .of_discrete]
  linarith

/-! ### §1.3 The disjunction puzzle in Kratzer 1991 -/

theorem disjunction_puzzle (r : W → W → Prop) : RightUnion (LewisLift r) :=
  rightUnion_lewisLift

/-! ### §1.4 Kratzer's revised comparative possibility -/

/-- The modified disjunction puzzle (32) holds of `r` when a proposition at least as likely as
each of two alternatives is at least as likely as their disjunction, all three being mutually
exclusive. -/
def ModifiedDisjunctionPuzzle (r : Set W → Set W → Prop) : Prop :=
  ∀ A B C, Disjoint A B → Disjoint A C → Disjoint B C → r A B → r A C → r A (B ∪ C)

theorem modifiedDisjunctionPuzzle_of_rightUnion {r : Set W → Set W → Prop} (h : RightUnion r) :
    ModifiedDisjunctionPuzzle r :=
  fun A B C _ _ _ ↦ h A B C

theorem ModifiedDisjunctionPuzzle.biUnion {r : Set W → Set W → Prop}
    (hr : ModifiedDisjunctionPuzzle r) {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {A : Set W}
    {B : ι → Set W} (hB : (s : Set ι).PairwiseDisjoint B) (hA : ∀ i ∈ s, Disjoint A (B i))
    (h : ∀ i ∈ s, r A (B i)) : r A (⋃ i ∈ s, B i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using h i (Finset.mem_singleton_self i)
  | cons i s hi hs ih =>
    rw [Finset.cons_eq_insert, Finset.set_biUnion_insert]
    rw [Finset.cons_eq_insert, Finset.coe_insert] at hB
    exact hr _ _ _ (hA i (Finset.mem_cons_self i s))
      (Set.disjoint_iUnion₂_right.2 fun j hj ↦ hA j (Finset.mem_cons_of_mem hj))
      (Set.disjoint_iUnion₂_right.2 fun j hj ↦ hB (Set.mem_insert i _)
        (Set.mem_insert_of_mem _ hj) fun hij ↦ hi (hij ▸ hj))
      (h i (Finset.mem_cons_self i s))
      (ih (hB.subset (Set.subset_insert _ _)) (fun j hj ↦ hA j (Finset.mem_cons_of_mem hj))
        fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

/-- An order validating the modified disjunction puzzle infers (14) from (4), feeding each
conclusion back as a premise as in (13). -/
theorem lottery_collapse {r : Set Ticket → Set Ticket → Prop} (hr : ModifiedDisjunctionPuzzle r)
    (h : ∀ n ≠ 0, r (wins {0}) (wins {n})) : r (wins {0}) (wins {0})ᶜ := by
  have hd : (Set.univ : Set ℕ).PairwiseDisjoint fun n ↦ wins {n} :=
    fun m _ n _ hmn ↦ Set.disjoint_left.2 fun _ hm hn ↦ hmn (hm.symm.trans hn)
  have hc : ⋃ n ∈ Finset.Ioo 0 500000, wins {n} = (wins {0})ᶜ := by
    ext t
    have := t.isLt
    simp only [wins, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.mem_Ioo,
      Set.mem_compl_iff, exists_prop]
    exact ⟨fun ⟨_, ⟨_, _⟩, _⟩ ↦ by omega, fun _ ↦ ⟨_, ⟨by omega, by omega⟩, rfl⟩⟩
  rw [← hc]
  exact hr.biUnion ⟨1, by simp⟩ (hd.subset (Set.subset_univ _))
    (fun n hn ↦ hd (Set.mem_univ 0) (Set.mem_univ n) (Finset.mem_Ioo.1 hn).1.ne)
    fun n hn ↦ h n (Finset.mem_Ioo.1 hn).1.ne'

section Revised

variable (r : W → W → Prop)

theorem revised_escapes_collapse :
    ¬EquiprobabilityCollapse (KratzerLift fun _ _ : Fin 2 ↦ True) := by
  intro h
  have := h {0} Set.univ fun ⟨_, _, hall⟩ ↦ (hall 0 ⟨rfl, fun h ↦ h rfl⟩).2 trivial
  rw [kratzerLift_univ_iff] at this
  exact absurd (this ▸ Set.mem_univ 1) (by simp)

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

theorem kratzerLift_modifiedDisjunctionPuzzle : ModifiedDisjunctionPuzzle (KratzerLift r) :=
  fun _ _ _ hB hC _ ↦ kratzerLift_rightUnion_of_disjoint r hB hC

theorem lifts_lottery_collapse (r : Ticket → Ticket → Prop) :
    ((∀ n ≠ 0, LewisLift r (wins {0}) (wins {n})) → LewisLift r (wins {0}) (wins {0})ᶜ) ∧
      ((∀ n ≠ 0, KratzerLift r (wins {0}) (wins {n})) → KratzerLift r (wins {0}) (wins {0})ᶜ) :=
  ⟨lottery_collapse (modifiedDisjunctionPuzzle_of_rightUnion rightUnion_lewisLift),
    lottery_collapse (kratzerLift_modifiedDisjunctionPuzzle r)⟩

end Revised

/-! ### §1.5 Lifting an order on worlds -/

/-- The ordering source `{{w₀}}`, under which `w₀` alone is best. -/
def onlyBest (w₀ : W) : Set (W → Prop) := {(· = w₀)}

theorem onlyBest_le (w₀ v u : W) : (v ≤[onlyBest w₀] u) ↔ (u = w₀ → v = w₀) := by
  simp [onlyBest, Preorder.ofCriteria_le_iff]

theorem bestWorlds_onlyBest (w₀ w : W) : bestWorlds ⊥ (fun _ ↦ onlyBest w₀) w = {w₀} := by
  ext x
  simp only [mem_bestWorlds, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
    forall_const, onlyBest_le, Set.mem_singleton_iff]
  exact ⟨fun h ↦ h w₀ (fun _ ↦ rfl) rfl, fun hx _ _ _ ↦ hx⟩

theorem must_bestWorlds [Finite W] (O : Set (W → Prop)) (w : W) :
    Yalcin2010.must O (bestWorlds ⊥ (fun _ ↦ O) w) w :=
  humanNecessity_of_necessity (.of_finite _ _ _) fun _ hv ↦ hv

theorem must_onlyBest [Finite W] (w₀ w : W) : Yalcin2010.must (onlyBest w₀) {w₀} w :=
  bestWorlds_onlyBest w₀ w ▸ must_bestWorlds _ w

/-- Masses `0.4`, `0.3`, `0.3` on three worlds, the countermodel of (46). -/
noncomputable def skewed : Measure (Fin 3) := Measure.ofRealWeights ![4 / 10, 3 / 10, 3 / 10]

private theorem skewed_nonneg (i : Fin 3) : 0 ≤ (![4 / 10, 3 / 10, 3 / 10] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num

instance : IsProbabilityMeasure skewed :=
  Measure.isProbabilityMeasure_ofRealWeights skewed_nonneg (by simp [Fin.sum_univ_three]; norm_num)

theorem skewed_real (A : Set (Fin 3)) :
    skewed.real A = ∑ i, A.indicator ![4 / 10, 3 / 10, 3 / 10] i :=
  Measure.sum_ofReal_smul_dirac_real_apply skewed_nonneg A

/-- Masses `0.6`, `0.2`, `0.2` on three worlds, the first outweighing the other two together. -/
noncomputable def peaked : Measure (Fin 3) := Measure.ofRealWeights ![6 / 10, 2 / 10, 2 / 10]

private theorem peaked_nonneg (i : Fin 3) : 0 ≤ (![6 / 10, 2 / 10, 2 / 10] : Fin 3 → ℝ) i := by
  fin_cases i <;> norm_num

instance : IsProbabilityMeasure peaked :=
  Measure.isProbabilityMeasure_ofRealWeights peaked_nonneg (by simp [Fin.sum_univ_three]; norm_num)

theorem peaked_real (A : Set (Fin 3)) :
    peaked.real A = ∑ i, A.indicator ![6 / 10, 2 / 10, 2 / 10] i :=
  Measure.sum_ofReal_smul_dirac_real_apply peaked_nonneg A

theorem skewed_agrees (u v : Fin 3) : (u ≤[onlyBest 0] v) ↔ skewed {v} ≤ skewed {u} := by
  rw [onlyBest_le, ← Measure.inducedGe, Measure.inducedGe_iff_real, skewed_real, skewed_real]
  fin_cases u <;> fin_cases v <;> simp <;> norm_num

theorem peaked_agrees (u v : Fin 3) : (u ≤[onlyBest 0] v) ↔ peaked {v} ≤ peaked {u} := by
  rw [onlyBest_le, ← Measure.inducedGe, Measure.inducedGe_iff_real, peaked_real, peaked_real]
  fin_cases u <;> fin_cases v <;> simp <;> norm_num

/-- No lift of the order on three worlds with the first alone best fixes the order on propositions
of every probability measure agreeing with it on singletons (p. 662). -/
theorem not_exists_lift :
    ¬∃ ge : Set (Fin 3) → Set (Fin 3) → Prop, ∀ P : Measure (Fin 3), IsProbabilityMeasure P →
      (∀ u v, (u ≤[onlyBest 0] v) ↔ P {v} ≤ P {u}) → P.inducedGe = ge := by
  rintro ⟨ge, h⟩
  have := congrFun₂ ((h skewed inferInstance skewed_agrees).trans
    (h peaked inferInstance peaked_agrees).symm) {0} {1, 2}
  simp only [Measure.inducedGe_iff_real, skewed_real, peaked_real, Fin.sum_univ_three,
    Set.indicator_apply] at this
  norm_num at this

/-- Under Kratzer's *must* the m-lifting refutes (35) in every finite model in which fewer than
half the worlds are best (p. 664). -/
theorem not_mustToProbably_of_ncard_lt [Finite W] (O : Set (W → Prop)) (w : W)
    (h : (bestWorlds ⊥ (fun _ ↦ O) w).ncard < (bestWorlds ⊥ (fun _ ↦ O) w)ᶜ.ncard) :
    ¬MustToProbably (MatchingLift (premisePreorder O).le) (Yalcin2010.must O · w) :=
  fun hV6 ↦ absurd (hV6 _ (must_bestWorlds O w)).1.ncard_le (not_le.2 h)

theorem mLift_refutes_V6 :
    ¬MustToProbably (MatchingLift (premisePreorder (onlyBest 0)).le)
      (Yalcin2010.must (onlyBest (0 : Fin 3)) · 0) :=
  not_mustToProbably_of_ncard_lt _ _ (by
    rw [bestWorlds_onlyBest, Set.ncard_singleton,
      show ({0} : Set (Fin 3))ᶜ = {1, 2} by ext x; fin_cases x <;> simp,
      Set.ncard_pair (by decide)]
    decide)

/-! ### §2.1 Scales of probability -/

theorem lottery_not_modifiedDisjunctionPuzzle : ¬ModifiedDisjunctionPuzzle lottery.inducedGe :=
  fun h ↦ lottery_not_fourteen (lottery_collapse h lottery_four)

theorem prob_refutes_rightUnion : ¬RightUnion skewed.inducedGe := by
  intro h
  have := h {0} {1} {2}
    (by simp [Measure.inducedGe_iff_real, skewed_real, Set.indicator_apply]; norm_num)
    (by simp [Measure.inducedGe_iff_real, skewed_real, Set.indicator_apply]; norm_num)
  simp [Measure.inducedGe_iff_real, skewed_real, Fin.sum_univ_three, Set.indicator_apply] at this
  norm_num at this

theorem prob_rightUnion_of_half [MeasurableSpace W] [DiscreteMeasurableSpace W] (P : Measure W)
    [IsProbabilityMeasure P] {A B C : Set W} (hA : 1 / 2 ≤ P.real A) (hB : B ⊆ Aᶜ)
    (hC : C ⊆ Aᶜ) : P.real (B ∪ C) ≤ P.real A := by
  have h1 := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  have h2 : P.real (B ∪ C) ≤ P.real Aᶜ := measureReal_mono (Set.union_subset hB hC)
  linarith

/-! ### §2.2 Symmetric fuzzy measures and equal shares -/

/-- A symmetric fuzzy measure (47) is normalized, symmetric under complement, and monotone. -/
structure SymmetricFuzzyMeasure (W : Type*) where
  /-- `mu A` is the measure of `A`. -/
  mu : Set W → ℝ
  mu_univ : mu Set.univ = 1
  symm : ∀ A, mu A + mu Aᶜ = 1
  mono : ∀ ⦃A B⦄, A ⊆ B → mu A ≤ mu B

namespace SymmetricFuzzyMeasure

variable (μ : SymmetricFuzzyMeasure W)

/-- `μ.likelihood A B` holds when `A` measures at least as much as `B`. -/
def likelihood (A B : Set W) : Prop := μ.mu B ≤ μ.mu A

/-- A probability measure is a symmetric fuzzy measure through its real values. -/
noncomputable def ofMeasure [MeasurableSpace W] [DiscreteMeasurableSpace W] (P : Measure W)
    [IsProbabilityMeasure P] : SymmetricFuzzyMeasure W :=
  ⟨P.real, probReal_univ, fun _ ↦ probReal_add_probReal_compl .of_discrete,
    fun _ _ h ↦ measureReal_mono h⟩

/-- Equal shares (49): two propositions compare as their differences do. -/
def EqualShares : Prop := ∀ A B, μ.mu B ≤ μ.mu A ↔ μ.mu (B \ A) ≤ μ.mu (A \ B)

theorem mu_empty : μ.mu ∅ = 0 := by
  have := μ.symm Set.univ
  rw [Set.compl_univ, μ.mu_univ] at this
  linarith

theorem nonneg (A : Set W) : 0 ≤ μ.mu A := μ.mu_empty ▸ μ.mono (Set.empty_subset A)

/-- A symmetric fuzzy measure with equal shares is a qualitatively additive measure. -/
def toQualAdd (h : μ.EqualShares) : QualAddMeasure ℝ W where
  toFun := μ.mu
  nonneg' := μ.nonneg
  empty' := μ.mu_empty
  total' := μ.mu_univ
  qualAdd' A B := h B A

variable {μ}

theorem EqualShares.strictDisjunctionIntro (h : μ.EqualShares) :
    StrictDisjunctionIntro μ.likelihood :=
  show StrictDisjunctionIntro (μ.toQualAdd h).inducedGe from
    ComparativeProbability.strictDisjunctionIntro

theorem EqualShares.union_le_iff (h : μ.EqualShares) {A B : Set W} :
    μ.mu (A ∪ B) ≤ μ.mu A ↔ μ.mu (B \ A) = 0 := by
  rw [h, Set.union_sdiff_left, Set.sdiff_eq_empty.2 Set.subset_union_left, μ.mu_empty]
  exact ⟨fun h' ↦ le_antisymm h' (μ.nonneg _), le_of_eq⟩

end SymmetricFuzzyMeasure

open scoped Classical in
/-- Sam goes to the movies (`0`) with measure `0.6`, to school (`1`) with `0.2`, or elsewhere
(`2`), and the movies alone measure as much as the movies or school (48). -/
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

theorem fuzzy_refutes_V13 : ¬StrictDisjunctionIntro cutClass.likelihood := fun h ↦
  (h {1} {0} ⟨by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass],
    by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass]⟩).2
    (by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass])

theorem rows_48 :
    ¬(cutClass.likelihood {0} ({0} ∪ {1}) ↔ Examples.ex48.feature? "truthValue" = some "true") ∧
      ∀ μ : SymmetricFuzzyMeasure W, μ.EqualShares → ∀ movies school : Set W,
        μ.mu (school \ movies) ≠ 0 →
        (μ.likelihood movies (movies ∪ school) ↔
          Examples.ex48.feature? "truthValue" = some "true") :=
  ⟨fun h ↦ absurd (h.1 (by norm_num [SymmetricFuzzyMeasure.likelihood, cutClass])) (by decide),
    fun _ h _ _ hs ↦ iff_of_false (fun h' ↦ hs (h.union_le_iff.1 h')) (by decide)⟩

/-! ### §3 Bridging rules -/

section Bridges

variable (r : W → W → Prop) [MeasurableSpace W] (P : Measure W)

/-- BR1 (57) requires the revised lift to constrain probability. -/
def Bridge1 : Prop := ∀ A B, KratzerLift r A B → P B ≤ P A

/-- BR2 (59) requires the world order to constrain probability on singletons. -/
def Bridge2 : Prop := ∀ u v, r u v → P {v} ≤ P {u}

/-- BR3 (61) requires the m-lifting to constrain probability. -/
def Bridge3 : Prop := ∀ A B, MatchingLift r A B → P B ≤ P A

theorem bridge1_disjoint_puzzle (h : Bridge1 r P) {A B C : Set W} (hB : Disjoint A B)
    (hC : Disjoint A C) (hAB : KratzerLift r A B) (hAC : KratzerLift r A C) :
    P (B ∪ C) ≤ P A :=
  h _ _ (kratzerLift_rightUnion_of_disjoint r hB hC hAB hAC)

theorem bridge3_of_agree [Fintype W] [MeasurableSingletonClass W]
    (h : ∀ v u, r v u ↔ P {u} ≤ P {v}) : Bridge3 r P :=
  fun _ _ hAB ↦ HollidayIcard2013.measure_le_of_matchingLift P r h hAB

end Bridges

theorem bridge1_kratzer :
    Bridge1 (premisePreorder (Kratzer2012.Grades.ideal 0)).le Kratzer2012.Grades.prob := by
  have hr : (premisePreorder (Kratzer2012.Grades.ideal 0)).le = (· ≥ ·) :=
    funext₂ fun w z ↦ propext (Kratzer2012.Grades.atLeastAsGoodAs_ideal_iff 0 w z)
  intro A B h
  rw [hr] at h
  exact (Kratzer2012.Grades.kratzerLift_iff_measure_le_iff.2
    Kratzer2012.Grades.superincreasing_prob A B).1 h

theorem not_bridge1_skewed : ¬Bridge1 (premisePreorder (onlyBest 0)).le skewed := fun h ↦ by
  have := h {0} {1, 2} (kratzerLift_iff.2 fun _ _ ↦ ⟨0, ⟨rfl, by simp⟩, fun ⟨_, h2⟩ ↦
    h2 ((onlyBest_le _ _ _).2 fun _ ↦ rfl)⟩)
  rw [← Measure.inducedGe, Measure.inducedGe_iff_real, skewed_real, skewed_real] at this
  simp [Fin.sum_univ_three, Set.indicator_apply] at this
  norm_num at this

theorem bridge2_refutes_V6 :
    Bridge2 (premisePreorder (onlyBest 0)).le skewed ∧
      ¬MustToProbably skewed.inducedGe (Yalcin2010.must (onlyBest (0 : Fin 3)) · 0) := by
  refine ⟨fun u v huv ↦ (skewed_agrees u v).1 huv, fun hV6 ↦ ?_⟩
  have h := (hV6 _ (must_onlyBest 0 0)).1
  simp [Measure.inducedGe_iff_real, skewed_real, Fin.sum_univ_three, Set.indicator_apply] at h
  norm_num at h

theorem bridge3_refutes_V6 :
    Bridge3 (premisePreorder (onlyBest 0)).le skewed ∧
      ¬MustToProbably skewed.inducedGe (Yalcin2010.must (onlyBest (0 : Fin 3)) · 0) :=
  ⟨bridge3_of_agree _ _ fun v u ↦ skewed_agrees v u, bridge2_refutes_V6.2⟩

/-- Masses `0.5001` and `0.4999` on two worlds, the model of BR1 on p. 674. -/
noncomputable def thin : Measure (Fin 2) := Measure.ofRealWeights ![5001 / 10000, 4999 / 10000]

private theorem thin_nonneg (i : Fin 2) :
    0 ≤ (![5001 / 10000, 4999 / 10000] : Fin 2 → ℝ) i := by
  fin_cases i <;> norm_num

instance : IsProbabilityMeasure thin :=
  Measure.isProbabilityMeasure_ofRealWeights thin_nonneg (by simp [Fin.sum_univ_two]; norm_num)

theorem thin_real (A : Set (Fin 2)) :
    thin.real A = ∑ i, A.indicator ![5001 / 10000, 4999 / 10000] i :=
  Measure.sum_ofReal_smul_dirac_real_apply thin_nonneg A

theorem bridge1_thin_margin :
    Bridge1 (premisePreorder (onlyBest 0)).le thin ∧
      Yalcin2010.must (onlyBest (0 : Fin 2)) {0} 0 ∧
      thin.real {0} < 5002 / 10000 := by
  have hsets : ∀ A : Set (Fin 2), A = ∅ ∨ A = {0} ∨ A = {1} ∨ A = Set.univ := fun A ↦ by
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A
    · right; right; right; ext x; fin_cases x <;> simp [h0, h1]
    · right; left; ext x; fin_cases x <;> simp [h0, h1]
    · right; right; left; ext x; fin_cases x <;> simp [h0, h1]
    · left; ext x; fin_cases x <;> simp [h0, h1]
  refine ⟨fun A B hAB ↦ (Measure.inducedGe_iff_real thin).2 ?_, must_onlyBest 0 0, ?_⟩
  · rw [thin_real, thin_real]
    rcases hsets A with rfl | rfl | rfl | rfl <;> rcases hsets B with rfl | rfl | rfl | rfl <;>
      simp [KratzerLift, onlyBest_le, Fin.sum_univ_two] at hAB ⊢ <;> norm_num at hAB ⊢
  · simp [thin_real]
    norm_num

/-- An ordering source on four worlds whose two best worlds each dominate only one of the other
two. -/
def crossed : Set (Fin 4 → Prop) :=
  {(· ∈ ({0, 2} : Set (Fin 4))), (· ∈ ({1, 3} : Set (Fin 4))), (· ∈ ({0, 1} : Set (Fin 4)))}

theorem crossed_le (v u : Fin 4) : (v ≤[crossed] u) ↔
    ((u = 0 ∨ u = 2) → (v = 0 ∨ v = 2)) ∧ ((u = 1 ∨ u = 3) → (v = 1 ∨ v = 3)) ∧
      ((u = 0 ∨ u = 1) → (v = 0 ∨ v = 1)) := by
  simp [crossed, Preorder.ofCriteria_le_iff]

theorem bestWorlds_crossed : bestWorlds ⊥ (fun _ ↦ crossed) 0 = {0, 1} := by
  ext x
  simp only [mem_bestWorlds, Background.accessibleWorlds_bot, Set.mem_univ, true_and,
    forall_const, crossed_le, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert x
  decide

theorem not_strict_kratzerLift_bestWorlds :
    ¬Strict (KratzerLift (premisePreorder crossed).le) (bestWorlds ⊥ (fun _ ↦ crossed) 0)
      (bestWorlds ⊥ (fun _ ↦ crossed) 0)ᶜ := by
  rw [bestWorlds_crossed]
  refine fun ⟨_, h⟩ ↦ h ?_
  rw [kratzerLift_iff]
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_compl_iff,
    crossed_le]
  decide

/-! ### §4 Probability and the epistemic auxiliaries -/

section Auxiliaries

variable [MeasurableSpace W] (P : Measure W) {f : Background W} {w : W} {A B : Set W}

/-- The probabilistic *must* with threshold `θ` holds when `Pr(A) ≥ θ`; it is strong at
`θ = 1` and weak below. -/
def probMust (θ : ℝ) (A : Set W) : Prop := A ∈ P.real ⁻¹' Set.Ici θ

/-- The dual *might* holds when `Pr(A) > 1 - θ`. -/
def probMight (θ : ℝ) (A : Set W) : Prop := A ∈ P.real ⁻¹' Set.Ioi (1 - θ)

theorem quant_must (hP : P (f.accessibleWorlds w)ᶜ = 0) (h : humanNecessity f ⊥ (· ∈ A) w) :
    P Aᶜ = 0 :=
  measure_mono_null (Set.compl_subset_compl.2 fun _ hv ↦
    (humanNecessity_bot_iff f _ w).1 h _ hv) hP

theorem quant_might (hP : P (f.accessibleWorlds w)ᶜ = 0) (h : P A ≠ 0) :
    humanPossibility f ⊥ (· ∈ A) w := fun hn ↦
  h (by simpa using quant_must P (A := Aᶜ) hP hn)

theorem quant_moreLikely_might (hP : P (f.accessibleWorlds w)ᶜ = 0)
    (h : Strict P.inducedGe A B) : humanPossibility f ⊥ (· ∈ A) w :=
  quant_might P hP fun h0 ↦ h.2 (by simp [Measure.inducedGe, h0])

variable [IsProbabilityMeasure P]

theorem quant_mustToProbably [DiscreteMeasurableSpace W] (hP : P (f.accessibleWorlds w)ᶜ = 0) :
    MustToProbably P.inducedGe (fun A ↦ humanNecessity f ⊥ (· ∈ A) w) := fun A h ↦ by
  have h0 := quant_must P hP h
  have h1 := (prob_compl_eq_zero_iff (.of_discrete : MeasurableSet A)).1 h0
  refine ⟨?_, ?_⟩ <;> simp [Measure.inducedGe, h0, h1]

theorem rows_35 [DiscreteMeasurableSpace W] (hP : P (f.accessibleWorlds w)ᶜ = 0) :
    (MustToProbably P.inducedGe (fun A ↦ humanNecessity f ⊥ (· ∈ A) w) ↔
        Examples.ex35.judgment = .acceptable) ∧
      ¬(MustToProbably (MatchingLift (premisePreorder (onlyBest 0)).le)
          (Yalcin2010.must (onlyBest (0 : Fin 3)) · 0) ↔
        Examples.ex35.judgment = .acceptable) :=
  ⟨iff_of_true (quant_mustToProbably P hP) rfl, fun h ↦ mLift_refutes_V6 (h.2 rfl)⟩

theorem probMust_one_iff (A : Set W) : probMust P 1 A ↔ P.real A = 1 :=
  ⟨fun h ↦ le_antisymm measureReal_le_one h, fun h ↦ h.ge⟩

/-- At threshold one the probabilistic *must* is the quantificational one when the epistemic space
is the set of worlds of positive probability (p. 676). -/
theorem probMust_one_iff_humanNecessity [DiscreteMeasurableSpace W] [Countable W]
    (hf : f.accessibleWorlds w = {v | P {v} ≠ 0}) :
    probMust P 1 A ↔ humanNecessity f ⊥ (· ∈ A) w := by
  rw [probMust_one_iff, humanNecessity_bot_iff, simpleNecessity_iff, hf, measureReal_def,
    ENNReal.toReal_eq_one_iff, ← prob_compl_eq_zero_iff .of_discrete,
    measure_null_iff_singleton (Set.to_countable _)]
  exact ⟨fun h v hv ↦ by_contra fun hA ↦ hv (h v hA), fun h v hv ↦ by_contra fun h0 ↦ hv (h v h0)⟩

theorem probMight_iff_not_probMust_compl [DiscreteMeasurableSpace W] (θ : ℝ) (A : Set W) :
    probMight P θ A ↔ ¬ probMust P θ Aᶜ := by
  change 1 - θ < P.real A ↔ ¬ θ ≤ P.real Aᶜ
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  rw [not_le]
  constructor <;> intro h <;> linarith

theorem moreLikely_might (h : Strict P.inducedGe A B) : probMight P 1 A := by
  have hlt := h.2
  rw [Measure.inducedGe_iff_real, not_le] at hlt
  have := measureReal_nonneg (μ := P) (s := B)
  show 1 - 1 < P.real A
  linarith

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
