module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Linglib.Core.Algebra.Order.BigOperators.Ring.Finset

/-!
# Expressivity of OT, Harmonic Grammar, and MaxEnt

This file compares the expressive power of Optimality Theory (OT), Harmonic Grammar (HG), and
maximum-entropy grammar (MaxEnt). With exponentially separated weights the harmony order of HG
agrees with the lexicographic comparison of OT, so every OT grammar is an HG grammar, and as the
weights are scaled up MaxEnt concentrates on the OT winner. The containment of OT in HG is
strict because of *cumulativity*, in which several low-weight violations together outweigh a
single high-weight one. The comparison follows Smolensky and Legendre, Pater, and Coetzee and
Pater, and the cumulativity witness is Coetzee and Pater's version of Itô and Mester's Lyman's
Law data.

## Main definitions

* `ExponentiallySeparated`, `expWeights`: the HG reading of an OT ranking.
* `RealizationProblem`: a constraint system with target outputs that one grammar must select on
  every input.
* `RealizationProblem.IsHGRealizable`, `RealizationProblem.IsOTRealizable`: realizability by a
  non-negative weighting and by a ranking.
* `RealizationProblem.ercs`: the winner–loser ERCs of a problem.

## Main results

* `Pi.strictMonoOn_sum_mul_iff` (in `Core`): a weighting orders the `M`-bounded violation
  profiles lexicographically exactly when it is exponentially separated.
* `Tableau.optimal_eq_argmax_harmonyScore`: under exponentially separated weights a tableau's OT
  winners are its HG winners.
* `maxent_ot_limit`: MaxEnt concentrates on the OT winner as the weights are scaled up.
* `RealizationProblem.realizedByRanking_iff_satisfiedBy`: OT-realization is ERC satisfaction.
* `ConstraintSystem.exists_hgLanguage_eq_language`: on finitely many inputs every OT language is
  an HG language.
* `RealizationProblem.IsOTRealizable.isHGRealizable`, `hg_strictly_contains_ot`: OT is strictly
  contained in HG.
* `RealizationProblem.isOTRealizable_iff_isPartialOrderRealizable`: partially ordered grammars
  realize exactly the OT-realizable targets, so their advantage is probabilistic.

## References

* [A. Prince and P. Smolensky, *Optimality Theory: Constraint Interaction in Generative Grammar*
  (1993)][prince-smolensky-1993]
* [P. Smolensky and G. Legendre, *The Harmonic Mind: From Neural Computation to
  Optimality-Theoretic Grammar* (2006)][smolensky-legendre-2006]
* [J. Pater, *Morpheme-specific phonology: Constraint indexation and inconsistency resolution*
  (2009)][pater-2009]
* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
* [J. Itô and A. Mester, *The Phonology of Voicing in Japanese* (1986)][ito-mester-1986]
* [B. Hayes and C. Wilson, *A Maximum Entropy Model of Phonotactics and Phonotactic Learning*
  (2008)][hayes-wilson-2008]
* [B. Tesar and P. Smolensky, *The Learnability of Optimality Theory* (1995)][tesar-smolensky-1995]
* [A. Prince, *Entailed Ranking Arguments* (2002)][prince-2002]
* [J. Riggle, *Violation Semirings in Optimality Theory* (2009)][riggle-2009b]
-/

@[expose] public section

namespace HarmonicGrammar

open OptimalityTheory Real Finset Filter Topology
open OptimalityTheory

/-! ### OT → HG weights

An OT ranking is a `List (Constraint C)`; as a `ConstraintSet C (Fin ranking.length)` it is just
`ranking.get`. The Harmonic-Grammar reading of that ranking with violation bound
`M` weights coordinate `i` (0 = highest) by `(M+1)^(n−1−i)` — the `expWeights`
vector below. So the HG harmony of an OT ranking is
`harmonyScore ranking.get (expWeights ranking.length M)`, with no separate
weighted-constraint object. -/

/-! ### Exponentially separated weights -/

/-- Weights are **exponentially separated** with violation bound `M` when each weight exceeds `M`
    times the sum of all lower-ranked weights. These are exactly the weightings whose weighted
    sums order the `M`-bounded violation profiles lexicographically
    (`Pi.strictMonoOn_sum_mul_iff`), so that no combination of lower-ranked violations overrides
    a single higher-ranked violation difference, as under OT's strict ranking. -/
def ExponentiallySeparated {n : Nat} (w : Fin n → ℝ) (M : Nat) : Prop :=
  ∀ k : Fin n, (M : ℝ) * ∑ i ∈ Ioi k, w i < w k

/-- Exponentially separated weights are positive. -/
theorem ExponentiallySeparated.pos {n M : ℕ} {w : Fin n → ℝ} (hw : ExponentiallySeparated w M)
    (k : Fin n) : 0 < w k :=
  Pi.pos_of_forall_natCast_mul_sum_Ioi_lt hw k

/-- The exponential weights give constraint `i` the weight `(M+1)^(n−1−i)`, so the
    highest-ranked constraint `0` gets the largest weight `(M+1)^(n−1)`. -/
def expWeights (n : Nat) (M : Nat) : Fin n → ℝ :=
  fun i ↦ ((M + 1 : ℝ) ^ (n - 1 - i.val))

theorem expWeights_pos (n : Nat) (M : Nat) (i : Fin n) :
    0 < expWeights n M i := by
  simp only [expWeights]
  positivity

private lemma filter_gt_insert_succ' {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    univ.filter (· > k) =
    insert (⟨k.val + 1, hk⟩ : Fin n) (univ.filter (· > ⟨k.val + 1, hk⟩)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.lt_def, Fin.ext_iff]
  omega

private lemma succ_not_mem_filter_gt' {n : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    (⟨k.val + 1, hk⟩ : Fin n) ∉ univ.filter (· > ⟨k.val + 1, hk⟩) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; omega

private lemma expWeights_succ_eq' {n M : ℕ} {k : Fin n} (hk : k.val + 1 < n) :
    expWeights n M k = (↑M + 1) * expWeights n M ⟨k.val + 1, hk⟩ := by
  simp only [expWeights]
  rw [show n - 1 - k.val = (n - 1 - (k.val + 1)) + 1 from by omega, pow_succ]; ring

private lemma expWeights_bound (n M : ℕ) (hM : 0 < M) (k : Fin n) :
    (↑M : ℝ) * (univ.filter (· > k)).sum (expWeights n M) <
    expWeights n M k := by
  by_cases hk : k.val + 1 = n
  · have hempty : univ.filter (· > k) = (∅ : Finset (Fin n)) := by
      ext i; constructor
      · intro hi; simp only [Finset.mem_filter, Fin.lt_def] at hi; omega
      · exact (Finset.notMem_empty _).elim
    rw [hempty, Finset.sum_empty, mul_zero]
    exact expWeights_pos n M k
  · have hlt : k.val + 1 < n := by omega
    rw [filter_gt_insert_succ' hlt,
      Finset.sum_insert (succ_not_mem_filter_gt' hlt), mul_add]
    have ih := expWeights_bound n M hM ⟨k.val + 1, hlt⟩
    rw [expWeights_succ_eq' hlt]
    linarith

theorem expWeights_separated (n : Nat) (M : Nat) (hM : 0 < M) :
    ExponentiallySeparated (expWeights n M) M := fun k ↦ by
  rw [← filter_lt_eq_Ioi]
  exact expWeights_bound n M hM k

/-! ### Ganging (complement of exponential separation) -/

/-- Two constraints with weights `w₁` and `w₂` **gang** against a third with weight `w₃` when each
    is weaker than `w₃` but together they are stronger. Under OT's strict ranking a lower-ranked
    constraint never overrides a higher-ranked one, however many violations accumulate. -/
def Ganging (w₁ w₂ w₃ : ℝ) : Prop :=
  0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
  w₁ < w₃ ∧ w₂ < w₃ ∧
  w₃ < w₁ + w₂

theorem ganging_example : Ganging 2 2 3 := by
  unfold Ganging; norm_num

theorem no_ganging_when_separated {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k : Fin n) : ∑ i ∈ Ioi k, w i < w k := by
  simpa using hw k

theorem exponential_separation_precludes_ganging {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k i j : Fin n)
    (hi : k < i) (hj : k < j) (hij : i ≠ j) :
    ¬ Ganging (w i) (w j) (w k) := by
  rintro ⟨_, _, _, _, _, hgang⟩
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Ioi k := by
    simp [Finset.insert_subset_iff, hi, hj]
  have hpair : w i + w j ≤ ∑ l ∈ Ioi k, w l := by
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ ↦ (hw.pos l).le
  linarith [no_ganging_when_separated w hw k]

/-! ### HG–OT agreement -/

theorem _root_.OptimalityTheory.Tableau.optimal_eq_argmax_harmonyScore {C : Type*} {n M : ℕ}
    {w : Fin n → ℝ} (t : Tableau C n) (hw : ExponentiallySeparated w M)
    (hM : ∀ c ∈ t.candidates, ∀ p, t.constraints p c ≤ M) :
    t.optimal = t.candidates.argmax (harmonyScore t.constraints w) :=
  Finset.argmin_eq_argmax_of_le_iff fun a ha b hb ↦ by
    rw [harmonyScore, harmonyScore, neg_le_neg_iff]
    exact ((Pi.strictMonoOn_sum_mul hw).le_iff_le (hM a ha) (hM b hb)).symm

/-! ### MaxEnt → OT limit -/

/-- Scaling exponentially separated weights concentrates the MaxEnt distribution on the sole OT
    winner of a ranking with violation bound `M`, which is the sole HG winner
    (`Tableau.optimal_eq_argmax_harmonyScore`). -/
theorem maxent_ot_limit {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M) (c_opt : C)
    (hbound : ∀ c : C, ∀ con ∈ ranking, con c ≤ M)
    (hopt : (Tableau.ofList Finset.univ ranking).optimal = {c_opt}) :
    Tendsto (fun α : ℝ ↦
      (maxEnt (ConstraintSet.violations ranking.get) (α • expWeights ranking.length M)).real
        {c_opt}) atTop (𝓝 1) := by
  refine tendsto_maxEnt_smul_atTop (T := ConstraintSet.violations ranking.get)
    (w := expWeights ranking.length M) ?_
  rw [harmony_violations, ← hopt, Tableau.optimal_eq_argmax_harmonyScore _
    (expWeights_separated _ M hM) fun c _ p ↦ hbound c _ (List.get_mem ranking p)]
  rfl

/-! ## Realizability

A framework realizes a target mapping when one of its grammars selects the target output on
every input. -/

variable {Input Output ι : Type*} {n : ℕ}

/-! ### Realization problems -/

/-- A realization problem is a constraint system with a target output for each of finitely many
    inputs, which a single grammar must select on every input at once. For OT it is the data of
    [tesar-smolensky-1995]'s ranking problem. -/
structure RealizationProblem (Input : Type*) (Output : Type*) (ι : Type*)
    extends ConstraintSystem Input Output ι where
  /-- The grammar handles a finite set of inputs. -/
  inputs : Finset Input
  /-- The grammar must select the target output on each input. -/
  target : Input → Output
  /-- Each target output is a candidate of its input. -/
  target_mem : ∀ i ∈ inputs, target i ∈ gen i

namespace RealizationProblem

/-- The weighting `w` *HG-realizes* the target when on every input the target is the sole
    candidate of greatest harmony. -/
def realizedByWeighting [Fintype ι] (P : RealizationProblem Input Output ι) (w : ι → ℝ) : Prop :=
  ∀ i ∈ P.inputs, P.hgLanguage w i = {P.target i}

/-- A problem is HG-realizable when some non-negative weighting realizes its target.
    Non-negativity is [pater-2009]'s standard HG; [coetzee-pater-2011] also discuss negative
    weights. -/
def IsHGRealizable [Fintype ι] (P : RealizationProblem Input Output ι) : Prop :=
  ∃ w : ι → ℝ, 0 ≤ w ∧ P.realizedByWeighting w

/-- The ranking `σ` *OT-realizes* the target when on every input it picks the target, the sole
    winner of the input's tableau under `σ`. -/
def realizedByRanking (P : RealizationProblem Input Output ι) (σ : Ranking ι n) : Prop :=
  ∀ i ∈ P.inputs, PicksAt P.toConstraintSystem σ i (P.target i)

/-- A problem is OT-realizable when some constraint ranking realizes its target. -/
def IsOTRealizable (P : RealizationProblem Input Output (Fin n)) : Prop :=
  ∃ σ : Ranking (Fin n) n, P.realizedByRanking σ

instance [DecidableEq Output] (P : RealizationProblem Input Output ι) (σ : Ranking ι n) :
    Decidable (P.realizedByRanking σ) := by
  unfold realizedByRanking; infer_instance

instance [DecidableEq Output] (P : RealizationProblem Input Output (Fin n)) :
    Decidable P.IsOTRealizable := by
  unfold IsOTRealizable; infer_instance

/-! ### OT-realization is ERC satisfaction -/

/-- The winner–loser ERCs of a problem have one comparative row for each input and non-target
    candidate ([prince-2002]). -/
def ercs [Fintype ι] [DecidableEq Output] (P : RealizationProblem Input Output ι) :
    Finset (ERC ι) :=
  P.inputs.biUnion fun i ↦ ((P.gen i).erase (P.target i)).image fun o ↦
    ercOfProfiles (P.con · (i, P.target i)) (P.con · (i, o))

theorem mem_ercs [Fintype ι] [DecidableEq Output] {P : RealizationProblem Input Output ι}
    {α : ERC ι} :
    α ∈ P.ercs ↔ ∃ i ∈ P.inputs, ∃ o ∈ P.gen i, o ≠ P.target i ∧
      ercOfProfiles (P.con · (i, P.target i)) (P.con · (i, o)) = α := by
  simp only [ercs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase]
  tauto

theorem realizedByRanking_iff_satisfiedBy [Fintype ι] [DecidableEq Output]
    {P : RealizationProblem Input Output ι} {σ : Ranking ι n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.con · (i, P.target i)) ≠ (P.con · (i, o))) :
    P.realizedByRanking σ ↔ ∀ α ∈ P.ercs, α.SatisfiedBy σ := by
  constructor
  · intro h α hα
    obtain ⟨i, hi, o, ho, hone, rfl⟩ := mem_ercs.mp hα
    exact (satisfiedBy_ercOfProfiles_iff_le σ _ _).mpr
      ((picksAt_iff.1 (h i hi)).2 o ho hone).le
  · intro h i hi
    refine picksAt_iff.2 ⟨P.target_mem i hi, fun o ho hone ↦ ?_⟩
    refine lt_of_le_of_ne ((satisfiedBy_ercOfProfiles_iff_le σ _ _).mp
      (h _ (mem_ercs.mpr ⟨i, hi, o, ho, hone, rfl⟩))) fun heq ↦ hvp i hi o ho hone ?_
    exact funext fun c ↦ by simpa using congrFun (toLex_inj.mp heq) (σ.symm c)

theorem isOTRealizable_iff_linearExtensions_nonempty [DecidableEq Output]
    {P : RealizationProblem Input Output (Fin n)}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.gen i, o ≠ P.target i →
      (P.con · (i, P.target i)) ≠ (P.con · (i, o))) :
    P.IsOTRealizable ↔ (ERC.linearExtensions P.ercs).Nonempty :=
  exists_congr fun _ ↦ (realizedByRanking_iff_satisfiedBy hvp).trans
    ERC.mem_linearExtensions.symm

end RealizationProblem

/-! ### Forward containment — OT ⊆ HG -/

theorem _root_.OptimalityTheory.ConstraintSystem.exists_hgLanguage_eq_language [Fintype ι]
    (S : ConstraintSystem Input Output ι) (X : Finset Input) (σ : Ranking ι n) :
    ∃ w : ι → ℝ, 0 ≤ w ∧ ∀ i ∈ X, S.hgLanguage w i = S.language σ i := by
  set M := (X.sup fun i ↦ (S.gen i).sup fun o ↦ Finset.univ.sup (S.con · (i, o))) + 1
  have hbound : ∀ i ∈ X, ∀ o ∈ S.gen i, ∀ k, S.con k (i, o) ≤ M := fun i hi o ho k ↦
    ((Finset.le_sup (f := (S.con · (i, o))) (Finset.mem_univ k)).trans
      ((Finset.le_sup (f := fun o ↦ Finset.univ.sup (S.con · (i, o))) ho).trans
        (Finset.le_sup (f := fun i ↦ (S.gen i).sup fun o ↦ Finset.univ.sup (S.con · (i, o)))
          hi))).trans (Nat.le_succ _)
  refine ⟨expWeights n M ∘ σ.symm, fun k ↦ (expWeights_pos n M (σ.symm k)).le, fun i hi ↦ ?_⟩
  rw [ConstraintSystem.hgLanguage, ConstraintSystem.language,
    Tableau.optimal_eq_argmax_harmonyScore _
    (expWeights_separated n M (Nat.succ_pos _)) fun o ho k ↦ hbound i hi o ho (σ k)]
  congr 1
  funext o
  simp only [harmonyScore, comp_equiv_symm_dotProduct]
  rfl

theorem RealizationProblem.IsOTRealizable.isHGRealizable
    {P : RealizationProblem Input Output (Fin n)} (h : P.IsOTRealizable) : P.IsHGRealizable := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨w, hw, h⟩ := P.exists_hgLanguage_eq_language P.inputs σ
  exact ⟨w, hw, fun i hi ↦ (h i hi).trans (hσ i hi)⟩

/-! ### Strict containment — the cumulativity gap -/

theorem hg_strictly_contains_ot :
    ∃ (Input Output : Type) (n : ℕ) (P : RealizationProblem Input Output (Fin n)),
      P.IsHGRealizable ∧ ¬ P.IsOTRealizable := by
  refine ⟨Fin 3, Bool, 3,
    { inputs := Finset.univ
      gen := fun _ ↦ Finset.univ
      con := fun k x ↦ if x.2 then ![![0, 1, 0], ![0, 0, 1], ![0, 1, 1]] x.1 k else ![1, 0, 0] k
      target := ![true, true, false]
      target_mem := fun _ _ ↦ Finset.mem_univ _ },
    ⟨![3, 2, 2], fun k ↦ by fin_cases k <;> norm_num, ?_⟩, ?_⟩
  · refine fun i _ ↦ Finset.argmax_eq_singleton_iff.2 ⟨Finset.mem_univ _, fun o _ hne ↦ ?_⟩
    simp only [harmonyScore, dotProduct, Fin.sum_univ_three]
    fin_cases i <;> cases o <;>
      first
      | (exfalso; exact hne rfl)
      | norm_num [Matrix.cons_val_two, Matrix.tail_cons]
  · rintro ⟨σ, hσ⟩
    rw [RealizationProblem.realizedByRanking_iff_satisfiedBy (by decide)] at hσ
    have h₁ : σ.toRel 0 1 := (simpleERC_satisfiedBy_toRel_iff 0 1 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨0, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₂ : σ.toRel 0 2 := (simpleERC_satisfiedBy_toRel_iff 0 2 σ).mp
      (hσ _ (RealizationProblem.mem_ercs.mpr
        ⟨1, Finset.mem_univ _, false, Finset.mem_univ _, by decide, by decide⟩))
    have h₃ := hσ _ (RealizationProblem.mem_ercs.mpr
      ⟨2, Finset.mem_univ _, true, Finset.mem_univ _, by decide, rfl⟩)
    obtain ⟨w, hwW, hdom⟩ := (ERC.satisfiedBy_iff_dominance σ _).mp h₃ 0 (by decide)
    fin_cases w
    · exact absurd hwW (by decide)
    · exact absurd h₁ (not_le.mpr hdom)
    · exact absurd h₂ (not_le.mpr hdom)

/-! ### Realizability by a partial order -/

namespace RealizationProblem

/-- A grammar `r` **POC-realizes** the target if every consistent extension
    realizes it. Since consistent extensions always exist
    (`exists_isConsistent`), this is never vacuous. -/
def realizedByPartialOrder (P : RealizationProblem Input Output (Fin n))
    (r : Fin n → Fin n → Prop) : Prop :=
  ∀ σ, IsConsistent r σ → P.realizedByRanking σ

/-- A `RealizationProblem` is **POC-realizable** if some partial order
    categorically realizes the target. -/
def IsPartialOrderRealizable (P : RealizationProblem Input Output (Fin n)) : Prop :=
  ∃ r : Fin n → Fin n → Prop, IsPartialOrder (Fin n) r ∧ P.realizedByPartialOrder r

end RealizationProblem

/-! ### Containments — OT ⊆ POC, POC ⊆ OT (categorical) -/

theorem RealizationProblem.IsPartialOrderRealizable.isOTRealizable
    {P : RealizationProblem Input Output (Fin n)}
    (h : P.IsPartialOrderRealizable) : P.IsOTRealizable := by
  obtain ⟨r, hpo, hreal⟩ := h
  have := hpo
  obtain ⟨σ, hσ⟩ := exists_isConsistent r
  exact ⟨σ, hreal σ hσ⟩

theorem RealizationProblem.IsOTRealizable.isPartialOrderRealizable
    {P : RealizationProblem Input Output (Fin n)}
    (h : P.IsOTRealizable) : P.IsPartialOrderRealizable := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.toRel, inferInstance,
    fun τ hτ ↦ Ranking.toRel_le_toRel_iff.mp hτ ▸ hσ⟩

theorem RealizationProblem.isOTRealizable_iff_isPartialOrderRealizable
    (P : RealizationProblem Input Output (Fin n)) :
    P.IsOTRealizable ↔ P.IsPartialOrderRealizable :=
  ⟨IsOTRealizable.isPartialOrderRealizable, IsPartialOrderRealizable.isOTRealizable⟩

end HarmonicGrammar
