module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Phonology.HarmonicGrammar.MaxEnt

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
* `RealizationProblem`: a target mapping that one grammar must realize on every input.
* `RealizationProblem.IsHGRealizable`, `RealizationProblem.IsOTRealizable`: realizability by a
  non-negative weighting and by a ranking.
* `RealizationProblem.ercs`: the winner–loser ERCs of a problem.

## Main results

* `ot_lex_imp_higher_harmony`: lexicographic dominance gives higher harmony under exponentially
  separated weights.
* `maxent_ot_limit`: MaxEnt concentrates on the OT winner as the weights are scaled up.
* `RealizationProblem.realizedByRanking_iff_satisfiedBy`: OT-realization is ERC satisfaction.
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
    times the sum of all lower-ranked weights. No combination of lower-ranked violations can then
    override a single higher-ranked violation difference, as under OT's strict ranking. -/
def ExponentiallySeparated {n : Nat} (w : Fin n → ℝ) (M : Nat) : Prop :=
  (∀ i, 0 < w i) ∧
  ∀ k : Fin n, (M : ℝ) * (univ.filter (· > k)).sum w < w k

/-- The exponential weights give constraint `i` the weight `(M+1)^(n−1−i)`, so the
    highest-ranked constraint `0` gets the largest weight `(M+1)^(n−1)`. -/
def expWeights (n : Nat) (M : Nat) : Fin n → ℝ :=
  fun i => ((M + 1 : ℝ) ^ (n - 1 - i.val))

/-- Exponential weights are positive. -/
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

/-- Exponential weights are exponentially separated. -/
theorem expWeights_separated (n : Nat) (M : Nat) (hM : 0 < M) :
    ExponentiallySeparated (expWeights n M) M :=
  ⟨expWeights_pos n M, fun k => expWeights_bound n M hM k⟩

/-! ### Ganging (complement of exponential separation) -/

/-- Two constraints with weights `w₁` and `w₂` **gang** against a third with weight `w₃` when each
    is weaker than `w₃` but together they are stronger. Under OT's strict ranking a lower-ranked
    constraint never overrides a higher-ranked one, however many violations accumulate. -/
def Ganging (w₁ w₂ w₃ : ℝ) : Prop :=
  0 < w₁ ∧ 0 < w₂ ∧ 0 < w₃ ∧
  w₁ < w₃ ∧ w₂ < w₃ ∧
  w₃ < w₁ + w₂

/-- The weights `2`, `2`, and `3` exhibit ganging. -/
theorem ganging_example : Ganging 2 2 3 := by
  unfold Ganging; norm_num

/-- With exponentially separated weights (M = 1), each constraint
    outweighs the total of all lower weights. -/
theorem no_ganging_when_separated {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k : Fin n) :
    (univ.filter (· > k)).sum w < w k := by
  have h := hw.2 k
  simp only [Nat.cast_one, one_mul] at h
  exact h

/-- With exponentially separated weights (`M = 1`), no two distinct lower-ranked constraints `i`
    and `j` gang against a higher-ranked `k`, since their combined weight is at most the total
    lower weight, which `no_ganging_when_separated` bounds strictly below `w k`. -/
theorem exponential_separation_precludes_ganging {n : Nat} (w : Fin n → ℝ)
    (hw : ExponentiallySeparated w 1) (k i j : Fin n)
    (hi : k < i) (hj : k < j) (hij : i ≠ j) :
    ¬ Ganging (w i) (w j) (w k) := by
  rintro ⟨_, _, _, _, _, hgang⟩
  have hsum : (univ.filter (· > k)).sum w < w k := no_ganging_when_separated w hw k
  have hsub : ({i, j} : Finset (Fin n)) ⊆ univ.filter (· > k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, gt_iff_lt]
    rcases hx with rfl | rfl <;> assumption
  have hpair : w i + w j ≤ (univ.filter (· > k)).sum w := by
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => (hw.1 l).le)
  linarith

/-! ### HG–OT agreement -/

/-- The **HG–OT agreement lemma** states that with exponentially separated weights and bounded
    violations, lexicographic dominance implies strictly lower weighted violations, so the
    lexicographically better candidate has strictly higher harmony. The proof splits the
    difference of the weighted sums at the first coordinate `k` where the profiles differ.
    Earlier terms cancel, the term at `k` contributes at least `wₖ`, and the later terms total at
    most `M` times the sum of the lower weights, which separation bounds below `wₖ`. -/
theorem lex_imp_lower_violations {n : Nat} (w : Fin n → ℝ) (M : Nat)
    (va vb : Fin n → Nat)
    (hM : ∀ i, va i ≤ M ∧ vb i ≤ M)
    (hw : ExponentiallySeparated w M)
    (hlex : toLex va < toLex vb) :
    w ⬝ᵥ (Nat.cast ∘ va) < w ⬝ᵥ (Nat.cast ∘ vb) := by
  obtain ⟨k, h_agree, h_lt⟩ :
      ∃ k : Fin n, (∀ i, i < k → va i = vb i) ∧ va k < vb k := hlex
  simp only [dotProduct, Function.comp_apply]
  -- Suffices: 0 < Σ w_i · (vb_i − va_i)
  suffices hpos : (0 : ℝ) <
      univ.sum (fun i ↦ w i * ((vb i : ℝ) - (va i : ℝ))) by
    have hlink : univ.sum (fun i ↦ w i * (va i : ℝ)) +
        univ.sum (fun i ↦ w i * ((vb i : ℝ) - (va i : ℝ))) =
        univ.sum (fun i ↦ w i * (vb i : ℝ)) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
    linarith
  -- Split the sum: f(k) + Σ_{i≠k} f(i)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  -- Split erase k into i < k and i > k
  have hsplit : univ.erase k =
      univ.filter (· < k) ∪ univ.filter (· > k) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_erase] at hi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases lt_or_gt_of_ne hi.1 with h | h
      · exact Or.inl ⟨Finset.mem_univ _, h⟩
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
    · intro hi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
      rw [Finset.mem_erase]
      rcases hi with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨ne_of_lt h, Finset.mem_univ _⟩
      · exact ⟨ne_of_gt h, Finset.mem_univ _⟩
  have hdisj : Disjoint (univ.filter (· < k) : Finset (Fin n))
      (univ.filter (· > k)) := by
    rw [Finset.disjoint_left]
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hsplit, Finset.sum_union hdisj]
  -- Terms i < k: each is 0
  have hlt_zero : (univ.filter (· < k)).sum
      (fun i ↦ w i * ((vb i : ℝ) - (va i : ℝ))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [h_agree i hi, sub_self, mul_zero]
  -- Term at k: w_k · (vb_k − va_k) ≥ w_k > 0
  have hk_bound : w k ≤ w k * ((vb k : ℝ) - (va k : ℝ)) := by
    have h1 : (va k : ℝ) + 1 ≤ (vb k : ℝ) := by exact_mod_cast h_lt
    nlinarith [(hw.1 k).le]
  -- Terms i > k: each ≥ −w_i · M, so sum ≥ −M · Σ_{i>k} w_i
  have hgt_bound : -(M : ℝ) * (univ.filter (· > k)).sum w ≤
      (univ.filter (· > k)).sum
        (fun i ↦ w i * ((vb i : ℝ) - (va i : ℝ))) := by
    have h_each : ∀ i ∈ univ.filter (· > k),
        -(w i * (M : ℝ)) ≤ w i * ((vb i : ℝ) - (va i : ℝ)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hva : (va i : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hM i).1
      nlinarith [(hw.1 i).le]
    have h_neg_sum : (univ.filter (· > k)).sum (fun i ↦ -(w i * (M : ℝ))) =
        -(M : ℝ) * (univ.filter (· > k)).sum w := by
      trans (univ.filter (· > k)).sum (fun i ↦ -(M : ℝ) * w i)
      · apply Finset.sum_congr rfl; intro i _; ring
      · rw [← Finset.mul_sum]
    linarith [Finset.sum_le_sum h_each]
  -- Combine: w_k − M · Σ_{i>k} w_i > 0 from ExponentiallySeparated
  linarith [hw.2 k, hlt_zero]

/-- An exponentially separated weighting is strictly monotone on the `M`-bounded part of the
lexicographic order. This is a concrete form of [riggle-2009b]'s order-preserving map from the
violation semiring to tropical costs. -/
theorem strictMonoOn_dotProduct {n : Nat} {w : Fin n → ℝ} {M : Nat}
    (hw : ExponentiallySeparated w M) :
    StrictMonoOn (fun v : ViolationProfile n => w ⬝ᵥ (Nat.cast ∘ ofLex v))
      {v | ∀ i, ofLex v i ≤ M} :=
  fun _ ha _ hb hlex => lex_imp_lower_violations w M _ _ (fun i => ⟨ha i, hb i⟩) hw hlex

/-- If candidate `a` lexicographically beats `b` on the violation profile induced by `ranking`
    and `M` bounds all violations, then `a` has strictly higher harmony than `b` under the
    exponential weights `expWeights ranking.length M`. -/
theorem ot_lex_imp_higher_harmony {C : Type*}
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M)
    (a b : C)
    (hbound : ∀ con ∈ ranking, con a ≤ M ∧ con b ≤ M)
    (hlex : toLex (fun i : Fin ranking.length => (ranking.get i) a) <
            toLex (fun i : Fin ranking.length => (ranking.get i) b)) :
    harmonyScore ranking.get (expWeights ranking.length M) a >
    harmonyScore ranking.get (expWeights ranking.length M) b := by
  show -(expWeights ranking.length M ⬝ᵥ (Nat.cast ∘ fun i => ranking.get i b)) <
       -(expWeights ranking.length M ⬝ᵥ (Nat.cast ∘ fun i => ranking.get i a))
  rw [neg_lt_neg_iff]
  exact lex_imp_lower_violations (expWeights ranking.length M) M
    (fun i => ranking.get i a) (fun i => ranking.get i b)
    (fun i => hbound (ranking.get i) (by simp [List.get_eq_getElem, List.getElem_mem]))
    (expWeights_separated ranking.length M hM) hlex

/-! ### MaxEnt → OT limit -/

/-- Scaling exponentially separated weights concentrates the MaxEnt distribution on a candidate
    that lexicographically beats every competitor under a ranking with violation bound `M`, since
    it has the greatest harmony (`ot_lex_imp_higher_harmony`). -/
theorem maxent_ot_limit {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
    (ranking : List (Constraint C)) (M : Nat) (hM : 0 < M) (c_opt : C)
    (hbound : ∀ c : C, ∀ con ∈ ranking, con c ≤ M)
    (hlex : ∀ c, c ≠ c_opt →
      toLex (fun i : Fin ranking.length => (ranking.get i) c_opt) <
      toLex (fun i : Fin ranking.length => (ranking.get i) c)) :
    Tendsto (fun α : ℝ ↦
      (maxEnt (ConstraintSet.violations ranking.get) (α • expWeights ranking.length M)).real
        {c_opt}) atTop (𝓝 1) :=
  tendsto_maxEnt_smul_atTop _ _ fun c hc ↦ ot_lex_imp_higher_harmony ranking M hM c_opt c
    (fun con hcon ↦ ⟨hbound c_opt con hcon, hbound c con hcon⟩) (hlex c hc)

/-! ## Realizability

A framework realizes a target mapping when one of its grammars selects the target output on
every input. -/

variable {Input Output ι : Type*} {n : ℕ}

/-! ### Realization problems -/

/-- A realization problem is a target mapping that a single grammar over the constraint set `con`
    must realize on every input at once. For OT it is the data of [tesar-smolensky-1995]'s ranking
    problem. -/
structure RealizationProblem (Input : Type*) (Output : Type*) (ι : Type*) where
  /-- The grammar handles a finite set of inputs. -/
  inputs : Finset Input
  /-- Each input has a finite candidate set. -/
  cands : Input → Finset Output
  /-- The constraints, evaluated on input–output mappings. -/
  con : ConstraintSet (Input × Output) ι
  /-- The grammar must select the target output on each input. -/
  target : Input → Output
  /-- Each target output is in its input's candidate set. -/
  target_mem : ∀ i ∈ inputs, target i ∈ cands i

namespace RealizationProblem

/-- The weighting `w` *HG-realizes* the target when on every input the target harmonically
    dominates every other candidate. -/
def realizedByWeighting [Fintype ι] (P : RealizationProblem Input Output ι) (w : ι → ℝ) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    harmonyDominates P.con w (i, P.target i) (i, o)

/-- A problem is HG-realizable when some non-negative weighting realizes its target.
    Non-negativity is [pater-2009]'s standard HG; [coetzee-pater-2011] also discuss negative
    weights. -/
def IsHGRealizable [Fintype ι] (P : RealizationProblem Input Output ι) : Prop :=
  ∃ w : ι → ℝ, 0 ≤ w ∧ P.realizedByWeighting w

/-- The ranking `σ` *OT-realizes* the target when on every input it picks the target, which
    strictly lex-dominates every alternative under `σ`. -/
def realizedByRanking (P : RealizationProblem Input Output ι) (σ : Ranking ι n) : Prop :=
  ∀ i ∈ P.inputs, PicksAt P.cands P.con σ i (P.target i)

/-- A problem is OT-realizable when some constraint ranking realizes its target. -/
def IsOTRealizable (P : RealizationProblem Input Output (Fin n)) : Prop :=
  ∃ σ : Ranking (Fin n) n, P.realizedByRanking σ

instance [DecidableEq Output] (P : RealizationProblem Input Output ι) (σ : Ranking ι n) :
    Decidable (P.realizedByRanking σ) := by
  unfold realizedByRanking; infer_instance

instance [DecidableEq Output] (P : RealizationProblem Input Output (Fin n)) :
    Decidable P.IsOTRealizable := by
  unfold IsOTRealizable; infer_instance

/-- `σ` OT-realizes `P` iff for every input the target is the unique
    `Tableau.optimal` of the tableau of the input's constraints under `σ`. -/
theorem realizedByRanking_iff_optimal [DecidableEq Output]
    (P : RealizationProblem Input Output ι) (σ : Ranking ι n) :
    P.realizedByRanking σ ↔ ∀ i ∈ P.inputs,
      (Tableau.ofRanking (P.con.comap (i, ·)) σ (P.cands i)).optimal = {P.target i} :=
  forall₂_congr fun _ _ ↦ by rw [Tableau.optimal_eq_singleton_iff]; rfl

/-! ### OT-realization is ERC satisfaction -/

/-- The winner–loser ERCs of a problem have one comparative row for each input and non-target
    candidate ([prince-2002]). -/
def ercs [Fintype ι] [DecidableEq Output] (P : RealizationProblem Input Output ι) :
    Finset (ERC ι) :=
  P.inputs.biUnion fun i => ((P.cands i).erase (P.target i)).image fun o =>
    ercOfProfiles (P.con · (i, P.target i)) (P.con · (i, o))

theorem mem_ercs [Fintype ι] [DecidableEq Output] {P : RealizationProblem Input Output ι}
    {α : ERC ι} :
    α ∈ P.ercs ↔ ∃ i ∈ P.inputs, ∃ o ∈ P.cands i, o ≠ P.target i ∧
      ercOfProfiles (P.con · (i, P.target i)) (P.con · (i, o)) = α := by
  simp only [ercs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_erase]
  tauto

/-- Provided no competitor ties the target's violation profile, `σ` realizes the target iff `σ`
    satisfies every winner–loser ERC ([prince-2002]). -/
theorem realizedByRanking_iff_satisfiedBy [Fintype ι] [DecidableEq Output]
    {P : RealizationProblem Input Output ι} {σ : Ranking ι n}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      (P.con · (i, P.target i)) ≠ (P.con · (i, o))) :
    P.realizedByRanking σ ↔ ∀ α ∈ P.ercs, α.SatisfiedBy σ := by
  constructor
  · intro h α hα
    obtain ⟨i, hi, o, ho, hone, rfl⟩ := mem_ercs.mp hα
    exact (satisfiedBy_ercOfProfiles_iff_le σ _ _).mpr ((h i hi).2 o ho hone).le
  · intro h i hi
    refine ⟨P.target_mem i hi, fun o ho hone ↦ ?_⟩
    refine lt_of_le_of_ne ((satisfiedBy_ercOfProfiles_iff_le σ _ _).mp
      (h _ (mem_ercs.mpr ⟨i, hi, o, ho, hone, rfl⟩))) fun heq => hvp i hi o ho hone ?_
    exact funext fun c => by simpa using congrFun (toLex_inj.mp heq) (σ.symm c)

/-- OT-realizability is consistency of the problem's ERC set
    ([prince-2002]). -/
theorem isOTRealizable_iff_linearExtensions_nonempty [DecidableEq Output]
    {P : RealizationProblem Input Output (Fin n)}
    (hvp : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
      (P.con · (i, P.target i)) ≠ (P.con · (i, o))) :
    P.IsOTRealizable ↔ (ERC.linearExtensions P.ercs).Nonempty :=
  exists_congr fun _ => (realizedByRanking_iff_satisfiedBy hvp).trans
    ERC.mem_linearExtensions.symm

end RealizationProblem

/-! ### Forward containment — OT ⊆ HG -/

/-- An OT-realizable problem is HG-realizable by exponentially separated weights permuted by the
    ranking, with the largest violation count as the separation bound. -/
theorem RealizationProblem.IsOTRealizable.isHGRealizable
    {P : RealizationProblem Input Output (Fin n)} (h : P.IsOTRealizable) : P.IsHGRealizable := by
  obtain ⟨σ, hσ⟩ := h
  set M := (P.inputs.sup fun i ↦ (P.cands i).sup fun o ↦ Finset.univ.sup (P.con · (i, o))) + 1
  have hbound : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, ∀ k, P.con k (i, o) ≤ M := fun i hi o ho k =>
    ((Finset.le_sup (f := (P.con · (i, o))) (Finset.mem_univ k)).trans
      ((Finset.le_sup (f := fun o ↦ Finset.univ.sup (P.con · (i, o))) ho).trans
        (Finset.le_sup (f := fun i ↦ (P.cands i).sup fun o ↦ Finset.univ.sup (P.con · (i, o)))
          hi))).trans (Nat.le_succ _)
  refine ⟨expWeights n M ∘ σ.symm, fun k => (expWeights_pos n M (σ.symm k)).le, ?_⟩
  intro i hi o ho hne
  rw [harmonyDominates_iff, harmonyScore, harmonyScore, neg_lt_neg_iff,
    comp_equiv_symm_dotProduct, comp_equiv_symm_dotProduct]
  apply lex_imp_lower_violations _ M
  · intro k
    exact ⟨hbound i hi (P.target i) (P.target_mem i hi) (σ k), hbound i hi o ho (σ k)⟩
  · exact expWeights_separated n M (Nat.succ_pos _)
  · exact (hσ i hi).2 o ho hne

/-! ### Strict containment — the cumulativity gap -/

/-- HG with non-negative weights strictly contains OT. The witness is [coetzee-pater-2011]'s
    abstract Lyman's Law instance after [ito-mester-1986], in which faithful candidates violate
    `{M1}`, `{M2}`, and `{M1, M2}` against an unfaithful `{F}` and only the third input targets
    the unfaithful output. The weights `[3, 2, 2]` realize it, since `2 + 2 > 3` holds on the
    third input only, while the winner–loser ERCs `F ≫ M1`, `F ≫ M2`, and "some markedness
    constraint above `F`" are inconsistent. -/
theorem hg_strictly_contains_ot :
    ∃ (Input Output : Type) (n : ℕ) (P : RealizationProblem Input Output (Fin n)),
      P.IsHGRealizable ∧ ¬ P.IsOTRealizable := by
  refine ⟨Fin 3, Bool, 3,
    { inputs := Finset.univ
      cands := fun _ => Finset.univ
      con := fun k x ↦ if x.2 then ![![0, 1, 0], ![0, 0, 1], ![0, 1, 1]] x.1 k else ![1, 0, 0] k
      target := ![true, true, false]
      target_mem := fun _ _ => Finset.mem_univ _ },
    ⟨![3, 2, 2], fun k => by fin_cases k <;> norm_num, ?_⟩, ?_⟩
  · intro i _ o _ hne
    simp only [harmonyDominates_iff, harmonyScore, dotProduct, Fin.sum_univ_three]
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

/-- Every partial-order-realized target is OT-realized, since any single
    consistent extension realizes it. -/
theorem RealizationProblem.IsPartialOrderRealizable.isOTRealizable
    {P : RealizationProblem Input Output (Fin n)}
    (h : P.IsPartialOrderRealizable) : P.IsOTRealizable := by
  obtain ⟨r, hpo, hreal⟩ := h
  have := hpo
  obtain ⟨σ, hσ⟩ := exists_isConsistent r
  exact ⟨σ, hreal σ hσ⟩

/-- Every OT-realized target is partial-order-realized — the witness is the
    σ-induced total ranking, whose unique consistent extension is σ itself. -/
theorem RealizationProblem.IsOTRealizable.isPartialOrderRealizable
    {P : RealizationProblem Input Output (Fin n)}
    (h : P.IsOTRealizable) : P.IsPartialOrderRealizable := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.toRel, inferInstance,
    fun τ hτ => Ranking.toRel_le_toRel_iff.mp hτ ▸ hσ⟩

/-- Under categorical realizability, OT and partial orders coincide; the
    partial order's advantage is probabilistic, the uniform measure on its linear extensions. -/
theorem RealizationProblem.isOTRealizable_iff_isPartialOrderRealizable
    (P : RealizationProblem Input Output (Fin n)) :
    P.IsOTRealizable ↔ P.IsPartialOrderRealizable :=
  ⟨IsOTRealizable.isPartialOrderRealizable, IsPartialOrderRealizable.isOTRealizable⟩

end HarmonicGrammar
