module

public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Linglib.Phonology.HarmonicGrammar.Expressivity
public import Linglib.Phonology.HarmonicGrammar.MaxEnt
public import Linglib.Phonology.HarmonicGrammar.Noise
public import Linglib.Data.Experiments.CoetzeePater2011

/-!
# Coetzee and Pater (2011): The Place of Variation in Phonological Theory

Coetzee and Pater compare grammatical models of phonological variation on English word-final
t/d-deletion (*west* ~ *wes*). Their four constraints (11) protect t/d by MAX everywhere and by
MAX-PRE-V and MAX-FINAL before a vowel and phrase-finally, so every ranking that deletes anywhere
deletes before a consonant, as Labov's generalization over the dialects of (10) requires. In the
partially ordered constraints (POC) model of Kiparsky and Anttila a grammar draws one of its
linear extensions uniformly, and the probability of deletion is the share of them that delete.

Any distribution over rankings, POC's or stochastic OT's, therefore deletes most before a
consonant, and so does Noisy Harmonic Grammar with noisy weights clamped at zero; MaxEnt with
negative weights does not, and variable rules fit any rates. Harmonic Grammar also expresses the
cumulative devoicing of Japanese loanwords, which no distribution over rankings matches and Noisy
HG matches exactly.

## Implementation notes

Locators follow the ROA-946 draft of 6 October 2009, and the printed tables are read from
`Data/Experiments/CoetzeePater2011.json`. Constraint indices follow (11): 0 is \*CT, 1 MAX,
2 MAX-PRE-V and 3 MAX-FINAL, while (23) prints them in the order \*CT, MAX-PRE-V, MAX-FINAL,
MAX. The constraint values of stochastic OT in (14), (21) and (23) come from Praat simulations
and are read as data, not derived.

## TODO

* Rows (b)–(e) of (13) print counts that (9) does not give: counting the linear extensions of
  their grammars gives 0, 2, 4; 8, 6, 8; 2, 0, 4; and 6, 8, 8 of 12, and only the two zero cells
  agree (`deletionProb_eq_pocRates_iff`). Each printed cell is the rate of the two-stratum
  grammar that ranks the fixed faithfulness constraint in a stratum of its own, as if the other
  pairs stayed free. The published chapter has not been checked for a correction.
* §3.3 says that POC can derive only 0, .50 and 1 for pre-consonantal deletion; the grammar of
  row (b) derives 1/3 (`deletionProb_maxPreVOverStarCT_preC_not_mem`).
* p. 21 says that no ranking "yields deletion in only pre-consonantal position", which row (d) of
  (12) does; the argument needs deletion everywhere except pre-consonantally.
* (24) with the two-place weights of (25) gives 33/131, about .252, before a vowel in Tejano,
  where (25) prints 25.03: Goldvarb's expected rates use its unrounded weights.

## References

* [A. W. Coetzee and J. Pater, *The Place of Variation in Phonological Theory*
  (2011)][coetzee-pater-2011]
* [P. Kiparsky, *An OT Perspective on Phonological Variation* (1993)][kiparsky-1993b]
* [A. Anttila, *Deriving Variation from Grammar* (1997)][anttila-1997]
* [W. Labov, *The Child as Linguistic Historian* (1989)][labov-1989]
* [G. R. Guy, *Explanation in Variable Phonology: An Exponential Model of Morphological
  Constraints* (1991)][guy-1991]
* [H. J. Cedergren and D. Sankoff, *Variable Rules: Performance as a Statistical Reflection of
  Competence* (1974)][cedergren-sankoff-1974]
* [P. Boersma, *Functional Phonology* (1998)][boersma-1998]
* [P. Boersma and B. Hayes, *Empirical Tests of the Gradual Learning Algorithm*
  (2001)][boersma-hayes-2001]
* [P. Smolensky and G. Legendre, *The Harmonic Mind: From Neural Computation to
  Optimality-Theoretic Grammar* (2006)][smolensky-legendre-2006]
* [S. Goldwater and M. Johnson, *Learning OT Constraint Rankings Using a Maximum Entropy
  Model* (2003)][goldwater-johnson-2003]
* [J. Itô and A. Mester, *The Phonology of Voicing in Japanese* (1986)][ito-mester-1986]
* [S. Kawahara, *A Faithfulness Ranking Projected from a Perceptibility Scale: The Case of
  [+voice] in Japanese* (2006)][kawahara-2006]
-/

@[expose] public section

namespace CoetzeePater2011

open OptimalityTheory HarmonicGrammar MeasureTheory ProbabilityTheory Finset Real
  Data.Experiments
open scoped NNReal ENNReal

/-! ### Deletion rates by context and by morphology ((7), (10)) -/

/-- The percentage of t/d that dialect `d` deletes before `ctx`, read from (10). -/
def observedRate (d : Dialect) (ctx : Context) : ℕ := (contextRates d ctx).percent

-- (10)
theorem observedRate_le_preC (d : Dialect) (ctx : Context) :
    observedRate d ctx ≤ observedRate d .preC := by
  cases d <;> cases ctx <;> decide

theorem observedRate_pause_lt_preV_iff (d : Dialect) :
    observedRate d .pause < observedRate d .preV ↔ d = .chicano ∨ d = .philadelphia := by
  cases d <;> decide

-- (10)
theorem observedRate_preV_lt_pause_iff (d : Dialect) :
    observedRate d .preV < observedRate d .pause ↔ d ≠ .chicano ∧ d ≠ .philadelphia := by
  cases d <;> decide

-- (7)
theorem morphRates_lt :
    ∀ r ∈ morphRates, r.regularPast < r.semiWeakPast ∧ r.semiWeakPast < r.monomorpheme := by
  decide

/-- Tejano′ trades the pre-vocalic and pre-consonantal rates of Tejano (p. 20–21). -/
def tejanoPrime : Context → ℕ
  | .preV => observedRate .tejano .preC
  | .pause => observedRate .tejano .pause
  | .preC => observedRate .tejano .preV

/-- The learning data for Tejano′ in (23) are these rates. -/
example (ctx : Context) : (tejanoPrimeRates ctx).rate.hundredths = tejanoPrime ctx := by
  cases ctx <;> decide

/-! ### The constraints of (11) -/

/-- The output retains the final t/d (*west*) or deletes it (*wes*). -/
inductive Output
  | retain
  | delete
  deriving DecidableEq, Fintype

/-- A candidate pairs the following context with the output. -/
abbrev Candidate := Context × Output

/-- \*CT penalizes a consonant cluster ending in a coronal stop. -/
def starCT : Constraint Candidate := Constraint.binary (·.2 = .retain)

/-- MAX penalizes an input consonant missing from the output. -/
def maxC : Constraint Candidate := Constraint.binary (·.2 = .delete)

/-- MAX-PRE-V penalizes a pre-vocalic input consonant missing from the output. -/
def maxPreV : Constraint Candidate := Constraint.binary fun c ↦ c.2 = .delete ∧ c.1 = .preV

/-- MAX-FINAL penalizes a phrase-final input consonant missing from the output. -/
def maxFinal : Constraint Candidate := Constraint.binary fun c ↦ c.2 = .delete ∧ c.1 = .pause

/-- The constraint set (11) lists the constraints in the paper's order. -/
def con : ConstraintSet Candidate (Fin 4) := ![starCT, maxC, maxPreV, maxFinal]

/-- The t/d deletion system lets both outputs compete in every context, under the constraint
set (11). -/
def tdDeletion : ConstraintSystem Context Output (Fin 4) := ⟨fun _ ↦ univ, con⟩

theorem tdDeletion_gen (ctx : Context) : tdDeletion.gen ctx = {.delete, .retain} := by
  cases ctx <;> decide

/-! ### Categorical systems (12) -/

/-- Ranking `σ` deletes in `ctx` if deletion is its unique optimum. -/
def Deletes (σ : Ranking (Fin 4) 4) (ctx : Context) : Prop := PicksAt tdDeletion σ ctx .delete

instance (σ : Ranking (Fin 4) 4) (ctx : Context) : Decidable (Deletes σ ctx) :=
  inferInstanceAs (Decidable (PicksAt tdDeletion σ ctx .delete))

theorem deletes_preC_iff : ∀ σ : Ranking (Fin 4) 4, Deletes σ .preC ↔ σ.Dominates 0 1 := by decide

theorem deletes_preV_iff :
    ∀ σ : Ranking (Fin 4) 4, Deletes σ .preV ↔ σ.Dominates 0 1 ∧ σ.Dominates 0 2 := by decide

theorem deletes_pause_iff :
    ∀ σ : Ranking (Fin 4) 4, Deletes σ .pause ↔ σ.Dominates 0 1 ∧ σ.Dominates 0 3 := by decide

/-- The categorical system of `σ` is the set of contexts in which it deletes. -/
def system (σ : Ranking (Fin 4) 4) : Finset Context := univ.filter (Deletes σ)

-- (12)
theorem image_system :
    univ.image system = {∅, {.pause, .preC}, {.preV, .preC}, {.preC}, univ} := by decide

theorem card_system_empty : (univ.filter (system · = ∅)).card = 12 := by decide

theorem card_system_pause_preC : (univ.filter (system · = {.pause, .preC})).card = 2 := by
  decide

theorem card_system_preV_preC : (univ.filter (system · = {.preV, .preC})).card = 2 := by
  decide

theorem card_system_preC : (univ.filter (system · = {.preC})).card = 2 := by decide

theorem card_system_univ : (univ.filter (system · = univ)).card = 6 := by decide

/-! ### Deletion probabilities ((9), (13)) -/

theorem favoring_eq (ctx : Context) : favoring con ctx .delete .retain = {0} := by
  cases ctx <;> decide

theorem active_preC : active con .preC .delete .retain = {0, 1} := by decide

theorem active_preV : active con .preV .delete .retain = {0, 1, 2} := by decide

theorem active_pause : active con .pause .delete .retain = {0, 1, 3} := by decide

/-- The grammar of row (a) of (13) has every ranking as a linear extension, and the grammars of
rows (b)–(e) the rankings that order their imposed pair as they do. -/
def extensions : ImposedRanking → Finset (Ranking (Fin 4) 4)
  | .none => univ
  | .maxPreVOverStarCT => univ.filter (·.Dominates 2 0)
  | .starCTOverMaxPreV => univ.filter (·.Dominates 0 2)
  | .maxFinalOverStarCT => univ.filter (·.Dominates 3 0)
  | .starCTOverMaxFinal => univ.filter (·.Dominates 0 3)

/-- The probability that a grammar of (13) deletes in `ctx`, the share of its linear extensions
that delete (9). -/
noncomputable def deletionProb (g : ImposedRanking) (ctx : Context) : ℝ :=
  (uniformOn (extensions g : Set (Ranking (Fin 4) 4))).real {σ | Deletes σ ctx}

-- (9)
private theorem deletionProb_eq_div {g : ImposedRanking} {ctx : Context} {q : ℝ} (k m : ℕ)
    (hk : ((extensions g).filter (Deletes · ctx)).card = k := by decide)
    (hm : (extensions g).card = m := by decide) (hq : (k : ℝ) / m = q := by norm_num) :
    deletionProb g ctx = q := by
  rw [deletionProb, uniformOn_finset_real_setOf, hk, hm, hq]

theorem deletionProb_none (ctx : Context) :
    deletionProb .none ctx = ((active con ctx .delete .retain).card : ℝ)⁻¹ := by
  rw [deletionProb, extensions, coe_univ,
    show {σ | Deletes σ ctx} = {σ | PicksAt tdDeletion σ ctx .delete} from rfl,
    uniformOn_real_picksAt_discrete_binary (tdDeletion_gen ctx) (by decide),
    show tdDeletion.con = con from rfl, favoring_eq,
    card_singleton, Nat.cast_one, one_div]

-- (13), (9)
theorem deletionProb_none_eq_pocRates (ctx : Context) :
    deletionProb .none ctx = (pocRates .none ctx).rankings / (pocRates .none ctx).total := by
  rw [deletionProb_none]
  cases ctx <;> norm_num [active_preV, active_pause, active_preC, pocRates]

-- (13)
theorem card_extensions (g : ImposedRanking) (ctx : Context) :
    (extensions g).card = (pocRates g ctx).total := by
  cases g <;> cases ctx <;> decide

theorem deletionProb_maxPreVOverStarCT :
    deletionProb .maxPreVOverStarCT .preV = 0 ∧ deletionProb .maxPreVOverStarCT .pause = 1/6 ∧
      deletionProb .maxPreVOverStarCT .preC = 1/3 :=
  ⟨deletionProb_eq_div 0 12, deletionProb_eq_div 2 12, deletionProb_eq_div 4 12⟩

theorem deletionProb_starCTOverMaxPreV :
    deletionProb .starCTOverMaxPreV .preV = 2/3 ∧ deletionProb .starCTOverMaxPreV .pause = 1/2 ∧
      deletionProb .starCTOverMaxPreV .preC = 2/3 :=
  ⟨deletionProb_eq_div 8 12, deletionProb_eq_div 6 12, deletionProb_eq_div 8 12⟩

theorem deletionProb_maxFinalOverStarCT :
    deletionProb .maxFinalOverStarCT .preV = 1/6 ∧ deletionProb .maxFinalOverStarCT .pause = 0 ∧
      deletionProb .maxFinalOverStarCT .preC = 1/3 :=
  ⟨deletionProb_eq_div 2 12, deletionProb_eq_div 0 12, deletionProb_eq_div 4 12⟩

theorem deletionProb_starCTOverMaxFinal :
    deletionProb .starCTOverMaxFinal .preV = 1/2 ∧ deletionProb .starCTOverMaxFinal .pause = 2/3 ∧
      deletionProb .starCTOverMaxFinal .preC = 2/3 :=
  ⟨deletionProb_eq_div 6 12, deletionProb_eq_div 8 12, deletionProb_eq_div 8 12⟩

/-- A printed cell of (13) is the probability (9) gives exactly in row (a) and in the two cells
where no linear extension deletes. -/
theorem deletionProb_eq_pocRates_iff (g : ImposedRanking) (ctx : Context) :
    deletionProb g ctx = (pocRates g ctx).rankings / (pocRates g ctx).total ↔
      g = .none ∨ (pocRates g ctx).rankings = 0 := by
  obtain ⟨b₁, b₂, b₃⟩ := deletionProb_maxPreVOverStarCT
  obtain ⟨c₁, c₂, c₃⟩ := deletionProb_starCTOverMaxPreV
  obtain ⟨d₁, d₂, d₃⟩ := deletionProb_maxFinalOverStarCT
  obtain ⟨e₁, e₂, e₃⟩ := deletionProb_starCTOverMaxFinal
  cases g
  · simp [deletionProb_none_eq_pocRates]
  all_goals cases ctx <;> norm_num [*, pocRates]

/-- The grammar of row (b) gives pre-consonantal deletion probability 1/3, outside the 0, .50 and 1
that §3.3 allows POC. -/
theorem deletionProb_maxPreVOverStarCT_preC_not_mem :
    deletionProb .maxPreVOverStarCT .preC ∉ ({0, 1/2, 1} : Set ℝ) := by
  rw [deletionProb_maxPreVOverStarCT.2.2]
  norm_num

-- §3.3
theorem five_le_of_real_picksAt_eq {n : ℕ} {Input Output : Type*} [DecidableEq Output]
    {S : ConstraintSystem Input Output (Fin n)}
    {r : Fin n → Fin n → Prop} [DecidableRel r] {i : Input} {o : Output}
    (h : (uniformOn (consistentTotalOrders r : Set (Ranking (Fin n) n))).real
      {σ | PicksAt S σ i o} = 1/100) : 5 ≤ n := by
  rw [uniformOn_finset_real_setOf] at h
  have ht : (consistentTotalOrders r).card ≤ n.factorial := (card_le_univ _).trans_eq (by
    rw [show Fintype.card (Ranking (Fin n) n) = Fintype.card (Equiv.Perm (Fin n)) from rfl,
      Fintype.card_perm, Fintype.card_fin])
  have h0 : (consistentTotalOrders r).card ≠ 0 := by
    rintro h0; rw [h0, Nat.cast_zero, div_zero] at h; norm_num at h
  rw [div_eq_div_iff (by exact_mod_cast h0) (by norm_num)] at h
  generalize ((consistentTotalOrders r).filter (PicksAt S · i o)).card = k at h
  generalize (consistentTotalOrders r).card = t at h ht h0
  have hkt : 100 * k = t := by exact_mod_cast (by linarith : (100 * k : ℝ) = t)
  by_contra hn
  have := Nat.factorial_le (show n ≤ 4 by omega)
  simp only [Nat.factorial, Nat.succ_eq_add_one] at this
  omega

theorem uniformOn_univ_real_picksAt_ne {Input Output : Type*} [DecidableEq Output]
    (S : ConstraintSystem Input Output (Fin 5)) (i : Input) (o : Output) :
    (uniformOn (Set.univ : Set (Ranking (Fin 5) 5))).real {σ | PicksAt S σ i o} ≠
      1/100 := by
  rw [← coe_univ, uniformOn_finset_real_setOf, card_univ, Fintype.card_perm, Fintype.card_fin]
  intro h
  rw [div_eq_div_iff (by positivity) (by norm_num)] at h
  generalize (univ.filter fun σ : Ranking (Fin 5) 5 ↦ PicksAt S σ i o).card = k at h
  norm_num [Nat.factorial] at h
  have : k * 100 = 120 := by exact_mod_cast h
  omega

/-! ### The restriction shared by POC and stochastic OT (§3.2, §4.4) -/

-- (12)
theorem deletes_preC_of_deletes {σ : Ranking (Fin 4) 4} {ctx : Context} (h : Deletes σ ctx) :
    Deletes σ .preC := by
  cases ctx
  · exact (deletes_preC_iff σ).mpr ((deletes_preV_iff σ).mp h).1
  · exact (deletes_preC_iff σ).mpr ((deletes_pause_iff σ).mp h).1
  · exact h

-- p. 11, p. 21
theorem measure_deletes_le_preC (μ : Measure (Ranking (Fin 4) 4)) (ctx : Context) :
    μ {σ | Deletes σ ctx} ≤ μ {σ | Deletes σ .preC} :=
  measure_mono fun _ ↦ deletes_preC_of_deletes

theorem not_forall_real_deletes_eq_tejanoPrime (μ : Measure (Ranking (Fin 4) 4))
    [IsFiniteMeasure μ] : ¬ ∀ ctx, μ.real {σ | Deletes σ ctx} = tejanoPrime ctx / 100 := by
  intro h
  have : μ.real {σ | Deletes σ .preV} ≤ μ.real {σ | Deletes σ .preC} :=
    measureReal_mono fun _ ↦ deletes_preC_of_deletes
  rw [h, h] at this
  norm_num [tejanoPrime, observedRate, contextRates] at this

/-! ### Harmonic Grammar (§4.2, §4.4) -/

variable {w : Fin 4 → ℝ}

@[simp] theorem harmonyScore_retain (ctx : Context) :
    harmonyScore con w (ctx, .retain) = -w 0 := by
  cases ctx <;> simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV,
    maxFinal]

@[simp] theorem harmonyScore_delete_preV :
    harmonyScore con w (.preV, .delete) = -(w 1 + w 2) := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

@[simp] theorem harmonyScore_delete_pause :
    harmonyScore con w (.pause, .delete) = -(w 1 + w 3) := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

@[simp] theorem harmonyScore_delete_preC :
    harmonyScore con w (.preC, .delete) = -w 1 := by
  simp [harmonyScore_eq_neg_sum, Fin.sum_univ_four, con, starCT, maxC, maxPreV, maxFinal]

/-- Deletion in `ctx` has greater harmony than retention under weights `w` ((16)–(17)). -/
def HGDeletes (w : Fin 4 → ℝ) (ctx : Context) : Prop :=
  harmonyDominates con w (ctx, .delete) (ctx, .retain)

@[simp] theorem hgDeletes_preC_iff : HGDeletes w .preC ↔ w 1 < w 0 := by
  simp [HGDeletes]

@[simp] theorem hgDeletes_preV_iff : HGDeletes w .preV ↔ w 1 + w 2 < w 0 := by
  simp [HGDeletes]

@[simp] theorem hgDeletes_pause_iff : HGDeletes w .pause ↔ w 1 + w 3 < w 0 := by
  simp [HGDeletes]

/-- Tableau (17) weights \*CT 2 over MAX 1, and deletion wins pre-consonantally. -/
example : HGDeletes ![2, 1, 0, 0] .preC := by simp

theorem hgDeletes_preC_of_hgDeletes (hw : 0 ≤ w) {ctx : Context} (h : HGDeletes w ctx) :
    HGDeletes w .preC := by
  rw [hgDeletes_preC_iff]
  cases ctx
  · rw [hgDeletes_preV_iff] at h; linarith [show 0 ≤ w 2 from hw 2]
  · rw [hgDeletes_pause_iff] at h; linarith [show 0 ≤ w 3 from hw 3]
  · rwa [hgDeletes_preC_iff] at h

-- (12)
theorem image_system_eq_filter :
    univ.image system = univ.filter fun S : Finset Context ↦ S.Nonempty → .preC ∈ S := by
  rw [image_system]
  decide

-- (12), footnote 8
theorem setOf_hgDeletes_eq :
    {S : Finset Context | ∃ w : Fin 4 → ℝ, 0 ≤ w ∧ ∀ ctx, HGDeletes w ctx ↔ ctx ∈ S} =
      ↑(univ.image system) := by
  ext S
  rw [image_system_eq_filter, coe_filter, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hS⟩ ⟨ctx, hctx⟩
    exact (hS _).mp (hgDeletes_preC_of_hgDeletes hw ((hS ctx).mpr hctx))
  · intro hS
    let protect (ctx : Context) : ℝ := if ctx ∈ S then 0 else 1
    refine ⟨![1, protect .preC, protect .preV, protect .pause], fun i ↦ ?_, fun ctx ↦ ?_⟩
    · fin_cases i <;> simp [protect] <;> split_ifs <;> norm_num
    · by_cases h : ctx ∈ S
      · cases ctx <;> simp [protect, h, hS ⟨_, h⟩]
      · cases ctx <;> simp [protect, h] <;> linarith [show (0 : ℝ) ≤ protect .preC by
          unfold protect; split_ifs <;> norm_num]

-- p. 19
theorem weightNoise_hgDeletes_le_preC (w : Fin 4 → ℝ) (v : ℝ≥0) (ctx : Context) :
    weightNoise (Fin 4) v {η | HGDeletes (w + η)⁺ ctx} ≤
      weightNoise (Fin 4) v {η | HGDeletes (w + η)⁺ .preC} :=
  measure_mono fun _ ↦ hgDeletes_preC_of_hgDeletes (posPart_nonneg _)

-- §4.4
theorem hgDeletes_neg (ctx : Context) : HGDeletes ![0, 0, -1, 0] ctx ↔ ctx = .preV := by
  cases ctx <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]

-- (12)
theorem singleton_preV_not_mem : {Context.preV} ∉ univ.image system := by decide

/-! ### MaxEnt Harmonic Grammar (§4.3–4.4) -/

instance : MeasurableSpace Output := ⊤
instance : MeasurableSingletonClass Output := ⟨fun _ ↦ trivial⟩

/-- The MaxEnt deletion probability in `ctx`, the probability of the deletion output under the
MaxEnt distribution of the context's two outputs. -/
noncomputable def maxEntProb (w : Fin 4 → ℝ) (ctx : Context) : ℝ :=
  (maxEnt (con.comap (ctx, ·)).violations w).real {.delete}

theorem maxEntProb_eq_sigmoid (w : Fin 4 → ℝ) (ctx : Context) :
    maxEntProb w ctx =
      sigmoid (harmonyScore con w (ctx, .delete) - harmonyScore con w (ctx, .retain)) :=
  maxEnt_real_singleton_of_pair _ _ (a := Output.delete) (b := .retain) (by decide) (by decide)

-- §4.4
theorem maxEntProb_le_preC (hw : 0 ≤ w) (ctx : Context) :
    maxEntProb w ctx ≤ maxEntProb w .preC := by
  rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_le_iff]
  cases ctx <;> simp <;> linarith [show 0 ≤ w 2 from hw 2, show 0 ≤ w 3 from hw 3]

theorem maxEntProb_preV_lt_pause_iff (w : Fin 4 → ℝ) :
    maxEntProb w .preV < maxEntProb w .pause ↔ w 3 < w 2 := by
  rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]
  simp

-- (23), p. 20
theorem learnedGrammars_maxFinal_lt_maxPreV_iff (d : Dialect) (m : Model) :
    (learnedGrammars d m).maxFinal.toRat < (learnedGrammars d m).maxPreV.toRat ↔
      observedRate d .preV < observedRate d .pause := by
  cases d <;> cases m <;> decide +kernel

/-- The MaxEnt weights of dialect `d` in (23), in the order of (11). -/
noncomputable def meWeights (d : Dialect) : Fin 4 → ℝ :=
  let g := learnedGrammars d .meHG
  ![g.starCT.toRat, g.maxC.toRat, g.maxPreV.toRat, g.maxFinal.toRat]

-- (23)
theorem maxEntProb_meWeights_lt_iff (d : Dialect) (ctx ctx' : Context) :
    maxEntProb (meWeights d) ctx < maxEntProb (meWeights d) ctx' ↔
      observedRate d ctx < observedRate d ctx' := by
  rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]
  cases d <;> cases ctx <;> cases ctx' <;>
    norm_num [meWeights, learnedGrammars, Decimal.toRat, observedRate, contextRates]

/-- The MaxEnt weights of Tejano′ in (23), with negative contextual faithfulness. -/
noncomputable def tejanoPrimeWeights : Fin 4 → ℝ :=
  let g := tejanoPrimeGrammars .meHG
  ![g.starCT.toRat, g.maxC.toRat, g.maxPreV.toRat, g.maxFinal.toRat]

-- §4.4
theorem maxEntProb_tejanoPrimeWeights_lt_iff (ctx ctx' : Context) :
    maxEntProb tejanoPrimeWeights ctx < maxEntProb tejanoPrimeWeights ctx' ↔
      tejanoPrime ctx < tejanoPrime ctx' := by
  rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]
  cases ctx <;> cases ctx' <;>
    norm_num [tejanoPrimeWeights, tejanoPrimeGrammars, Decimal.toRat, tejanoPrime, observedRate,
      contextRates]

/-- The stochastic OT and Noisy HG learners of (23) leave Tejano′ with equal rates in all three
contexts. -/
example (m : Model) (hm : m ≠ .meHG) :
    (tejanoPrimeGrammars m).preV = (tejanoPrimeGrammars m).pause ∧
      (tejanoPrimeGrammars m).pause = (tejanoPrimeGrammars m).preC := by
  cases m <;> simp_all [tejanoPrimeGrammars]

/-! ### Cumulativity: Japanese loanword devoicing ((18)–(22)) -/

/-- A loanword keeps its voiced obstruents or devoices the geminate. -/
inductive Voicing
  | voiced
  | devoiced
  deriving DecidableEq, Fintype

instance : MeasurableSpace Voicing := ⊤
instance : MeasurableSingletonClass Voicing := ⟨fun _ ↦ trivial⟩

/-- IDENT-VOICE is violated by the devoiced output. -/
def identVoice : Constraint (Loan × Voicing) := Constraint.binary (·.2 = .devoiced)

/-- OCP-VOICE is violated by two voiced obstruents in one root, in faithful *bobu* and *guddo*. -/
def ocpVoice : Constraint (Loan × Voicing) :=
  Constraint.binary fun x ↦ x.2 = .voiced ∧ x.1 ≠ .webbu

/-- \*VOICED-GEMINATE is violated by a voiced geminate, in faithful *webbu* and *guddo*. -/
def voicedGeminate : Constraint (Loan × Voicing) :=
  Constraint.binary fun x ↦ x.2 = .voiced ∧ x.1 ≠ .bobu

/-- The tableaux (18)–(19) form a realization problem over IDENT-VOICE, OCP-VOICE and
\*VOICED-GEMINATE, after Itô and Mester and Kawahara, in which only *guddo* devoices. -/
def loanwordDevoicing : RealizationProblem Loan Voicing (Fin 3) where
  inputs := univ
  gen _ := univ
  con := ![identVoice, ocpVoice, voicedGeminate]
  target
    | .guddo => .devoiced
    | _ => .voiced
  target_mem _ _ := mem_univ _

-- (18), (19)
theorem loanwordDevoicing_realizedByWeighting :
    loanwordDevoicing.realizedByWeighting ![3/2, 1, 1] := by
  refine fun i _ ↦ Finset.argmax_eq_singleton_iff.2 ⟨mem_univ _, fun o _ hne ↦ ?_⟩
  cases i <;> cases o <;>
    simp [loanwordDevoicing, harmonyScore, dotProduct, Fin.sum_univ_three, identVoice, ocpVoice,
      voicedGeminate] at hne ⊢ <;> norm_num

theorem loanwordDevoicing_not_isOTRealizable : ¬ loanwordDevoicing.IsOTRealizable := by decide

/-- Ranking `σ` devoices loanword `l`. -/
def Devoices (σ : Ranking (Fin 3) 3) (l : Loan) : Prop :=
  PicksAt loanwordDevoicing.toConstraintSystem σ l .devoiced

-- p. 18
theorem setOf_devoices_guddo :
    {σ | Devoices σ .guddo} = {σ | Devoices σ .bobu} ∪ {σ | Devoices σ .webbu} := by
  ext σ
  revert σ
  unfold Devoices
  decide

-- (21), p. 18
theorem measure_devoices_guddo_le (μ : Measure (Ranking (Fin 3) 3)) :
    μ {σ | Devoices σ .guddo} ≤ μ {σ | Devoices σ .bobu} + μ {σ | Devoices σ .webbu} := by
  rw [setOf_devoices_guddo]
  exact measure_union_le _ _

/-- The learning data of (21) break that bound, and the stochastic OT grammar learned from them
keeps it. -/
example : (devoicingRates .bobu).learningData.toRat + (devoicingRates .webbu).learningData.toRat <
      (devoicingRates .guddo).learningData.toRat ∧
    (devoicingRates .guddo).stOT.toRat ≤
      (devoicingRates .bobu).stOT.toRat + (devoicingRates .webbu).stOT.toRat := by
  decide +kernel

-- p. 18
theorem weightNoiseChoiceProb_guddo (w : Fin 3 → ℝ) (hw : w 0 = w 1 + w 2) (v : ℝ≥0)
    (hv : v ≠ 0) :
    weightNoiseChoiceProb (fun k o ↦ loanwordDevoicing.con k (.guddo, o)) w v .devoiced =
      2⁻¹ := by
  rw [weightNoiseChoiceProb_of_forall_ne_eq _ _ _ hv (b := .voiced)
    (fun c hc ↦ by cases c <;> simp_all) (by decide) fun h ↦ by
      simpa [ConstraintSet.violationDiff, loanwordDevoicing, identVoice] using congrFun h 0]
  have : harmonyScore (fun k o ↦ loanwordDevoicing.con k (.guddo, o)) w .devoiced -
      harmonyScore (fun k o ↦ loanwordDevoicing.con k (.guddo, o)) w .voiced = 0 := by
    simp [harmonyScore_eq_neg_sum, Fin.sum_univ_three, loanwordDevoicing, identVoice, ocpVoice,
      voicedGeminate, hw]
  rw [this, zero_div, normalCDF_zero, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- The Noisy HG grammar of (21) weighs IDENT-VOICE as OCP-VOICE and \*VOICED-GEMINATE
together. -/
example : ∀ g ∈ loanwordWeights, g.model = .nHG →
    g.identVoice.toRat = g.ocpVoice.toRat + g.voicedGeminate.toRat := by
  decide +kernel

-- (22)
theorem guddo_maxEnt_half (o : Voicing) :
    (maxEnt (loanwordDevoicing.con.comap (.guddo, ·)).violations ![2, 1, 1]).real {o} = 2⁻¹ := by
  have h : harmonyScore (loanwordDevoicing.con.comap (.guddo, ·)) ![2, 1, 1] =
      fun _ ↦ (-2 : ℝ) := by
    funext o
    cases o <;> norm_num [loanwordDevoicing, harmonyScore, dotProduct, Fin.sum_univ_three,
      identVoice, ocpVoice, voicedGeminate]
  rw [maxEnt_real_singleton, harmony_violations, h]
  simp [show Fintype.card Voicing = 2 from rfl]

/-! ### Variable rules (§4.5) -/

/-- Cedergren and Sankoff's variable-rule probability (24) combines the input probability and
one factor weight for each contextual factor present, all as factors `p`. -/
noncomputable def variableRule {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  (∏ i, p i) / ((∏ i, p i) + ∏ i, (1 - p i))

-- p. 21–22
theorem variableRule_eq_sigmoid {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Ioo 0 1) :
    variableRule p = sigmoid (∑ i, logit (p i)) := by
  have hpos : 0 < ∏ i, p i := prod_pos fun i _ ↦ (hp i).1
  have hexp : exp (-∑ i, logit (p i)) = (∏ i, (1 - p i)) / ∏ i, p i := by
    rw [← sum_neg_distrib, exp_sum, ← prod_div_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [logit, ← log_inv, exp_log (inv_pos.mpr (div_pos (hp i).1 (sub_pos.mpr (hp i).2))),
      inv_div]
  rw [variableRule, sigmoid_def, hexp, one_add_div hpos.ne', inv_div]

/-- Goldvarb's Tejano weights in (25), input .44 and pre-vocalic factor .30, give 33/131, about
.25 ((26)). -/
example : variableRule ![((goldvarbInputs .tejano).p0.toRat : ℝ),
    (goldvarbFactors .tejano .preV).factorWeight.toRat] = 33/131 := by
  norm_num [variableRule, Fin.prod_univ_two, goldvarbInputs, goldvarbFactors, Decimal.toRat]

/-- An informal-register factor .70 raises the pre-vocalic rate to .44 ((27)). -/
example : variableRule ![((goldvarbInputs .tejano).p0.toRat : ℝ),
    (goldvarbFactors .tejano .preV).factorWeight.toRat, informalRegisterFactor.toRat] =
      44/100 := by
  norm_num [variableRule, Fin.prod_univ_succ, goldvarbInputs, goldvarbFactors,
    informalRegisterFactor, Decimal.toRat]

-- (25)
theorem exists_variableRule_eq (q : Context → ℝ) :
    ∃ p₀ : ℝ, ∃ p : Context → ℝ, ∀ ctx, variableRule ![p₀, p ctx] = q ctx := by
  refine ⟨2⁻¹, q, fun ctx ↦ ?_⟩
  rw [variableRule, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show 2⁻¹ * q ctx + (1 - 2⁻¹) * (1 - q ctx) = (2⁻¹ : ℝ) by ring, div_eq_iff (by norm_num)]
  ring

-- p. 24–25
theorem variableRule_lt_iff {p₀ c c' s : ℝ} (h₀ : p₀ ∈ Set.Ioo 0 1) (hc : c ∈ Set.Ioo 0 1)
    (hc' : c' ∈ Set.Ioo 0 1) (hs : s ∈ Set.Ioo 0 1) :
    variableRule ![p₀, c, s] < variableRule ![p₀, c', s] ↔ c < c' := by
  rw [variableRule_eq_sigmoid _ fun i ↦ by fin_cases i <;> assumption,
    variableRule_eq_sigmoid _ fun i ↦ by fin_cases i <;> assumption, sigmoid_lt_iff,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, add_lt_add_iff_right,
    add_lt_add_iff_left]
  rw [← sigmoid_lt_iff, sigmoid_logit hc, sigmoid_logit hc']

-- (28), p. 25
theorem exists_styleSensitive_reorders :
    ∃ w sens : Fin 4 → ℝ, sens 2 = 0 ∧
      maxEntProb (w + (0 : ℝ) • sens) .preV < maxEntProb (w + (0 : ℝ) • sens) .pause ∧
      maxEntProb (w + (1 : ℝ) • sens) .pause < maxEntProb (w + (1 : ℝ) • sens) .preV := by
  refine ⟨![0, 0, 1, 0], ![0, 0, 0, 2], rfl, ?_, ?_⟩
  · rw [maxEntProb_preV_lt_pause_iff]; norm_num
  · rw [maxEntProb_eq_sigmoid, maxEntProb_eq_sigmoid, sigmoid_lt_iff]; simp

/-! ### Lexically indexed faithfulness ((32)) -/

/-- A constraint indexed to word `l` assigns its violations to the candidates of `l` alone. -/
def indexed (l : Lexeme) (c : Constraint Candidate) : Constraint (Lexeme × Candidate) :=
  fun x ↦ if x.1 = l then c x.2 else 0

/-- The constraints of (32) are those of (11) with each faithfulness constraint indexed to each
word, `none` being \*CT and `some (l, k)` the faithfulness constraint `con k.succ` indexed to
`l`. -/
def indexedCon : ConstraintSet (Lexeme × Candidate) (Option (Lexeme × Fin 3))
  | none => (con 0).comap Prod.snd
  | some (l, k) => indexed l (con k.succ)

/-- The weights of (32). -/
noncomputable def indexedWeights : Option (Lexeme × Fin 3) → ℝ
  | none => indexedStarCT.toRat
  | some (.feast, k) => (![indexedMaxFeast, indexedMaxPreVFeast, indexedMaxFinalFeast] k).toRat
  | some (.most, k) => (![indexedMaxMost, indexedMaxPreVMost, indexedMaxFinalMost] k).toRat

/-- The tableau of word `l` before `ctx` under the constraints of (32). -/
def indexedTableau (l : Lexeme) (ctx : Context) : ConstraintSet Output (Option (Lexeme × Fin 3)) :=
  fun k o ↦ indexedCon k (l, ctx, o)

/-- The permutation `exchange` swaps the two words in the indices of (32). -/
def exchange : Option (Lexeme × Fin 3) ≃ Option (Lexeme × Fin 3) :=
  Equiv.optionCongr ((Equiv.swap Lexeme.feast .most).prodCongr (Equiv.refl _))

theorem indexedTableau_most (ctx : Context) :
    indexedTableau .most ctx = fun k ↦ indexedTableau .feast ctx (exchange k) := by
  funext k o
  rcases k with _ | ⟨_ | _, k⟩ <;> rfl

-- p. 29
theorem weightNoiseChoiceProb_feast_lt_most {w : Option (Lexeme × Fin 3) → ℝ}
    (hw : ∀ k, w (some (.most, k)) < w (some (.feast, k))) {v : ℝ≥0} (hv : v ≠ 0)
    (ctx : Context) :
    weightNoiseChoiceProb (indexedTableau .feast ctx) w v .delete <
      weightNoiseChoiceProb (indexedTableau .most ctx) w v .delete := by
  set d := (indexedTableau .feast ctx).violationDiff (R := ℝ) .delete .retain
  have hd : d ≠ 0 := fun h ↦ by simpa [d, ConstraintSet.violationDiff, indexedTableau,
    indexedCon, con, starCT] using congrFun h none
  have hmost : (indexedTableau .most ctx).violationDiff (R := ℝ) .delete .retain = d ∘ exchange :=
    by rw [indexedTableau_most]; rfl
  have hb (c : Output) (hc : c ≠ .delete) : c = .retain := by cases c <;> simp_all
  rw [weightNoiseChoiceProb_of_forall_ne_eq _ _ _ hv hb (by decide) hd,
    weightNoiseChoiceProb_of_forall_ne_eq _ _ _ hv hb (by decide)
      (by
        rw [hmost]
        exact fun h ↦ hd (funext fun k ↦ by simpa using congrFun h (exchange.symm k))),
    ENNReal.ofReal_lt_ofReal_iff (normalCDF_pos _), harmonyScore_sub,
    harmonyScore_sub, hmost, show d ∘ exchange ⬝ᵥ d ∘ exchange = d ⬝ᵥ d from
      exchange.sum_comp fun k ↦ d k * d k]
  refine normalCDF_strictMono (div_lt_div_of_pos_right ?_ (Real.sqrt_pos.mpr (mul_pos
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)) ((Finset.sum_nonneg fun k _ ↦
      mul_self_nonneg (d k)).lt_of_ne (Ne.symm (mt dotProduct_self_eq_zero.mp hd))))))
  rw [neg_lt_neg_iff, show w ⬝ᵥ d ∘ exchange = ∑ k, w (exchange.symm k) * d k by
    rw [dotProduct, ← exchange.symm.sum_comp]; simp]
  have hf (j : Fin 3) : 0 ≤ d (some (.feast, j)) := by
    have : ∀ (c : Context) (k : Fin 3), con k.succ (c, .retain) = 0 := by decide
    simp [d, ConstraintSet.violationDiff, indexedTableau, indexedCon, indexed, this]
  refine Finset.sum_lt_sum (fun k _ ↦ ?_) ⟨some (.feast, 0), mem_univ _, ?_⟩
  · rcases k with _ | ⟨_ | _, j⟩
    · rfl
    · exact mul_le_mul_of_nonneg_right (hw j).le (hf j)
    · simp [d, ConstraintSet.violationDiff, indexedTableau, indexedCon, indexed]
  · rw [show exchange.symm (some (.feast, 0)) = some (.most, 0) from rfl]
    simpa [d, ConstraintSet.violationDiff, indexedTableau, indexedCon, indexed, con, maxC]
      using hw 0

-- (32)
theorem weightNoiseChoiceProb_indexedWeights {v : ℝ≥0} (hv : v ≠ 0) (ctx : Context) :
    weightNoiseChoiceProb (indexedTableau .feast ctx) indexedWeights v .delete <
      weightNoiseChoiceProb (indexedTableau .most ctx) indexedWeights v .delete :=
  weightNoiseChoiceProb_feast_lt_most (fun k ↦ by
    fin_cases k <;> norm_num [indexedWeights, indexedMaxFeast, indexedMaxMost,
      indexedMaxPreVFeast, indexedMaxPreVMost, indexedMaxFinalFeast, indexedMaxFinalMost,
      Decimal.toRat]) hv ctx

/-- The learned grammar of (32) deletes less from *feast* than from *most* in every context. -/
example (ctx : Context) :
    (indexedRates .feast ctx).learned.toRat < (indexedRates .most ctx).learned.toRat := by
  cases ctx <;> decide +kernel

end CoetzeePater2011
