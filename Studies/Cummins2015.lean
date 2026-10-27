module

public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Dist

/-!
# Cummins (2015): Constraints on numerical expressions

Cummins models the choice of a numerically quantified expression as classical Optimality
Theory. Six violable constraints, informativeness, granularity, quantifier simplicity,
numeral salience, numeral priming and quantifier priming, evaluate the candidate expressions
against the speaker's knowledge and the preceding context, and a speaker's total ranking
selects one, so that apparent variation is variation across rankings and contexts. Round
numerals are salient by Jansen and Pollmann's k-ness, a candidate incurring a subset of a
rival's violations is preferred under every ranking, and a hearer who presumes the utterance
optimal infers that an alternative bounding it in this way was not available to the speaker:
*more than n* implicates *not more than m* for any greater *m* at least as salient and at the
same granularity level, unless *n* was primed.

We derive the constraints' violations from the numeral and the context, reproduce the book's
toy and correction tableaux from them and its approximation tableaux from their printed
marks, and prove the bounding implicature and the exact condition for its attenuation under
priming for arbitrary numerals.

## Implementation notes

* Numeral salience uses the book's k-ness with a zero exponent admitted, under which 20 and
  100 are entirely round. The book prints 50 as satisfying salience, though by its
  definition 50 lacks 2-ness, which changes no comparison in its tableaux.
* Quantifier simplicity follows the book's simplifying assumption that a comparative incurs
  no violation and a superlative one; *exactly* and *about* incur one, as its tableaux print.
* Informativeness reads a comparative or superlative against its own bound, the book's bound
  under discussion, and the other forms at their numeral. The informativeness marks of the
  approximation tableaux, which the book says do not follow from its definition, are entered
  as printed, a parenthesized star counting as one, with entire roundness as the criterion
  for the ambiguity mark that fits them.
* The book assigns no numeric granularity levels to cardinals; `granularityLevel` counts
  trailing zeros, and an unset level is met by every numeral, as the book allows.

## References

* [C. Cummins, *Constraints on numerical expressions* (2015)][cummins-2015]
* [A. Prince, P. Smolensky, *Optimality Theory: constraint interaction in generative
  grammar* (1993)][prince-smolensky-1993]
* [C. J. M. Jansen, M. M. W. Pollmann, *On round numbers: pragmatic aspects of numerical
  expressions* (2001)][jansen-pollmann-2001]
* [M. Krifka, *Approximate interpretations of number words: a case for strategic
  communication* (2009)][krifka-2009b]
* [C. Cummins, U. Sauerland, S. Solt, *Granularity and scalar implicature in numerical
  expressions* (2012)][cummins-sauerland-solt-2012]
-/

@[expose] public section

namespace Cummins2015

open OptimalityTheory Numerals.Roundness

/-! ### Numeral salience (§2.4.4) -/

/-- The roundness of a numeral counts the kinds of k-ness, 10-, 5-, 2- and 2½-ness, it exhibits,
the zero exponent admitted (definition (13)). -/
def roundness (n : ℕ) : ℕ := score (Kness.Holds 0) n

theorem roundness_le_four (n : ℕ) : roundness n ≤ 4 := score_le_card n

/-- An entirely round numeral exhibits every kind of k-ness. -/
def EntirelyRound (n : ℕ) : Prop := roundness n = 4

instance : DecidablePred EntirelyRound := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### Candidates, contexts and the six constraints (§2.4) -/

/-- The quantifier of a candidate expression. -/
inductive Form where
  | bare
  | exactly
  | about
  | moreThan
  | atLeast
  | fewerThan
  | atMost
  deriving DecidableEq

/-- The bare numeral and the comparatives are simplest, the other modifiers and the superlatives
one degree more complex (§2.4.3, §4.9). -/
def Form.complexity : Form → ℕ
  | .bare | .moreThan | .fewerThan => 0
  | .exactly | .about | .atLeast | .atMost => 1

/-- A candidate expression applies a quantifier to a numeral. -/
structure Candidate where
  /-- The quantifier. -/
  form : Form
  /-- The numeral. -/
  numeral : ℕ
  deriving DecidableEq

/-- The context of utterance records the bounds of the value under discussion the speaker knows,
the granularity level the context sets, if any, and the primed numeral and quantifier. -/
structure Context where
  /-- The lower bound the speaker knows. -/
  lo : Option ℕ := none
  /-- The upper bound the speaker knows. -/
  hi : Option ℕ := none
  /-- The granularity level the context sets. -/
  granularity : Option ℕ := none
  /-- The numeral activated in the prior context. -/
  primedNumeral : Option ℕ := none
  /-- The quantifier activated in the prior context. -/
  primedForm : Option Form := none

/-- Informativeness assigns one violation for each value the expression admits that the speaker's
knowledge excludes (constraint 1). A comparative or superlative puts its own bound under
discussion; the other forms are read at their numeral. -/
def info (ctx : Context) : Constraint Candidate := fun c ↦
  match c.form, ctx.lo, ctx.hi with
  | .moreThan, some lo, _ => lo - (c.numeral + 1)
  | .atLeast, some lo, _ => lo - c.numeral
  | .fewerThan, _, some hi => c.numeral - (hi + 1)
  | .atMost, _, some hi => c.numeral - hi
  | .moreThan, none, _ | .atLeast, none, _ | .fewerThan, _, none | .atMost, _, none => 0
  | _, lo, hi => if (∀ l ∈ lo, l ≤ c.numeral) ∧ ∀ h ∈ hi, c.numeral ≤ h then 0 else 1

/-- *more than n*. -/
def moreThan (n : ℕ) : Candidate := ⟨.moreThan, n⟩

/-- The bare numeral. -/
def bare (n : ℕ) : Candidate := ⟨.bare, n⟩

/-- *exactly n*. -/
def exactly (n : ℕ) : Candidate := ⟨.exactly, n⟩

/-- *about n*. -/
def about (n : ℕ) : Candidate := ⟨.about, n⟩

/-- Quantifier simplicity assigns one violation per degree of complexity (constraint 3). -/
def qsimp : Constraint Candidate := fun c ↦ c.form.complexity

/-- Numeral salience assigns one violation for each kind of k-ness the numeral lacks
(constraint 4). -/
def nsal : Constraint Candidate := fun c ↦ 4 - roundness c.numeral

example : nsal (bare 20) = 0 := by decide
example : nsal (bare 40) = 1 := by decide
example : nsal (bare 30) = 2 := by decide
example : nsal (bare 12) = 3 := by decide
example : nsal (bare 17) = 4 := by decide

/-- The decimal granularity level of a numeral counts its trailing zeros, up to thousands. -/
def granularityLevel (n : ℕ) : ℕ :=
  if n = 0 then 0 else if 1000 ∣ n then 3 else if 100 ∣ n then 2 else if 10 ∣ n then 1 else 0

theorem pow_granularityLevel_eq_scaleLcm {n : ℕ} (hn : n ≠ 0) :
    (10 : ℤ) ^ granularityLevel n = scaleLcm {1000, 100, 10, 1} (n : ℤ) := by
  symm
  unfold granularityLevel
  split_ifs with h0 h3 h2 h1
  · exact absurd h0 hn
  · refine scaleLcm_eq_of_aligned (by decide) (by decide) (m := 10 ^ 3) (by decide)
      (by exact_mod_cast h3) fun w hw hwn ↦ ?_
    fin_cases hw <;> norm_num
  · refine scaleLcm_eq_of_aligned (by decide) (by decide) (m := 10 ^ 2) (by decide)
      (by exact_mod_cast h2) fun w hw hwn ↦ ?_
    fin_cases hw
    · exact absurd (by exact_mod_cast hwn) h3
    all_goals norm_num
  · refine scaleLcm_eq_of_aligned (by decide) (by decide) (m := 10 ^ 1) (by decide)
      (by exact_mod_cast h1) fun w hw hwn ↦ ?_
    fin_cases hw
    · exact absurd (by exact_mod_cast hwn) h3
    · exact absurd (by exact_mod_cast hwn) h2
    all_goals norm_num
  · refine scaleLcm_eq_of_aligned (by decide) (by decide) (m := 10 ^ 0) (by norm_num)
      (by norm_num) fun w hw hwn ↦ ?_
    fin_cases hw
    · exact absurd (by exact_mod_cast hwn) h3
    · exact absurd (by exact_mod_cast hwn) h2
    · exact absurd (by exact_mod_cast hwn) h1
    · norm_num

/-- Granularity assigns one violation per level of mismatch with the level the context sets, an
unset level being met by every numeral (constraint 2). -/
def gran (ctx : Context) : Constraint Candidate := fun c ↦
  ctx.granularity.elim 0 (Nat.dist (granularityLevel c.numeral))

/-- Numeral priming assigns a violation when a numeral is primed and another is used
(constraint 5). -/
def npri (ctx : Context) : Constraint Candidate := fun c ↦
  match ctx.primedNumeral with
  | some p => if c.numeral = p then 0 else 1
  | none => 0

/-- Quantifier priming assigns a violation when a quantifier is primed and another is used
(constraint 6). -/
def qpri (ctx : Context) : Constraint Candidate := fun c ↦
  match ctx.primedForm with
  | some f => if c.form = f then 0 else 1
  | none => 0

/-- The six constraints, in the book's order, are informativeness, granularity, quantifier
simplicity, numeral salience, numeral priming and quantifier priming. -/
def con (ctx : Context) : ConstraintSet Candidate (Fin 6) :=
  ![info ctx, gran ctx, qsimp, nsal, npri ctx, qpri ctx]

/-! ### Constraint interaction in the toy system (§3.1, Tables 3.1–3.3) -/

/-- The toy system ranks informativeness, numeral salience and numeral priming. -/
def toy (ctx : Context) : ConstraintSet Candidate (Fin 3) := ![info ctx, nsal, npri ctx]

/-- The speaker knows the value to be at least 22. -/
def atLeast22 : Context := { lo := some 22 }

/-- The same, with 21 contextually salient. -/
def atLeast22Primed : Context := { atLeast22 with primedNumeral := some 21 }

-- Table 3.1, Table 3.3
theorem atLeast22_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (toy atLeast22) r {moreThan 21, moreThan 20}).optimal =
      if r.Dominates 0 1 then {moreThan 21} else {moreThan 20} := by
  revert r; decide

-- Table 3.2, Table 3.3
theorem atLeast22Primed_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (toy atLeast22Primed) r {moreThan 21, moreThan 20}).optimal =
      if r.Dominates 1 0 ∧ r.Dominates 1 2 then {moreThan 20} else {moreThan 21} := by
  revert r; decide

/-- Priming over salience over informativeness, the last ranking of Table 3.3. -/
def primingFirst : Ranking (Fin 3) 3 := Equiv.swap 0 2

theorem primingFirst_optimal :
    (Tableau.ofRanking (toy atLeast22) primingFirst {moreThan 21, moreThan 20}).optimal =
        {moreThan 20} ∧
      (Tableau.ofRanking (toy atLeast22Primed) primingFirst {moreThan 21, moreThan 20}).optimal =
        {moreThan 21} := by
  decide

/-! ### Approximation (§3.3.1, Tables 3.4–3.8) -/

/-- The value the speaker means to convey, exact or approximate. -/
inductive Situation where
  /-- Exactly `n`. -/
  | exact (n : ℕ)
  /-- Approximately `n`. -/
  | about (n : ℕ)

/-- Informativeness as the approximation tableaux read it is violated once by an expression whose
quantifier or numeral misfits the value, and once more by a bare entirely round numeral,
ambiguous between precise and approximate readings. The book prints the ambiguity mark for
*100* and not for *50*; entire roundness is the criterion that fits. -/
def Situation.info : Situation → Constraint Candidate
  | .exact n => fun c ↦ (if c.form = .about ∨ c.numeral ≠ n then 1 else 0) +
      (if c.form = .bare ∧ EntirelyRound c.numeral then 1 else 0)
  | .about n => fun c ↦ (if c.form = .exactly ∨ c.numeral ≠ n then 1 else 0) +
      (if c.form = .bare ∧ EntirelyRound c.numeral then 1 else 0)

/-- The approximation system ranks informativeness, numeral salience and quantifier
simplicity. -/
def approx (s : Situation) : ConstraintSet Candidate (Fin 3) := ![s.info, nsal, qsimp]

-- Table 3.4
theorem bare_notMem_optimal_of_roundness_lt {n m : ℕ} (hmn : roundness m < roundness n)
    (r : Ranking (Fin 3) 3) {cands : Finset Candidate} (hc : bare n ∈ cands) :
    bare m ∉ (Tableau.ofRanking (approx (.exact n)) r cands).optimal := by
  have hne : m ≠ n := ne_of_apply_ne roundness hmn.ne
  refine Tableau.ofRanking_notMem_optimal_of_lt hc (Pi.lt_def.2 ⟨fun i ↦ ?_, 1, ?_⟩)
  · match i with
    | 0 =>
      show (Situation.exact n).info (bare n) ≤ (Situation.exact n).info (bare m)
      simp only [Situation.info, bare, reduceCtorEq, false_or, true_and, hne, ne_eq,
        not_true_eq_false, not_false_eq_true, ite_true, ite_false]
      split_ifs <;> omega
    | 1 => show 4 - roundness n ≤ 4 - roundness m; omega
    | 2 => exact le_rfl
  · show 4 - roundness n < 4 - roundness m
    have := roundness_le_four n; omega

-- Table 3.5
theorem exact51_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (approx (.exact 51)) r {bare 50, bare 51}).optimal =
      if r.Dominates 0 1 then {bare 51} else {bare 50} := by
  revert r; decide

-- Table 3.6
theorem exact100_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (approx (.exact 100)) r {bare 100, exactly 100, about 100, about 99}).optimal
      = if r.Dominates 0 2 then {exactly 100} else {bare 100} := by
  revert r; decide

-- Table 3.7
theorem about100_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (approx (.about 100)) r {bare 100, about 100}).optimal =
      if r.Dominates 0 2 then {about 100} else {bare 100} := by
  revert r; decide

-- Table 3.8
theorem exact99_optimal (r : Ranking (Fin 3) 3) :
    (Tableau.ofRanking (approx (.exact 99)) r {bare 99, exactly 99, bare 100, about 100}).optimal
      = if r.Dominates 0 1 then {bare 99}
        else if r.Dominates 2 0 then {bare 100} else {about 100} := by
  revert r; decide

/-! ### Corrections (§3.3.2, Tables 3.9–3.10) -/

/-- The four maximally informative corrections to a description of boxes holding `n` or
`n + 1` items ((38)–(41)). -/
inductive Correction where
  /-- *more than n − 1*. -/
  | moreThan
  /-- *at least n*. -/
  | atLeast
  /-- *at most n + 1*. -/
  | atMost
  /-- *fewer than n + 2*. -/
  | fewerThan
  deriving DecidableEq

/-- Each correction is a candidate, *more than n − 1*, *at least n*, *at most n + 1* or *fewer
than n + 2*. -/
def Correction.candidate (n : ℕ) : Correction → Candidate
  | .moreThan => ⟨.moreThan, n - 1⟩
  | .atLeast => ⟨.atLeast, n⟩
  | .atMost => ⟨.atMost, n + 1⟩
  | .fewerThan => ⟨.fewerThan, n + 2⟩

/-- The candidates of the tableaux. -/
def Correction.all : Finset Correction := {.moreThan, .atLeast, .atMost, .fewerThan}

/-- The speaker knows each box holds `n` or `n + 1` items, and the description corrected
primed its quantifier and numeral. -/
def correctionContext (n : ℕ) (form : Form) (numeral : ℕ) : Context :=
  { lo := some n, hi := some (n + 1), primedNumeral := some numeral, primedForm := some form }

/-- The correction system ranks quantifier priming, numeral priming, quantifier simplicity and
informativeness. -/
def corr (ctx : Context) : ConstraintSet Candidate (Fin 4) := ![qpri ctx, npri ctx, qsimp, info ctx]

/-- The correction system on the four corrections. -/
def corrOn (ctx : Context) (n : ℕ) : ConstraintSet Correction (Fin 4) :=
  (corr ctx).comap (Correction.candidate n)

/-- The printed marks of Table 3.9, after *more than n*, set quantifier and numeral priming
against the corrections that change them and simplicity against the superlatives. -/
def table3_9 : ConstraintSet Correction (Fin 4) :=
  ![Constraint.binary (· ≠ .moreThan), Constraint.binary (· ≠ .atLeast),
    Constraint.binary (fun c ↦ c = .atLeast ∨ c = .atMost), 0]

/-- The printed marks of Table 3.10, after *at least n − 1*. -/
def table3_10 : ConstraintSet Correction (Fin 4) :=
  ![Constraint.binary (· ≠ .atLeast), Constraint.binary (· ≠ .moreThan),
    Constraint.binary (fun c ↦ c = .atLeast ∨ c = .atMost), 0]

-- `Matrix.cons_val_two`/`three` are named because the `Matrix.cons_val` simproc panics on an
-- over-applied vector at a literal index of two or more.
-- Table 3.9
theorem corrOn_moreThan {n : ℕ} (hn : 1 ≤ n) :
    corrOn (correctionContext n .moreThan n) n = table3_9 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  funext i c
  match i with
  | 0 | 1 | 2 | 3 => cases c <;>
    simp [corrOn, corr, table3_9, Matrix.cons_val_two, Matrix.cons_val_three, correctionContext,
      Correction.candidate, qpri, npri, qsimp, info, Form.complexity, Nat.add_assoc]

-- Table 3.10
theorem corrOn_atLeast {n : ℕ} (hn : 1 ≤ n) :
    corrOn (correctionContext n .atLeast (n - 1)) n = table3_10 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  funext i c
  match i with
  | 0 | 1 | 2 | 3 => cases c <;>
    simp [corrOn, corr, table3_10, Matrix.cons_val_two, Matrix.cons_val_three, correctionContext,
      Correction.candidate, qpri, npri, qsimp, info, Form.complexity, Nat.add_assoc]

theorem moreThan_correction_optimal {n : ℕ} (hn : 1 ≤ n) (r : Ranking (Fin 4) 4) :
    (Tableau.ofRanking (corrOn (correctionContext n .moreThan n) n) r Correction.all).optimal =
      if r.Dominates 0 1 ∨ r.Dominates 2 1 then {.moreThan} else {.atLeast} := by
  rw [corrOn_moreThan hn]; revert r; decide +kernel

theorem atLeast_correction_optimal {n : ℕ} (hn : 1 ≤ n) (r : Ranking (Fin 4) 4) :
    (Tableau.ofRanking (corrOn (correctionContext n .atLeast (n - 1)) n) r
      Correction.all).optimal =
      if r.Dominates 1 0 ∨ r.Dominates 2 0 then {.moreThan} else {.atLeast} := by
  rw [corrOn_atLeast hn]; revert r; decide +kernel

/-! ### The hearer, and the implicature of *more than n* (§3.4, §5.3, §5.4) -/

theorem about100_notMem_optimal_of_exact (r : Ranking (Fin 3) 3) :
    about 100 ∉ (Tableau.ofRanking (approx (.exact 100)) r {bare 100, about 100}).optimal := by
  revert r; decide

/-- In a context, *more than m* is a stronger alternative to *more than n* when `n < m` and `m`
is at least as salient as `n` and at its granularity level, if the context sets one. -/
def StrongerAlternative (ctx : Context) (n m : ℕ) : Prop :=
  n < m ∧ roundness n ≤ roundness m ∧
    (ctx.granularity = none ∨ granularityLevel m = granularityLevel n)

instance (ctx : Context) (n m : ℕ) : Decidable (StrongerAlternative ctx n m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- [cummins-sauerland-solt-2012]
theorem moreThan_notMem_optimal {ctx : Context} {L n m : ℕ} (hlo : ctx.lo = some L)
    (halt : StrongerAlternative ctx n m) (hm : m < L) (hp : ctx.primedNumeral ≠ some n)
    (r : Ranking (Fin 6) 6) {cands : Finset Candidate} (hc : moreThan m ∈ cands) :
    moreThan n ∉ (Tableau.ofRanking (con ctx) r cands).optimal := by
  obtain ⟨hnm, hsal, hgran⟩ := halt
  refine Tableau.ofRanking_notMem_optimal_of_lt hc (Pi.lt_def.2 ⟨fun i ↦ ?_, 0, ?_⟩)
  · match i with
    | 0 =>
      show info ctx (moreThan m) ≤ info ctx (moreThan n)
      simp only [info, moreThan, hlo]; omega
    | 1 =>
      show gran ctx (moreThan m) ≤ gran ctx (moreThan n)
      rcases hgran with hg | hg
      · simp only [gran, hg, Option.elim_none, le_refl]
      · simp only [gran, moreThan, hg, le_refl]
    | 2 => exact le_rfl
    | 3 => show 4 - roundness m ≤ 4 - roundness n; omega
    | 4 =>
      show npri ctx (moreThan m) ≤ npri ctx (moreThan n)
      unfold npri
      rcases hq : ctx.primedNumeral with _ | p
      · exact le_rfl
      · have hnp : n ≠ p := fun e ↦ hp (e ▸ hq)
        simp only [moreThan, hnp, ite_false]
        split_ifs <;> omega
    | 5 => exact le_rfl
  · show info ctx (moreThan m) < info ctx (moreThan n)
    simp only [info, moreThan, hlo]; omega

-- §5.4
theorem moreThan_optimal_iff_of_primed {ctx : Context} {L n m : ℕ} (hlo : ctx.lo = some L)
    (halt : StrongerAlternative ctx n m) (hm : m < L) (hp : ctx.primedNumeral = some n)
    (r : Ranking (Fin 6) 6) :
    (Tableau.ofRanking (con ctx) r {moreThan n, moreThan m}).optimal = {moreThan n} ↔
      r.Dominates 4 0 ∧ (roundness n < roundness m → r.Dominates 4 3) := by
  obtain ⟨hnm, hsal, hgran⟩ := halt
  have h0 : con ctx 0 (moreThan m) < con ctx 0 (moreThan n) := by
    show info ctx (moreThan m) < info ctx (moreThan n); simp only [info, moreThan, hlo]; omega
  have h1 : con ctx 1 (moreThan n) = con ctx 1 (moreThan m) := by
    show gran ctx (moreThan n) = gran ctx (moreThan m)
    rcases hgran with hg | hg
    · simp only [gran, hg, Option.elim_none]
    · simp only [gran, moreThan, hg]
  have h3 : con ctx 3 (moreThan m) < con ctx 3 (moreThan n) ↔ roundness n < roundness m := by
    show 4 - roundness m < 4 - roundness n ↔ _; have := roundness_le_four m; omega
  have h4 : con ctx 4 (moreThan n) < con ctx 4 (moreThan m) := by
    show npri ctx (moreThan n) < npri ctx (moreThan m)
    simp only [npri, moreThan, hp, ite_eq_right hnm.ne']; exact Nat.zero_lt_one
  have hne : moreThan n ≠ moreThan m := by simp [moreThan, hnm.ne]
  refine (Tableau.optimal_eq_singleton_iff_pair (by simp) hne).trans ?_
  rw [Tableau.ofRanking_profile_lt_iff_exists_dominates]
  constructor
  · rintro ⟨i, hi, hd⟩
    obtain rfl : i = 4 := by
      match i with
      | 4 => rfl
      | 0 => exact absurd hi h0.asymm
      | 1 => exact absurd hi h1.not_lt
      | 3 => exact absurd hi (not_lt.2 (Nat.sub_le_sub_left hsal 4))
      | 2 | 5 => exact absurd hi (lt_irrefl _)
    exact ⟨hd 0 h0, fun hs ↦ hd 3 (h3.2 hs)⟩
  · rintro ⟨hd0, hd3⟩
    refine ⟨4, h4, fun j hj ↦ ?_⟩
    match j with
    | 0 => exact hd0
    | 1 => exact absurd hj h1.symm.not_lt
    | 3 => exact hd3 (h3.1 hj)
    | 4 => exact absurd hj h4.asymm
    | 2 | 5 => exact absurd hj (lt_irrefl _)

end Cummins2015
