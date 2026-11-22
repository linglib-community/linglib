module

public import Linglib.Data.Statistics.Cummins2015
public import Linglib.Phonology.OptimalityTheory.Evaluation
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Set.Nat
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Tactic.DeriveFintype

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

We derive the constraints' violations from the numeral and the context, informativeness as the
number of possibilities an expression admits that the speaker's knowledge excludes, reproduce
the book's tableaux from them, and prove for arbitrary numerals the bounding implicature, its
absence when the stronger numeral is less salient, and the exact condition for its attenuation
under priming. The corrections of the book's Experiment 2 are `Cummins2015.corrections`.

## Implementation notes

* Numeral salience uses the book's k-ness with a zero exponent admitted, under which 20 and
  100 are entirely round. The tableaux print one salience mark for a numeral with no k-ness and
  none for 50; `nsal` counts four and one, which changes no comparison in them.
* Quantifier simplicity follows the book's simplifying assumption that a comparative incurs
  no violation and a superlative one; *exactly* and *about* incur one, as its tableaux print.
* The possibilities informativeness counts are the exact values and the approximate values, the
  book's higher level of counting. A bare numeral admits its exact value and, when entirely
  round, its approximate value, *exactly n* and *about n* one possibility each, and a bounded
  expression every exact value in its range; these give the printed informativeness marks of
  the approximation tableaux, a parenthesized star counting as one.
* A bounded expression is assessed against the bound under discussion: the values the speaker's
  knowledge leaves open are closed upwards for a lower bound and downwards for an upper bound.
* Rankings are of all six constraints. The toy and approximation tableaux print the three that
  distinguish their candidates; the correction system leaves numeral salience out, as the book's
  tableaux do.
* The correction tableaux are derived for all four descriptions of Experiment 2; the book prints
  those after *more than n* and *at least n − 1* and describes the other two as similar.
* `moreThan_optimal_iff_of_primed` is exact for the derived violations: when the stronger
  numeral is strictly more salient, as 80 is than 70, numeral priming must outrank salience as
  well as informativeness.
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

/-! ### Candidates and what they admit (§2.4.1) -/

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

/-- *more than n*. -/
def moreThan (n : ℕ) : Candidate := ⟨.moreThan, n⟩

/-- The bare numeral. -/
def bare (n : ℕ) : Candidate := ⟨.bare, n⟩

/-- *exactly n*. -/
def exactly (n : ℕ) : Candidate := ⟨.exactly, n⟩

/-- *about n*. -/
def about (n : ℕ) : Candidate := ⟨.about, n⟩

/-- A possibility a speaker may mean to convey: that the value is exactly `n`, or that it is
approximately `n`. -/
inductive Situation where
  /-- Exactly `n`. -/
  | exact (n : ℕ)
  /-- Approximately `n`. -/
  | about (n : ℕ)
  deriving DecidableEq

/-- The possibilities an expression admits. A bounded expression admits each exact value in its
range, *exactly n* and *about n* one possibility each, and a bare numeral its exact value,
together with the approximate one when it is entirely round. -/
def Candidate.admits (c : Candidate) : Set Situation :=
  match c.form with
  | .bare => {t | t = .exact c.numeral ∨ t = .about c.numeral ∧ EntirelyRound c.numeral}
  | .exactly => {.exact c.numeral}
  | .about => {.about c.numeral}
  | .moreThan => .exact '' Set.Ioi c.numeral
  | .atLeast => .exact '' Set.Ici c.numeral
  | .fewerThan => .exact '' Set.Iio c.numeral
  | .atMost => .exact '' Set.Iic c.numeral

/-- The bound under discussion: of the values the speaker's knowledge leaves open, a lower-bounded
expression is assessed against the lower bound alone and an upper-bounded one against the upper
bound alone. -/
def Form.topic : Form → Set ℕ → Set ℕ
  | .moreThan | .atLeast => fun V ↦ upperClosure V
  | .fewerThan | .atMost => fun V ↦ lowerClosure V
  | .bare | .exactly | .about => id

/-! ### Contexts and the six constraints (§2.4) -/

/-- The context of utterance records the possibilities the speaker's knowledge leaves open, the
granularity level the context sets, if any, and the primed numeral and quantifier. -/
structure Context where
  /-- The possibilities the speaker's knowledge leaves open. -/
  knowledge : Set Situation := Set.univ
  /-- The granularity level the context sets. -/
  granularity : Option ℕ := none
  /-- The numeral activated in the prior context. -/
  primedNumeral : Option ℕ := none
  /-- The quantifier activated in the prior context. -/
  primedForm : Option Form := none

/-- The exact values the speaker's knowledge leaves open. -/
def Context.values (ctx : Context) : Set ℕ := Situation.exact ⁻¹' ctx.knowledge

/-- The speaker knows the value to be at least `L`. -/
def Context.atLeast (L : ℕ) : Context := { knowledge := .exact '' Set.Ici L }

/-- The speaker means to convey the possibility `s`. -/
def Situation.context (s : Situation) : Context := { knowledge := {s} }

variable {ctx : Context} {L H : ℕ} {s : Situation}

theorem Context.values_eq {V : Set ℕ} (h : ctx.knowledge = .exact '' V) : ctx.values = V := by
  rw [values, h, Set.preimage_image_eq _ fun _ _ ↦ Situation.exact.inj]

theorem Context.isLeast_values (h : ctx.knowledge = .exact '' Set.Ici L) :
    IsLeast ctx.values L := by
  rw [values_eq h]; exact isLeast_Ici

/-- Informativeness assigns one violation for each possibility the expression admits that the
speaker knows to be excluded, the speaker's knowledge of a bounded expression's values being
taken at the bound under discussion (constraint 1). -/
noncomputable def info (ctx : Context) : Constraint Candidate := fun c ↦
  (c.admits \ (ctx.knowledge ∪ .exact '' c.form.topic ctx.values)).ncard

private theorem ncard_exact_image_diff {S V : Set ℕ} {K : Set Situation}
    (hK : Situation.exact ⁻¹' K ⊆ V) :
    (Situation.exact '' S \ (K ∪ Situation.exact '' V)).ncard = (S \ V).ncard := by
  have : Situation.exact '' S \ (K ∪ Situation.exact '' V) = Situation.exact '' (S \ V) := by
    ext t
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, ht⟩
      exact ⟨k, ⟨hk, fun hV ↦ ht (.inr ⟨k, hV, rfl⟩)⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hV⟩, rfl⟩
      refine ⟨⟨k, hk, rfl⟩, ?_⟩
      rintro (h | ⟨j, hj, e⟩)
      · exact hV (hK h)
      · exact hV (Situation.exact.inj e ▸ hj)
  rw [this, Set.ncard_image_of_injective _ fun _ _ ↦ Situation.exact.inj]

private theorem coe_upperClosure_of_isLeast {V : Set ℕ} (h : IsLeast V L) :
    (upperClosure V : Set ℕ) = Set.Ici L := by
  ext k
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_Ici]
  exact ⟨fun ⟨a, ha, hak⟩ ↦ (h.2 ha).trans hak, fun hk ↦ ⟨L, h.1, hk⟩⟩

private theorem coe_lowerClosure_of_isGreatest {V : Set ℕ} (h : IsGreatest V H) :
    (lowerClosure V : Set ℕ) = Set.Iic H := by
  ext k
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_Iic]
  exact ⟨fun ⟨a, ha, hka⟩ ↦ hka.trans (h.2 ha), fun hk ↦ ⟨H, h.1, hk⟩⟩

theorem info_moreThan (h : IsLeast ctx.values L) (n : ℕ) :
    info ctx (moreThan n) = L - (n + 1) := by
  rw [info, show (moreThan n).admits = .exact '' Set.Ioi n from rfl,
    show (moreThan n).form.topic ctx.values = Set.Ici L from coe_upperClosure_of_isLeast h,
    ncard_exact_image_diff fun _ hk ↦ h.2 hk,
    show Set.Ioi n \ Set.Ici L = Set.Ioo n L from Set.ext fun k ↦ by simp, Set.ncard_Ioo_nat]
  omega

theorem info_atLeast (h : IsLeast ctx.values L) (n : ℕ) :
    info ctx ⟨.atLeast, n⟩ = L - n := by
  rw [info, show (Candidate.mk .atLeast n).admits = .exact '' Set.Ici n from rfl,
    show Form.atLeast.topic ctx.values = Set.Ici L from coe_upperClosure_of_isLeast h,
    ncard_exact_image_diff fun _ hk ↦ h.2 hk,
    show Set.Ici n \ Set.Ici L = Set.Ico n L from Set.ext fun k ↦ by simp, Set.ncard_Ico_nat]

theorem info_fewerThan (h : IsGreatest ctx.values H) (n : ℕ) :
    info ctx ⟨.fewerThan, n⟩ = n - (H + 1) := by
  rw [info, show (Candidate.mk .fewerThan n).admits = .exact '' Set.Iio n from rfl,
    show Form.fewerThan.topic ctx.values = Set.Iic H from coe_lowerClosure_of_isGreatest h,
    ncard_exact_image_diff fun _ hk ↦ h.2 hk,
    show Set.Iio n \ Set.Iic H = Set.Ioo H n from Set.ext fun k ↦ by simp,
    Set.ncard_Ioo_nat]
  omega

theorem info_atMost (h : IsGreatest ctx.values H) (n : ℕ) :
    info ctx ⟨.atMost, n⟩ = n - H := by
  rw [info, show (Candidate.mk .atMost n).admits = .exact '' Set.Iic n from rfl,
    show Form.atMost.topic ctx.values = Set.Iic H from coe_lowerClosure_of_isGreatest h,
    ncard_exact_image_diff fun _ hk ↦ h.2 hk,
    show Set.Iic n \ Set.Iic H = Set.Ioc H n from Set.ext fun k ↦ by simp [and_comm],
    Set.ncard_Ioc_nat]

private theorem ncard_singleton_diff (a s : Situation) :
    (({a} : Set Situation) \ {s}).ncard = if a = s then 0 else 1 := by
  split_ifs with e
  · simp [e]
  · rw [Set.sdiff_singleton_eq_self fun h ↦ e (Set.mem_singleton_iff.1 h).symm,
      Set.ncard_singleton]

private theorem info_eq_of_topic_eq_id {c : Candidate} (hc : c.form.topic = id)
    (h : ctx.knowledge = {s}) : info ctx c = (c.admits \ {s}).ncard := by
  rw [info, hc, id, Context.values, Set.union_eq_left.2 (Set.image_preimage_subset _ _), h]

theorem info_exactly (h : ctx.knowledge = {s}) (n : ℕ) :
    info ctx (exactly n) = if .exact n = s then 0 else 1 :=
  (info_eq_of_topic_eq_id rfl h).trans (ncard_singleton_diff _ _)

theorem info_about (h : ctx.knowledge = {s}) (n : ℕ) :
    info ctx (about n) = if .about n = s then 0 else 1 :=
  (info_eq_of_topic_eq_id rfl h).trans (ncard_singleton_diff _ _)

theorem info_bare (h : ctx.knowledge = {s}) (n : ℕ) :
    info ctx (bare n) = (if .exact n = s then 0 else 1) +
      if EntirelyRound n ∧ .about n ≠ s then 1 else 0 := by
  rw [info_eq_of_topic_eq_id rfl h]
  by_cases hr : EntirelyRound n
  · have hd : Disjoint (({.exact n} : Set Situation) \ {s}) ({.about n} \ {s}) :=
      Set.disjoint_of_subset Set.sdiff_subset Set.sdiff_subset
        (Set.disjoint_singleton.2 Situation.noConfusion)
    rw [show (bare n).admits = {.exact n} ∪ {.about n} from
        Set.ext fun t ↦ by simpa [Candidate.admits, bare, hr] using or_comm,
      Set.union_sdiff_distrib, Set.ncard_union_eq hd
        ((Set.finite_singleton _).subset Set.sdiff_subset)
        ((Set.finite_singleton _).subset Set.sdiff_subset),
      ncard_singleton_diff, ncard_singleton_diff]
    simp only [hr, true_and, ne_eq, ite_not]
  · rw [show (bare n).admits = {.exact n} from
        Set.ext fun t ↦ by simp [Candidate.admits, bare, hr], ncard_singleton_diff]
    simp only [hr, false_and, ite_false, add_zero]

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
    10 ^ granularityLevel n = scaleLcm {1000, 100, 10, 1} n := by
  refine ((isGreatest_scaleLcm (by decide) (by unfold IsChain; beta_reduce; decide)
    ⟨1, by decide, one_dvd _⟩).unique ⟨⟨?_, ?_⟩, ?_⟩).symm <;> unfold granularityLevel
  · split_ifs <;> decide
  · split_ifs <;> norm_num <;> assumption_mod_cast
  · rintro w ⟨hw, hwn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> norm_cast at hwn <;> split_ifs <;> norm_num <;> omega

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

/-- The six constraints, in the book's order. -/
inductive Con where
  /-- Informativeness. -/
  | info
  /-- Granularity. -/
  | gran
  /-- Quantifier simplicity. -/
  | qsimp
  /-- Numeral salience. -/
  | nsal
  /-- Numeral priming. -/
  | npri
  /-- Quantifier priming. -/
  | qpri
  deriving DecidableEq, Fintype

/-- The tableau of the six constraints with informativeness assessed by `I`. -/
def tableau (I : Constraint Candidate) (ctx : Context) (c : Candidate) : Con → ℕ
  | .info => I c
  | .gran => gran ctx c
  | .qsimp => qsimp c
  | .nsal => nsal c
  | .npri => npri ctx c
  | .qpri => qpri ctx c

/-- The violations of the six constraints in a context. -/
noncomputable def con (ctx : Context) : Tableau Candidate Con := tableau (info ctx) ctx

private theorem optimal_con {I : Constraint Candidate} {cands : Finset Candidate}
    (h : ∀ c ∈ cands, info ctx c = I c) (r : Ranking Con) :
    r.optimal (con ctx) cands = r.optimal (tableau I ctx) cands := by
  have e : ∀ c ∈ cands, con ctx c = tableau I ctx c := fun c hc ↦ funext fun i ↦ by
    cases i <;> first | rfl | exact h c hc
  ext c
  simp only [Ranking.Enumeration.mem_optimal_iff]
  refine and_congr_right fun hc ↦ forall₂_congr fun d hd ↦ ?_
  simp only [Ranking.Enumeration.profile, e c hc, e d hd]

/-! ### Constraint interaction in the toy example (§3.1, Tables 3.1–3.3) -/

/-- The speaker knows the value to be at least 22, with 21 contextually salient. -/
def atLeast22Primed : Context := { Context.atLeast 22 with primedNumeral := some 21 }

private theorem info_atLeast22 (h : ctx.knowledge = .exact '' Set.Ici 22) :
    ∀ c ∈ ({moreThan 21, moreThan 20} : Finset Candidate),
      info ctx c = 22 - (c.numeral + 1) := fun c hc ↦ by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl <;> exact info_moreThan (Context.isLeast_values h) _

-- Table 3.1, Table 3.3
theorem atLeast22_optimal (r : Ranking Con) :
    r.optimal (con (.atLeast 22)) {moreThan 21, moreThan 20} =
      if r.Dominates .info .nsal then {moreThan 21} else {moreThan 20} := by
  rw [optimal_con (info_atLeast22 rfl)]; revert r; decide +kernel

-- Table 3.2, Table 3.3
theorem atLeast22Primed_optimal (r : Ranking Con) :
    r.optimal (con atLeast22Primed) {moreThan 21, moreThan 20} =
      if r.Dominates .nsal .info ∧ r.Dominates .nsal .npri then {moreThan 20}
      else {moreThan 21} := by
  rw [optimal_con (info_atLeast22 rfl)]; revert r; decide +kernel

/-- A ranking with priming over salience over informativeness, the last of Table 3.3. -/
def primingFirst : Ranking Con := .ofList [.npri, .nsal, .info, .gran, .qsimp, .qpri]

theorem primingFirst_optimal :
    primingFirst.optimal (con (.atLeast 22)) {moreThan 21, moreThan 20} = {moreThan 20} ∧
      primingFirst.optimal (con atLeast22Primed) {moreThan 21, moreThan 20} =
        {moreThan 21} := by
  rw [atLeast22_optimal, atLeast22Primed_optimal]; decide +kernel

/-! ### Approximation (§3.3.1, Tables 3.4–3.8) -/

/-- Informativeness of *n*, *exactly n* and *about n* for a speaker who means `s`, in closed
form. -/
private def pointInfo (s : Situation) : Constraint Candidate := fun c ↦
  match c.form with
  | .bare => (if .exact c.numeral = s then 0 else 1) +
      if EntirelyRound c.numeral ∧ .about c.numeral ≠ s then 1 else 0
  | .exactly => if .exact c.numeral = s then 0 else 1
  | .about => if .about c.numeral = s then 0 else 1
  | _ => 0

private theorem info_eq_pointInfo (h : ctx.knowledge = {s}) (c : Candidate)
    (hc : c.form = .bare ∨ c.form = .exactly ∨ c.form = .about) :
    info ctx c = pointInfo s c := by
  obtain ⟨f, n⟩ := c
  obtain rfl | rfl | rfl : f = .bare ∨ f = .exactly ∨ f = .about := hc
  exacts [info_bare h n, info_exactly h n, info_about h n]

-- Table 3.4
theorem bare_notMem_optimal_of_roundness_lt {n m : ℕ} (hmn : roundness m < roundness n)
    (r : Ranking Con) {cands : Finset Candidate} (hc : bare n ∈ cands) :
    bare m ∉ r.optimal (con (Situation.exact n).context) cands := by
  have hne : Situation.exact m ≠ .exact n := fun e ↦
    hmn.ne (congrArg roundness (Situation.exact.inj e))
  refine Ranking.Enumeration.notMem_optimal_of_lt hc (Pi.lt_def.2 ⟨fun i ↦ ?_, .nsal, ?_⟩)
  · cases i with
    | info =>
      show info _ (bare n) ≤ info _ (bare m)
      rw [info_bare rfl, info_bare rfl]
      simp only [↓reduceIte, hne]
      split_ifs <;> omega
    | nsal => show 4 - roundness n ≤ 4 - roundness m; omega
    | gran | qsimp | npri | qpri => exact le_rfl
  · show 4 - roundness n < 4 - roundness m
    have := roundness_le_four n; omega

private theorem optimal_context {cands : Finset Candidate}
    (h : ∀ c ∈ cands, c.form = .bare ∨ c.form = .exactly ∨ c.form = .about)
    (r : Ranking Con) :
    r.optimal (con s.context) cands = r.optimal (tableau (pointInfo s) s.context) cands :=
  optimal_con (fun c hc ↦ info_eq_pointInfo rfl c (h c hc)) r

-- Table 3.5
theorem exact51_optimal (r : Ranking Con) :
    r.optimal (con (Situation.exact 51).context) {bare 50, bare 51} =
      if r.Dominates .info .nsal then {bare 51} else {bare 50} := by
  rw [optimal_context (by decide)]; revert r; decide +kernel

-- Table 3.6
theorem exact100_optimal (r : Ranking Con) :
    r.optimal (con (Situation.exact 100).context)
        {bare 100, exactly 100, about 100, about 99} =
      if r.Dominates .info .qsimp then {exactly 100} else {bare 100} := by
  rw [optimal_context (by decide)]; revert r; decide +kernel

-- Table 3.7
theorem about100_optimal (r : Ranking Con) :
    r.optimal (con (Situation.about 100).context) {bare 100, about 100} =
      if r.Dominates .info .qsimp then {about 100} else {bare 100} := by
  rw [optimal_context (by decide)]; revert r; decide +kernel

-- Table 3.8
theorem exact99_optimal (r : Ranking Con) :
    r.optimal (con (Situation.exact 99).context) {bare 99, exactly 99, bare 100, about 100} =
      if r.Dominates .info .nsal then {bare 99}
      else if r.Dominates .qsimp .info then {bare 100} else {about 100} := by
  rw [optimal_context (by decide)]; revert r; decide +kernel

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

/-- The description a participant corrects, as a candidate: *more than n*, *fewer than n + 1*,
*at least n − 1* or *at most n + 2*. -/
def Prompt.candidate (n : ℕ) : Prompt → Candidate
  | .moreThan => ⟨.moreThan, n⟩
  | .fewerThan => ⟨.fewerThan, n + 1⟩
  | .atLeast => ⟨.atLeast, n - 1⟩
  | .atMost => ⟨.atMost, n + 2⟩

/-- The speaker knows each box holds `n` or `n + 1` items, and the description corrected
primed its quantifier and numeral. -/
def Prompt.context (n : ℕ) (p : Prompt) : Context :=
  { knowledge := .exact '' Set.Icc n (n + 1), primedNumeral := some (p.candidate n).numeral,
    primedForm := some (p.candidate n).form }

/-- The maximally informative comparative on the prompt's side. -/
def Prompt.comparative : Prompt → Correction
  | .moreThan | .atLeast => .moreThan
  | .fewerThan | .atMost => .fewerThan

/-- The maximally informative superlative on the prompt's side. -/
def Prompt.superlative : Prompt → Correction
  | .moreThan | .atLeast => .atLeast
  | .fewerThan | .atMost => .atMost

/-- The correction that keeps the prompt's quantifier. -/
def Prompt.sameQuantifier : Prompt → Correction
  | .moreThan => .moreThan
  | .fewerThan => .fewerThan
  | .atLeast => .atLeast
  | .atMost => .atMost

/-- The correction that keeps the prompt's numeral. -/
def Prompt.sameNumeral : Prompt → Correction
  | .moreThan => .atLeast
  | .fewerThan => .atMost
  | .atLeast => .moreThan
  | .atMost => .fewerThan

/-- The correction system leaves numeral salience out of the six constraints. -/
noncomputable def corr (ctx : Context) (n : ℕ) (c : Correction) : Con → ℕ
  | .nsal => 0
  | i => con ctx (c.candidate n) i

/-- The marks of a correction tableau set quantifier priming against every correction but `q`,
numeral priming against every correction but `k`, and simplicity against the superlatives.
Table 3.9, after *more than n*, is `marks .moreThan .atLeast`, and Table 3.10, after *at least
n − 1*, is `marks .atLeast .moreThan`. -/
def marks (q k c : Correction) : Con → ℕ
  | .qpri => Constraint.binary (· ≠ q) c
  | .npri => Constraint.binary (· ≠ k) c
  | .qsimp => Constraint.binary (fun c ↦ c = .atLeast ∨ c = .atMost) c
  | .info | .gran | .nsal => 0

-- Table 3.9, Table 3.10
theorem corr_context {n : ℕ} (hn : 1 ≤ n) (p : Prompt) :
    corr (p.context n) n = marks p.sameQuantifier p.sameNumeral := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hV : (p.context (n + 1)).values = Set.Icc (n + 1) (n + 1 + 1) := Context.values_eq rfl
  have hL : IsLeast (p.context (n + 1)).values (n + 1) := hV ▸ ⟨by simp, fun _ h ↦ h.1⟩
  have hH : IsGreatest (p.context (n + 1)).values (n + 1 + 1) :=
    hV ▸ ⟨by simp, fun _ h ↦ h.2⟩
  funext c i
  cases i with
  | info =>
    show info _ (c.candidate (n + 1)) = 0
    cases c
    · exact (info_moreThan hL _).trans (by omega)
    · exact (info_atLeast hL _).trans (by omega)
    · exact (info_atMost hH _).trans (by omega)
    · exact (info_fewerThan hH _).trans (by omega)
  | nsal => rfl
  | gran | qsimp | npri | qpri => cases p <;> cases c <;>
    simp [corr, con, tableau, marks, Prompt.context, Prompt.candidate, Prompt.sameQuantifier,
      Prompt.sameNumeral, Correction.candidate, gran, qpri, npri, qsimp, Form.complexity,
      Nat.add_assoc]

/-- The rankings under which the comparative correction beats the superlative: after a
comparative, quantifier priming or simplicity over numeral priming; after a superlative, numeral
priming or simplicity over quantifier priming. -/
def Prompt.ComparativeWins (r : Ranking Con) : Prompt → Prop
  | .moreThan | .fewerThan => r.Dominates .qpri .npri ∨ r.Dominates .qsimp .npri
  | .atLeast | .atMost => r.Dominates .npri .qpri ∨ r.Dominates .qsimp .qpri

instance (r : Ranking Con) (p : Prompt) : Decidable (p.ComparativeWins r) := by
  cases p <;> exact inferInstanceAs (Decidable (_ ∨ _))

private theorem marks_optimal_moreThan (r : Ranking Con) :
    r.optimal (marks (Prompt.moreThan).sameQuantifier (Prompt.moreThan).sameNumeral)
        Correction.all =
      if (Prompt.moreThan).ComparativeWins r then {(Prompt.moreThan).comparative}
      else {(Prompt.moreThan).superlative} := by
  revert r; decide +kernel

private theorem marks_optimal_fewerThan (r : Ranking Con) :
    r.optimal (marks (Prompt.fewerThan).sameQuantifier (Prompt.fewerThan).sameNumeral)
        Correction.all =
      if (Prompt.fewerThan).ComparativeWins r then {(Prompt.fewerThan).comparative}
      else {(Prompt.fewerThan).superlative} := by
  revert r; decide +kernel

private theorem marks_optimal_atLeast (r : Ranking Con) :
    r.optimal (marks (Prompt.atLeast).sameQuantifier (Prompt.atLeast).sameNumeral)
        Correction.all =
      if (Prompt.atLeast).ComparativeWins r then {(Prompt.atLeast).comparative}
      else {(Prompt.atLeast).superlative} := by
  revert r; decide +kernel

private theorem marks_optimal_atMost (r : Ranking Con) :
    r.optimal (marks (Prompt.atMost).sameQuantifier (Prompt.atMost).sameNumeral)
        Correction.all =
      if (Prompt.atMost).ComparativeWins r then {(Prompt.atMost).comparative}
      else {(Prompt.atMost).superlative} := by
  revert r; decide +kernel

/-- Under every ranking the optimal correction of a description is the maximally informative
comparative or superlative on its side, the comparative exactly under `Prompt.ComparativeWins`. -/
theorem correction_optimal {n : ℕ} (hn : 1 ≤ n) (p : Prompt) (r : Ranking Con) :
    r.optimal (corr (p.context n) n) Correction.all =
      if p.ComparativeWins r then {p.comparative} else {p.superlative} := by
  rw [corr_context hn]
  cases p
  exacts [marks_optimal_moreThan r, marks_optimal_fewerThan r, marks_optimal_atLeast r,
    marks_optimal_atMost r]

/-- No ranking yields the superlative correction after both a comparative and a superlative
description, since the first needs numeral priming over quantifier priming and the second the
reverse. -/
theorem comparativeWins_moreThan_or_atLeast (r : Ranking Con) :
    Prompt.moreThan.ComparativeWins r ∨ Prompt.atLeast.ComparativeWins r := by
  revert r; decide +kernel

-- Experiment 2: most corrections of each description take one of the two forms
-- `correction_optimal` allows.
theorem corrected_lt_two_mul_predicted (p : Prompt) :
    (corrections p).corrected <
      2 * ((corrections p).superlative + (corrections p).comparative) := by
  cases p <;> decide

/-! ### The hearer, and the implicature of *more than n* (§3.4, §5.3, §5.4) -/

theorem about100_notMem_optimal_of_exact (r : Ranking Con) :
    about 100 ∉ r.optimal (con (Situation.exact 100).context) {bare 100, about 100} := by
  rw [optimal_context (by decide)]; revert r; decide +kernel

/-- In a context, *more than m* is a stronger alternative to *more than n* when `n < m` and `m`
is at least as salient as `n` and at its granularity level, if the context sets one. -/
def StrongerAlternative (ctx : Context) (n m : ℕ) : Prop :=
  n < m ∧ roundness n ≤ roundness m ∧
    (ctx.granularity = none ∨ granularityLevel m = granularityLevel n)

instance (ctx : Context) (n m : ℕ) : Decidable (StrongerAlternative ctx n m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- *more than n* is never optimal for a speaker who knows *more than m* for a stronger
alternative `m`, unless `n` was primed, so its use implicates *not more than m*
([cummins-sauerland-solt-2012]). -/
theorem moreThan_notMem_optimal {n m : ℕ} (hlo : IsLeast ctx.values L)
    (halt : StrongerAlternative ctx n m) (hm : m < L) (hp : ctx.primedNumeral ≠ some n)
    (r : Ranking Con) {cands : Finset Candidate} (hc : moreThan m ∈ cands) :
    moreThan n ∉ r.optimal (con ctx) cands := by
  obtain ⟨hnm, hsal, hgran⟩ := halt
  have h0 : info ctx (moreThan m) < info ctx (moreThan n) := by
    rw [info_moreThan hlo, info_moreThan hlo]; omega
  refine Ranking.Enumeration.notMem_optimal_of_lt hc (Pi.lt_def.2 ⟨fun i ↦ ?_, .info, h0⟩)
  cases i with
  | info => exact h0.le
  | gran =>
    show gran ctx (moreThan m) ≤ gran ctx (moreThan n)
    rcases hgran with hg | hg
    · simp only [gran, hg, Option.elim_none, le_refl]
    · simp only [gran, moreThan, hg, le_refl]
  | nsal => show 4 - roundness m ≤ 4 - roundness n; omega
  | npri =>
    show npri ctx (moreThan m) ≤ npri ctx (moreThan n)
    unfold npri
    rcases hq : ctx.primedNumeral with _ | p
    · exact le_rfl
    · have hnp : n ≠ p := fun e ↦ hp (e ▸ hq)
      simp only [moreThan, hnp, ite_false]
      split_ifs <;> omega
  | qsimp | qpri => exact le_rfl

/-- With nothing primed and no granularity level set, *more than n* beats a true *more than m*
with `n < m` exactly when `n` is strictly more salient and salience outranks informativeness, so
*more than n* does not then implicate *not more than m* (§5.3). -/
theorem moreThan_optimal_iff_of_unprimed {n m : ℕ} (hlo : IsLeast ctx.values L)
    (hnm : n < m) (hm : m < L) (hg : ctx.granularity = none) (hp : ctx.primedNumeral = none)
    (r : Ranking Con) :
    r.optimal (con ctx) {moreThan n, moreThan m} = {moreThan n} ↔
      roundness m < roundness n ∧ r.Dominates .nsal .info := by
  have h0 : con ctx (moreThan m) .info < con ctx (moreThan n) .info := by
    show info ctx (moreThan m) < info ctx (moreThan n)
    rw [info_moreThan hlo, info_moreThan hlo]; omega
  have h1 : con ctx (moreThan n) .gran = con ctx (moreThan m) .gran := by
    show gran ctx (moreThan n) = gran ctx (moreThan m); simp only [gran, hg, Option.elim_none]
  have h3 : con ctx (moreThan n) .nsal < con ctx (moreThan m) .nsal ↔
      roundness m < roundness n := by
    show 4 - roundness n < 4 - roundness m ↔ _; have := roundness_le_four n; omega
  have h4 : con ctx (moreThan n) .npri = con ctx (moreThan m) .npri := by
    show npri ctx (moreThan n) = npri ctx (moreThan m); simp only [npri, hp]
  have hne : moreThan n ≠ moreThan m := by simp [moreThan, hnm.ne]
  refine (Ranking.Enumeration.optimal_eq_singleton_iff_pair rfl hne).trans ?_
  rw [Ranking.Enumeration.profile_lt_iff_exists_dominates]
  constructor
  · rintro ⟨i, hi, hd⟩
    cases i with
    | nsal => exact ⟨h3.1 hi, hd .info h0⟩
    | info => exact absurd hi h0.asymm
    | gran => exact absurd hi h1.not_lt
    | npri => exact absurd hi h4.not_lt
    | qsimp | qpri => exact absurd hi (lt_irrefl _)
  · rintro ⟨hs, hd⟩
    refine ⟨.nsal, h3.2 hs, fun j hj ↦ ?_⟩
    cases j with
    | info => exact hd
    | gran => exact absurd hj h1.symm.not_lt
    | nsal => exact absurd hj (h3.2 hs).asymm
    | npri => exact absurd hj h4.symm.not_lt
    | qsimp | qpri => exact absurd hj (lt_irrefl _)

-- (113), (116)
example (r : Ranking Con) :
    r.optimal (con (.atLeast 1002)) {moreThan 1000, moreThan 1001} = {moreThan 1000} ↔
      r.Dominates .nsal .info := by
  rw [moreThan_optimal_iff_of_unprimed (Context.isLeast_values rfl) (by decide) (by decide)
    rfl rfl]
  exact and_iff_right (by decide)

/-- When `n` is primed, *more than n* beats a true stronger alternative *more than m* exactly
when numeral priming outranks informativeness, and salience too if `m` is strictly more
salient (§5.4). -/
theorem moreThan_optimal_iff_of_primed {n m : ℕ} (hlo : IsLeast ctx.values L)
    (halt : StrongerAlternative ctx n m) (hm : m < L) (hp : ctx.primedNumeral = some n)
    (r : Ranking Con) :
    r.optimal (con ctx) {moreThan n, moreThan m} = {moreThan n} ↔
      r.Dominates .npri .info ∧ (roundness n < roundness m → r.Dominates .npri .nsal) := by
  obtain ⟨hnm, hsal, hgran⟩ := halt
  have h0 : con ctx (moreThan m) .info < con ctx (moreThan n) .info := by
    show info ctx (moreThan m) < info ctx (moreThan n)
    rw [info_moreThan hlo, info_moreThan hlo]; omega
  have h1 : con ctx (moreThan n) .gran = con ctx (moreThan m) .gran := by
    show gran ctx (moreThan n) = gran ctx (moreThan m)
    rcases hgran with hg | hg
    · simp only [gran, hg, Option.elim_none]
    · simp only [gran, moreThan, hg]
  have h3 : con ctx (moreThan m) .nsal < con ctx (moreThan n) .nsal ↔
      roundness n < roundness m := by
    show 4 - roundness m < 4 - roundness n ↔ _; have := roundness_le_four m; omega
  have h4 : con ctx (moreThan n) .npri < con ctx (moreThan m) .npri := by
    show npri ctx (moreThan n) < npri ctx (moreThan m)
    simp only [npri, moreThan, hp, ite_eq_right hnm.ne']; exact Nat.zero_lt_one
  have hne : moreThan n ≠ moreThan m := by simp [moreThan, hnm.ne]
  refine (Ranking.Enumeration.optimal_eq_singleton_iff_pair rfl hne).trans ?_
  rw [Ranking.Enumeration.profile_lt_iff_exists_dominates]
  constructor
  · rintro ⟨i, hi, hd⟩
    cases i with
    | npri => exact ⟨hd .info h0, fun hs ↦ hd .nsal (h3.2 hs)⟩
    | info => exact absurd hi h0.asymm
    | gran => exact absurd hi h1.not_lt
    | nsal => exact absurd hi (not_lt.2 (Nat.sub_le_sub_left hsal 4))
    | qsimp | qpri => exact absurd hi (lt_irrefl _)
  · rintro ⟨hd0, hd3⟩
    refine ⟨.npri, h4, fun j hj ↦ ?_⟩
    cases j with
    | info => exact hd0
    | gran => exact absurd hj h1.symm.not_lt
    | nsal => exact hd3 (h3.1 hj)
    | npri => exact absurd hj h4.asymm
    | qsimp | qpri => exact absurd hj (lt_irrefl _)

-- (117), (118)
example (r : Ranking Con) :
    r.optimal (con { Context.atLeast 81 with primedNumeral := some 70 })
        {moreThan 70, moreThan 80} = {moreThan 70} ↔
      r.Dominates .npri .info ∧ r.Dominates .npri .nsal := by
  rw [moreThan_optimal_iff_of_primed (Context.isLeast_values rfl) (by decide) (by decide) rfl]
  exact and_congr_right fun _ ↦ imp_iff_right (by decide)

end Cummins2015
