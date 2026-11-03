module

public import Linglib.Phonology.HarmonicGrammar.IntersectingFamilies
public import Linglib.Discourse.Givenness
public import Linglib.Data.Examples.ArnoldEtAl2000
public import Linglib.Data.Examples.Readers
public import Studies.Hawkins1994
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Arnold, Losongco, Wasow and Ginstrom (2000): Heaviness vs. Newness

This file models the order of two postverbal constituents in heavy NP shift and the English
dative alternation as [the paper's logistic regression](##themeLastProb_eq), a MaxEnt grammar in
which end weight, given before new and a cost of the theme-last order put the theme last with
probability $\sigma(w_H h + w_N n - w_B)$, $h$ the difference in words and $n$ in newness.
[Neither factor reduces to the other](##factorsThrough_heavyDiff_iff) and [they do not interact
in the log-odds](##interaction_logOdds_eq_zero), yet [newness matters most where the rest of the
grammar predicts least](##themeLastProb_new_sub_given_lt_iff). [Hawkins's recognition domain
grades the order by $h$](##sum_crd_verbPhrase_sub_eq_heavyDiff), [as the paper
counts](##crd_ex5_ex8).

## Implementation notes

* Newness is the paper's coding after Prince: given if the referent was mentioned before in the
  agenda item or the exchange, inferables counted as given. `BinaryGivenness` is read here as
  that coding, discourse-old against discourse-new, not as identifiability.
* Heaviness enters as the difference in words, the measure the paper takes; its regressions bin
  the difference into three categories for the dative alternation and five for heavy NP shift.
  For heavy NP shift the theme is the direct object and the goal the prepositional phrase, and
  the paper codes the newness of the direct object only.
* The construction's baseline is the regressions' intercept; the verb factor of the
  heavy-NP-shift corpus, selected without interactions, would be one baseline per verb.
* The experiment's newness × heaviness interaction lies outside a grammar of these constraints;
  its production-difficulty and participant factors and the fitted coefficients are not
  represented.

## References

* [arnold-losongco-wasow-ginstrom-2000]
* [behaghel-1909]
* [prince-1992]
* [hawkins-1994]
-/

@[expose] public section

namespace ArnoldEtAl2000

open OptimalityTheory HarmonicGrammar Discourse Real

/-! ### The grammar -/

/-- A constituent by the two measures the paper codes. -/
structure Phrase where
  /-- Its length in words. -/
  words : ℕ
  /-- Its discourse status. -/
  discourse : BinaryGivenness
  deriving DecidableEq

/-- A postverbal pair: theme and goal for the dative alternation, direct object and
prepositional phrase for heavy NP shift. -/
abbrev Pair := Phrase × Phrase

/-- Which constituent comes last: `themeLast` is the double object or the shifted order,
`goalLast` the prepositional dative or the canonical order. -/
inductive Order
  | themeLast
  | goalLast
  deriving DecidableEq, Fintype

instance : MeasurableSpace Order := ⊤
instance : MeasurableSingletonClass Order := ⟨fun _ ↦ trivial⟩

/-- A candidate is a pair in one of its two orders. -/
abbrev Candidate := Pair × Order

/-- End weight, Behaghel's law ([behaghel-1909]): the words by which the first constituent exceeds
the second. -/
def heavyFirst : Constraint Candidate
  | ((th, gl), .themeLast) => gl.words - th.words
  | ((th, gl), .goalLast) => th.words - gl.words

/-- Given before new: a new constituent before a given one. -/
def newFirst : Constraint Candidate
  | ((th, gl), .themeLast) => if gl.discourse = .new ∧ th.discourse = .given then 1 else 0
  | ((th, gl), .goalLast) => if th.discourse = .new ∧ gl.discourse = .given then 1 else 0

/-- The construction's own cost: a violation for the theme-last order whatever the
constituents, the intercept of the paper's regressions. -/
def starThemeLast : Constraint Candidate := Constraint.binary (·.2 = .themeLast)

/-- The three constraints. -/
def con : ConstraintSet Candidate (Fin 3) := ![heavyFirst, newFirst, starThemeLast]

/-- The weights: `wH` for heaviness, `wN` for newness, `wB` for the construction's baseline. -/
def weights (wH wN wB : ℝ) : Fin 3 → ℝ := ![wH, wN, wB]

/-- The probability of the theme-last order of a pair. -/
noncomputable def themeLastProb (wH wN wB : ℝ) (p : Pair) : ℝ :=
  (maxEnt (con.comap (p, ·)).violations (weights wH wN wB)).real {.themeLast}

/-- The heaviness predictor: the theme's length minus the goal's. -/
def heavyDiff (p : Pair) : ℝ := (p.1.words : ℝ) - p.2.words

/-- The newness predictor: `1` when the theme is new and the goal given, `-1` in the mirror case,
`0` otherwise. -/
def newDiff (p : Pair) : ℝ :=
  (if p.1.discourse = .new ∧ p.2.discourse = .given then (1 : ℝ) else 0) -
    (if p.2.discourse = .new ∧ p.1.discourse = .given then (1 : ℝ) else 0)

variable {wH wN wB : ℝ}

theorem harmonyScore_themeLast_sub (p : Pair) :
    harmonyScore con (weights wH wN wB) (p, .themeLast) -
      harmonyScore con (weights wH wN wB) (p, .goalLast) =
        wH * heavyDiff p + wN * newDiff p - wB := by
  obtain ⟨th, gl⟩ := p
  have h : ((th.words - gl.words : ℕ) : ℝ) - ((gl.words - th.words : ℕ) : ℝ) =
      th.words - gl.words := by
    exact_mod_cast (by omega : ((th.words - gl.words : ℕ) : ℤ) - (gl.words - th.words : ℕ) =
      th.words - gl.words)
  simp only [con, weights, harmonyScore_cons, harmonyScore_nil, heavyFirst, newFirst,
    starThemeLast, Constraint.binary_apply, heavyDiff, newDiff, reduceCtorEq, ite_true, ite_false]
  push_cast
  linear_combination wH * h

-- the paper's logistic regression on the heaviness and newness predictors, with an intercept
theorem themeLastProb_eq (p : Pair) :
    themeLastProb wH wN wB p = sigmoid (wH * heavyDiff p + wN * newDiff p - wB) := by
  rw [themeLastProb, maxEnt_real_singleton_of_pair _ _ (a := Order.themeLast) (b := .goalLast)
    (by decide) (by decide), harmony_violations, harmonyScore_comap, harmonyScore_comap,
    harmonyScore_themeLast_sub]

-- the newer and heavier the theme, the likelier it comes last
theorem themeLastProb_le_themeLastProb (hH : 0 ≤ wH) (hN : 0 ≤ wN) {p q : Pair}
    (hh : heavyDiff p ≤ heavyDiff q) (hn : newDiff p ≤ newDiff q) :
    themeLastProb wH wN wB p ≤ themeLastProb wH wN wB q := by
  rw [themeLastProb_eq, themeLastProb_eq]
  gcongr

/-! ### Neither factor reduces to the other -/

/-- The order's probability is a function of the heaviness difference alone exactly when newness
has no weight. -/
theorem factorsThrough_heavyDiff_iff :
    (themeLastProb wH wN wB).FactorsThrough heavyDiff ↔ wN = 0 := by
  refine ⟨fun h ↦ ?_, fun h p q hpq ↦ by simp only [themeLastProb_eq, h, zero_mul, hpq]⟩
  simpa [themeLastProb_eq, heavyDiff, newDiff] using
    @h (⟨0, .new⟩, ⟨0, .given⟩) (⟨0, .given⟩, ⟨0, .given⟩) (by simp [heavyDiff])

-- and a function of the newness difference alone exactly when heaviness has no weight
theorem factorsThrough_newDiff_iff :
    (themeLastProb wH wN wB).FactorsThrough newDiff ↔ wH = 0 := by
  refine ⟨fun h ↦ ?_, fun h p q hpq ↦ by simp only [themeLastProb_eq, h, zero_mul, hpq]⟩
  simpa [themeLastProb_eq, heavyDiff, newDiff] using
    @h (⟨1, .given⟩, ⟨0, .given⟩) (⟨0, .given⟩, ⟨0, .given⟩) (by simp [newDiff])

/-! ### Interaction -/

/-- The pair of a length and a givenness profile. -/
def pair (l : ℕ × ℕ) (s : BinaryGivenness × BinaryGivenness) : Pair :=
  (⟨l.1, s.1⟩, ⟨l.2, s.2⟩)

/-- The four pairs crossing two givenness profiles, the rows, with two length profiles, the
columns. -/
def cross (l l' : ℕ × ℕ) (s s' : BinaryGivenness × BinaryGivenness) : Square Pair :=
  ⟨pair l s, pair l' s, pair l s', pair l' s'⟩

theorem independent_cross (l l' : ℕ × ℕ) (s s' : BinaryGivenness × BinaryGivenness) :
    (cross l l' s s').Independent con .themeLast .goalLast := by
  intro k
  fin_cases k
  exacts [.inl ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩]

/-- Newness and heaviness do not interact in the log-odds of the two orders, as in the corpus
regressions; the experiment's interaction lies outside the grammar. -/
theorem interaction_logOdds_eq_zero (l l' : ℕ × ℕ) (s s' : BinaryGivenness × BinaryGivenness) :
    (cross l l' s s').interaction (fun p ↦
      log ((maxEnt (con.comap (p, ·)).violations (weights wH wN wB)).real {.themeLast} /
        (maxEnt (con.comap (p, ·)).violations (weights wH wN wB)).real {.goalLast})) = 0 :=
  (independent_cross l l' s s').interaction_logOdds_maxEnt _

-- what newness adds to the theme-last order at given lengths, comparing a new theme and given
-- goal with the reverse
theorem themeLastProb_new_sub_given (m n : ℕ) :
    themeLastProb wH wN wB (⟨m, .new⟩, ⟨n, .given⟩) -
        themeLastProb wH wN wB (⟨m, .given⟩, ⟨n, .new⟩) =
      sinh wN / (cosh (wH * ((m : ℝ) - n) - wB) + cosh wN) := by
  rw [themeLastProb_eq, themeLastProb_eq, ← sigmoid_add_sub_sigmoid_sub]
  congr 2 <;> simp [heavyDiff, newDiff] <;> ring

/-- Newness raises the probability of the theme-last order the more, the weaker the prediction
that heaviness and the construction's baseline make without it: the pattern of the corpus
figures, which the paper reads as interacting constraints. -/
theorem themeLastProb_new_sub_given_lt_iff (hN : 0 < wN) (m n m' n' : ℕ) :
    themeLastProb wH wN wB (⟨m', .new⟩, ⟨n', .given⟩) -
        themeLastProb wH wN wB (⟨m', .given⟩, ⟨n', .new⟩) <
      themeLastProb wH wN wB (⟨m, .new⟩, ⟨n, .given⟩) -
        themeLastProb wH wN wB (⟨m, .given⟩, ⟨n, .new⟩) ↔
      |wH * ((m : ℝ) - n) - wB| < |wH * ((m' : ℝ) - n') - wB| := by
  rw [themeLastProb_new_sub_given, themeLastProb_new_sub_given,
    div_lt_div_iff_of_pos_left (sinh_pos_iff.2 hN) (by positivity) (by positivity),
    add_lt_add_iff_right, cosh_lt_cosh]

-- (17): with a longer, newer constituent before a shorter, given one, both factors weigh
-- against the attested order, which is less probable than with constituents alike
theorem themeLastProb_lt_themeLastProb_of_lt_of_new_of_given {p : Pair} (q : Phrase)
    (hH : 0 ≤ wH) (hw : 0 < wH + wN) (hl : p.2.words < p.1.words)
    (hth : p.1.discourse = .new) (hgl : p.2.discourse = .given) :
    themeLastProb wH wN wB (q, q) < themeLastProb wH wN wB p := by
  have hd : (1 : ℝ) ≤ p.1.words - p.2.words := by
    rw [le_sub_iff_add_le']
    exact_mod_cast hl
  rw [themeLastProb_eq, themeLastProb_eq, sigmoid_lt_iff]
  simp only [newDiff, heavyDiff, hth, hgl, and_self, ite_true, reduceCtorEq, ite_false, sub_self,
    sub_zero, mul_zero, mul_one]
  linarith [mul_le_mul_of_nonneg_left hd hH]

/-! ### Hawkins's recognition domain -/

/-- The number of words in a constituent as printed. -/
def wordCount (s : String) : ℕ := (s.toList.filter (· = ' ')).length + 1

/-- The word counts of a row's two constituents in surface order. -/
def constituents (r : Datum) : Option (ℕ × ℕ) := do
  let a ← r.feature? "first"
  let b ← r.feature? "second"
  pure (wordCount a, wordCount b)

/-- A verb and the two constituents after it, of `c.1` and `c.2` words, as Hawkins's recognition
domain reads them, each constituent constructed by its first word: a preposition, a determiner
or a name. -/
def verbPhrase (c : ℕ × ℕ) : List Hawkins1994.IC := [⟨0, 0⟩, ⟨0, c.1 - 1⟩, ⟨0, c.2 - 1⟩]

-- the domain runs through the first constituent to the word constructing the second
theorem sum_crd_verbPhrase {c : ℕ × ℕ} (h : 1 ≤ c.1) :
    (Hawkins1994.crd (verbPhrase c)).sum = c.1 + 2 := by
  simp [verbPhrase, Hawkins1994.crd, Hawkins1994.crdTail, Hawkins1994.IC.words]
  omega

/-- Hawkins's recognition domain is longer with the theme first than with the goal first by the
heaviness predictor, the theme's excess in words: early immediate constituents grades the order
as end weight does. -/
theorem sum_crd_verbPhrase_sub_eq_heavyDiff {p : Pair} (h₁ : 1 ≤ p.1.words)
    (h₂ : 1 ≤ p.2.words) :
    ((Hawkins1994.crd (verbPhrase (p.1.words, p.2.words))).sum : ℝ) -
      (Hawkins1994.crd (verbPhrase (p.2.words, p.1.words))).sum = heavyDiff p := by
  rw [sum_crd_verbPhrase h₁, sum_crd_verbPhrase (c := (p.2.words, p.1.words)) h₂, heavyDiff]
  push_cast
  ring

/-- Hawkins's recognition domain covers four words in (5) and eleven in its unshifted order (4),
and five in (8) against four in the unshifted *That brings Barry Bonds to the plate*. -/
theorem crd_ex5_ex8 :
    (constituents Examples.ex_5).map (fun c ↦ ((Hawkins1994.crd (verbPhrase c)).sum,
      (Hawkins1994.crd (verbPhrase c.swap)).sum)) = some (4, 11) ∧
    (constituents Examples.ex_8).map (fun c ↦ ((Hawkins1994.crd (verbPhrase c)).sum,
      (Hawkins1994.crd (verbPhrase c.swap)).sum)) = some (5, 4) := by
  decide +kernel

/-! ### The paper's examples -/

theorem rows_heavier_last :
    ∀ r ∈ Examples.all, r.feature? "exception" = none →
      ∀ c ∈ (constituents r).toList, c.1 ≤ c.2 := by
  decide +kernel

-- (8) and (17)
theorem rows_exceptions_lighter_last :
    ∀ r ∈ Examples.all, (r.feature? "exception").isSome →
      ∀ c ∈ (constituents r).toList, c.2 < c.1 := by
  decide +kernel

end ArnoldEtAl2000
