module

public import Linglib.Phonology.HarmonicGrammar.IntersectingFamilies
public import Linglib.Discourse.Givenness
public import Linglib.Data.Examples.ArnoldEtAl2000
public import Linglib.Data.Examples.Readers
public import Studies.Hawkins1994
public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
public import Linglib.Core.Analysis.SpecialFunctions.Sigmoid.Difference

/-!
# Arnold, Losongco, Wasow and Ginstrom (2000): Heaviness vs. Newness

This file models the order of two postverbal constituents in heavy NP shift and the English
dative alternation as [the paper's logistic regression](##themeLastProb_eq): end weight and given
before new read the constituents in the order spoken, a cost of the theme-last order is the
intercept, and the theme comes last with probability $\sigma(w_H h + w_N n - w_B)$ for the
differences $h$ in words and $n$ in newness. [Neither factor reduces to the
other](##factorsThrough_heavyDiff_iff) and [they do not interact in the
log-odds](##interaction_logit_eq_zero), yet [newness matters most where the rest predicts
least](##themeLastProb_new_sub_given_lt_iff). [Hawkins's recognition domain grades the order as
end weight does](##sum_crd_verbPhrase_sub), [as the paper counts](##crd_ex5_ex8).

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

/-- A candidate's two constituents in the order spoken. -/
def linearize : Candidate → Phrase × Phrase
  | ((th, gl), .themeLast) => (gl, th)
  | (p, .goalLast) => p

/-- End weight, Behaghel's law ([behaghel-1909]), on the lengths of two constituents in the order
spoken: the words by which the first exceeds the second. -/
def heavyFirst : Constraint (ℕ × ℕ) := fun c ↦ c.1 - c.2

/-- Given before new, on the statuses of two constituents in the order spoken: a new constituent
before a given one. -/
def newFirst : Constraint (BinaryGivenness × BinaryGivenness) :=
  Constraint.binary (· = (.new, .given))

/-- The construction's own cost: a violation for the theme-last order whatever the
constituents, the intercept of the paper's regressions. -/
def starThemeLast : Constraint Candidate := Constraint.binary (·.2 = .themeLast)

/-- End weight and given before new read the constituents in the order spoken, the
construction's cost the order itself. -/
def con : ConstraintSet Candidate (Fin 3) :=
  ![heavyFirst ∘ Prod.map Phrase.words Phrase.words ∘ linearize,
    newFirst ∘ Prod.map Phrase.discourse Phrase.discourse ∘ linearize, starThemeLast]

/-- The weights: `wH` for heaviness, `wN` for newness, `wB` for the construction's baseline. -/
def weights (wH wN wB : ℝ) : Fin 3 → ℝ := ![wH, wN, wB]

/-- The probability of the theme-last order of a pair. -/
noncomputable def themeLastProb (wH wN wB : ℝ) (p : Pair) : ℝ :=
  (maxEnt (con.comap (p, ·)).violations (weights wH wN wB)).real {.themeLast}

/-- The heaviness predictor: the theme's length minus the goal's. -/
def heavyDiff (p : Pair) : ℝ := (p.1.words : ℝ) - p.2.words

/-- The newness predictor: the violations of given before new with the theme first less those
with the goal first, `1` when the theme is new and the goal given, `-1` in the mirror case, `0`
otherwise. -/
def newDiff (p : Pair) : ℝ :=
  (newFirst (p.1.discourse, p.2.discourse) : ℝ) - newFirst (p.2.discourse, p.1.discourse)

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
  simp only [con, weights, harmonyScore_cons, harmonyScore_nil, Function.comp_apply, linearize,
    Prod.map, heavyFirst, starThemeLast, Constraint.binary_apply, heavyDiff, newDiff,
    reduceCtorEq, ite_true, ite_false]
  push_cast
  linear_combination wH * h

-- the paper's logistic regression on the heaviness and newness predictors, with an intercept
theorem themeLastProb_eq (p : Pair) :
    themeLastProb wH wN wB p = sigmoid (wH * heavyDiff p + wN * newDiff p - wB) := by
  rw [themeLastProb, maxEnt_real_singleton_of_pair _ _ (a := Order.themeLast) (b := .goalLast)
    (by decide) (by decide), harmony_violations, harmonyScore_comap, harmonyScore_comap,
    harmonyScore_themeLast_sub]

theorem logit_themeLastProb (p : Pair) :
    logit (themeLastProb wH wN wB p) =
      harmonyScore con (weights wH wN wB) (p, .themeLast) -
        harmonyScore con (weights wH wN wB) (p, .goalLast) := by
  rw [themeLastProb_eq, logit_sigmoid, harmonyScore_themeLast_sub]

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
  simpa [themeLastProb_eq, heavyDiff, newDiff, newFirst] using
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

/-- Newness and heaviness do not interact in the log-odds of the theme-last order, as in the
corpus regressions; the experiment's interaction lies outside the grammar. -/
theorem interaction_logit_eq_zero (l l' : ℕ × ℕ) (s s' : BinaryGivenness × BinaryGivenness) :
    (cross l l' s s').interaction (fun p ↦ logit (themeLastProb wH wN wB p)) = 0 := by
  simpa only [logit_themeLastProb] using
    (independent_cross l l' s s').interaction_harmonyScore_sub (weights wH wN wB)

/-- Newness raises the probability of the theme-last order the more, the weaker the prediction
that heaviness and the construction's baseline make without it: the pattern of the corpus
figures, which the paper reads as interacting constraints. -/
theorem themeLastProb_new_sub_given_lt_iff (hN : 0 < wN) (m n m' n' : ℕ) :
    themeLastProb wH wN wB (⟨m', .new⟩, ⟨n', .given⟩) -
        themeLastProb wH wN wB (⟨m', .given⟩, ⟨n', .new⟩) <
      themeLastProb wH wN wB (⟨m, .new⟩, ⟨n, .given⟩) -
        themeLastProb wH wN wB (⟨m, .given⟩, ⟨n, .new⟩) ↔
      |wH * ((m : ℝ) - n) - wB| < |wH * ((m' : ℝ) - n') - wB| := by
  have hnew (k l : ℕ) : themeLastProb wH wN wB (⟨k, .new⟩, ⟨l, .given⟩) =
      sigmoid (wH * ((k : ℝ) - l) - wB + wN) := by
    rw [themeLastProb_eq]
    congr 1
    simp [heavyDiff, newDiff, newFirst]
    ring
  have hgiven (k l : ℕ) : themeLastProb wH wN wB (⟨k, .given⟩, ⟨l, .new⟩) =
      sigmoid (wH * ((k : ℝ) - l) - wB - wN) := by
    rw [themeLastProb_eq]
    congr 1
    simp [heavyDiff, newDiff, newFirst]
    ring
  have h2 (c : ℝ) : c + wN + (c - wN) = 2 * c := by ring
  rw [hnew, hgiven, hnew, hgiven, sigmoid_sub_sigmoid_lt_sigmoid_sub_sigmoid_iff (by ring)
    (by linarith), h2, h2, abs_mul, abs_mul, abs_two, mul_lt_mul_iff_right₀ two_pos]

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
  simp only [newDiff, heavyDiff, newFirst, Constraint.binary_apply, hth, hgl, sub_self,
    Prod.mk.injEq, reduceCtorEq, and_self, ite_true, ite_false]
  push_cast
  linarith [mul_le_mul_of_nonneg_left hd hH]

/-! ### Hawkins's recognition domain -/

/-- The number of words in a constituent as printed. -/
def wordCount (s : String) : ℕ := (s.toList.filter (· = ' ')).length + 1

/-- The lengths of a row's two constituents in the order printed. -/
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

/-- Hawkins's recognition domain of an order exceeds that of the reverse order by the end weight
it violates beyond the reverse: early immediate constituents grades the order as end weight
does. -/
theorem sum_crd_verbPhrase_sub {c : ℕ × ℕ} (h₁ : 1 ≤ c.1) (h₂ : 1 ≤ c.2) :
    ((Hawkins1994.crd (verbPhrase c)).sum : ℤ) - (Hawkins1994.crd (verbPhrase c.swap)).sum =
      heavyFirst c - heavyFirst c.swap := by
  rw [sum_crd_verbPhrase h₁, sum_crd_verbPhrase (c := c.swap) h₂]
  simp only [heavyFirst, Prod.fst_swap, Prod.snd_swap]
  omega

/-- Hawkins's recognition domain covers four words in (5) and eleven in its unshifted order (4),
and five in (8) against four in the unshifted *That brings Barry Bonds to the plate*. -/
theorem crd_ex5_ex8 :
    (constituents Examples.ex_5).map (fun c ↦ ((Hawkins1994.crd (verbPhrase c)).sum,
      (Hawkins1994.crd (verbPhrase c.swap)).sum)) = some (4, 11) ∧
    (constituents Examples.ex_8).map (fun c ↦ ((Hawkins1994.crd (verbPhrase c)).sum,
      (Hawkins1994.crd (verbPhrase c.swap)).sum)) = some (5, 4) := by
  decide +kernel

/-! ### The paper's examples -/

-- the printed orders satisfy end weight
theorem rows_heavyFirst_eq_zero :
    ∀ r ∈ Examples.all, r.feature? "exception" = none →
      ∀ c ∈ (constituents r).toList, heavyFirst c = 0 := by
  decide +kernel

-- but for (8) and (17)
theorem rows_heavyFirst_pos :
    ∀ r ∈ Examples.all, (r.feature? "exception").isSome →
      ∀ c ∈ (constituents r).toList, 0 < heavyFirst c := by
  decide +kernel

end ArnoldEtAl2000
