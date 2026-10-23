module

public import Linglib.Phonology.HarmonicGrammar.Harmony
public import Linglib.Discourse.Givenness
public import Linglib.Data.Examples.ArnoldEtAl2000
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Arnold, Wasow, Losongco & Ginstrom 2000: heaviness vs. newness

Postverbal constituent order in English — heavy NP shift and the dative alternation — has
been attributed to grammatical weight (Behaghel's law of growing constituents) and to
discourse status (given before new), but the two are confounded: given referents get short
expressions and new ones long. A corpus study of the Aligned-Hansard debates and an
elicitation experiment in which directors instruct actors to give objects to toy animals
measure heaviness as the difference in word count between the two constituents and newness
by prior mention, and find that both factors independently shift the order, the newer and
heavier constituent coming later, with neither reducible to the other. Their relative
strength varies with the data: heaviness dominates where length differences are large,
newness where the given referent has just been mentioned — a system of interacting
constraints whose strength grows as the competing constraint weakens. Speakers' early
disfluencies favour goal-first orders, so the postponement of new and heavy material serves
planning as well as comprehension.

The two factors are read as weighted constraints over the two orders of a constituent pair:
a graded penalty for putting the heavier constituent first, sized by the length difference the
paper measures, and a penalty for putting a new constituent before a given one. The harmony
difference between the orders is the weighted sum of the two signed preferences, which is
the additive independence the paper reports; the paper's interaction is a matter of effect
size in the data and is not represented.

## Main definitions

* `Phrase`, `Pair`, `Order`: a constituent by word count and givenness, a postverbal pair,
  and which constituent comes last.
* `heavyFirst`, `newFirst`: the two constraints; `con` their weighted family.
* `heavyDiff`, `newDiff`: each constraint's signed preference for the theme-last order.

## References

* [arnold-losongco-wasow-ginstrom-2000]
* [behaghel-1909] — the law of growing constituents
* [prince-1992] — discourse-given, inferable, and new
-/

@[expose] public section

namespace ArnoldEtAl2000

open OptimalityTheory HarmonicGrammar Discourse

/-! ### Phrases, orderings, and candidates -/

/-- A constituent by the two measures the paper codes: word count and discourse status. -/
structure Phrase where
  words : ℕ
  discourse : BinaryGivenness
  deriving DecidableEq

/-- A postverbal pair: theme and goal for the dative alternation, direct object and PP for
heavy NP shift. -/
abbrev Pair := Phrase × Phrase

/-- Which constituent comes last: `themeLast` is the double object or the shifted order,
`goalLast` the prepositional dative or the canonical order. -/
inductive Order
  | themeLast
  | goalLast
  deriving DecidableEq

abbrev Candidate := Pair × Order

/-! ### The two constraints -/

/-- The weight penalty: the number of words by which the first constituent exceeds the
second — the relative length the paper measures. -/
def heavyFirst : Constraint Candidate
  | ((th, gl), .themeLast) => gl.words - th.words
  | ((th, gl), .goalLast) => th.words - gl.words

/-- The newness penalty: a new constituent before a given one. -/
def newFirst : Constraint Candidate
  | ((th, gl), .themeLast) => if gl.discourse = .new ∧ th.discourse = .given then 1 else 0
  | ((th, gl), .goalLast) => if th.discourse = .new ∧ gl.discourse = .given then 1 else 0

/-- The two constraints. -/
def con : ConstraintSet Candidate (Fin 2) := ![heavyFirst, newFirst]

/-- The weights: `wH` for heaviness, `wN` for newness. -/
def weights (wH wN : ℝ) : Fin 2 → ℝ := ![wH, wN]

/-! ### Signed preferences -/

/-- Heaviness's preference for `themeLast`: the theme's length minus the goal's. -/
def heavyDiff (p : Pair) : ℝ := (p.1.words : ℝ) - p.2.words

/-- Newness's preference for `themeLast`: `1` when the theme is new and the goal given, `-1`
in the mirror case, `0` otherwise. -/
def newDiff (p : Pair) : ℝ :=
  (if p.1.discourse = .new ∧ p.2.discourse = .given then (1 : ℝ) else 0) -
    (if p.2.discourse = .new ∧ p.1.discourse = .given then (1 : ℝ) else 0)

theorem cast_sub_sub_cast_sub (a b : ℕ) : ((a - b : ℕ) : ℝ) - ((b - a : ℕ) : ℝ) = a - b := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring

/-- The harmony difference between the two orders is the weighted sum of the two signed
preferences. -/
theorem score_diff_eq_components (wH wN : ℝ) (p : Pair) :
    harmonyScore con (weights wH wN) (p, .themeLast) -
      harmonyScore con (weights wH wN) (p, .goalLast) = wH * heavyDiff p + wN * newDiff p := by
  obtain ⟨th, gl⟩ := p
  rw [harmonyScore_eq_neg_sum, harmonyScore_eq_neg_sum]
  simp only [con, weights, heavyFirst, newFirst, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h := cast_sub_sub_cast_sub th.words gl.words
  unfold heavyDiff newDiff
  push_cast
  linear_combination wH * h

/-- The theme-last order wins exactly when the weighted preferences sum in its favour. -/
theorem themeLast_iff (wH wN : ℝ) (p : Pair) :
    harmonyDominates con (weights wH wN) (p, .themeLast) (p, .goalLast) ↔
      0 < wH * heavyDiff p + wN * newDiff p := by
  rw [harmonyDominates_iff, ← sub_pos, score_diff_eq_components]

/-! ### Independence -/

theorem heaviness_alone {wH : ℝ} (hH : 0 < wH) (p : Pair) :
    harmonyDominates con (weights wH 0) (p, .themeLast) (p, .goalLast) ↔
      p.2.words < p.1.words := by
  rw [themeLast_iff, zero_mul, add_zero, mul_pos_iff_of_pos_left hH, heavyDiff, sub_pos,
    Nat.cast_lt]

theorem newness_alone {wN : ℝ} (hN : 0 < wN) (p : Pair) :
    harmonyDominates con (weights 0 wN) (p, .themeLast) (p, .goalLast) ↔
      p.1.discourse = .new ∧ p.2.discourse = .given := by
  rw [themeLast_iff, zero_mul, zero_add, mul_pos_iff_of_pos_left hN, newDiff]
  split_ifs <;> simp_all

theorem score_diff_add_word (wH wN : ℝ) (th gl : Phrase) :
    harmonyScore con (weights wH wN) (({ th with words := th.words + 1 }, gl), .themeLast) -
        harmonyScore con (weights wH wN) (({ th with words := th.words + 1 }, gl), .goalLast) =
      harmonyScore con (weights wH wN) ((th, gl), .themeLast) -
        harmonyScore con (weights wH wN) ((th, gl), .goalLast) + wH := by
  rw [score_diff_eq_components, score_diff_eq_components]
  simp only [heavyDiff, newDiff]
  push_cast
  ring

theorem one_factor_decides (wH wN : ℝ) (p : Pair) :
    (newDiff p = 0 → (harmonyDominates con (weights wH wN) (p, .themeLast) (p, .goalLast) ↔
      0 < wH * heavyDiff p)) ∧
    (heavyDiff p = 0 → (harmonyDominates con (weights wH wN) (p, .themeLast) (p, .goalLast) ↔
      0 < wN * newDiff p)) :=
  ⟨fun h => by rw [themeLast_iff, h, mul_zero, add_zero],
    fun h => by rw [themeLast_iff, h, mul_zero, zero_add]⟩

/-! ### The paper's examples -/

/-- The number of words in a constituent as printed. -/
def words (s : String) : ℕ := (s.toList.filter (· = ' ')).length + 1

/-- The word counts of a row's two constituents in surface order. -/
def constituents (r : Datum) : Option (ℕ × ℕ) := do
  let a ← r.feature? "first"
  let b ← r.feature? "second"
  pure (words a, words b)

theorem rows_heavier_last :
    ∀ r ∈ Examples.all, r.feature? "exception" = none →
      ∀ c ∈ (constituents r).toList, c.1 ≤ c.2 := by
  decide +kernel

/-- The examples the paper sets aside — the announcer's *That brings to the plate Barry
Bonds* and (17) — put the lighter constituent last: other factors, planning among them. -/
theorem rows_exceptions_lighter_last :
    ∀ r ∈ Examples.all, (r.feature? "exception").isSome →
      ∀ c ∈ (constituents r).toList, c.2 < c.1 := by
  decide +kernel

end ArnoldEtAl2000
