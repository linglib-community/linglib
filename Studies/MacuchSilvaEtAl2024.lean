module

public import Mathlib.Order.WithBot
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Macuch Silva, Lorson, Franke, Cummins and Rohde (2024): Strategic Use of English Quantifiers

This file formalizes the argumentative-difficulty account of [macuch-silva-etal-2024]. Two
experiments have English speakers describe exam results, a number of correct answers out of a
total, under the goal of presenting the outcome as a success or as a failure, with the four
quantifiers *all*, *most*, *some* and *none* in Experiment 1. The difficulty of framing a
result toward a goal is the distance of its proportion of correct answers from the goal's
ideal: the proportion itself for a failure framing and its complement for a success framing
(`difficulty`), so the two difficulties of one table sum to one (`difficulty_add`). The
account predicts that as difficulty grows the speaker retreats to informationally weaker
quantifiers, *all* giving way to *most* and then to *some*, those truthful over broader ranges
of outcomes: truth is inherited down the lexical scale (`Truthful.of_le`), the strongest
truthful quantifier for the goal-congruent adjective is monotone in the count it describes
(`strongest_mono`), and difficulty orders those counts the other way, so the strongest
truthful quantifier weakens with difficulty (`weakening_with_difficulty`). The paper thereby
extends the argumentative strength of [cummins-franke-2021] from a property of the speaker's
utterance to a property of the situation.

## Implementation notes

Proportions and difficulties are rationals. The positive quantifiers form the scale ⟨some,
most, all⟩, ordered by rank, and *none* is the bottom adjoined to it (`WithBot`): the strongest
truthful quantifier is *none* exactly when the count is zero. The paper's refined difficulty,
which also counts the students scoring zero, and the response probabilities of Figure 5 are
described in prose.

## References

* [macuch-silva-etal-2024]
* [cummins-franke-2021]
-/

@[expose] public section

namespace MacuchSilvaEtAl2024

/-- The framing goal: present the results as a success or as a failure. -/
inductive Goal where
  | highSuccess
  | lowSuccess
  deriving DecidableEq

/-- The adjective of the description frame, *N students got some questions right/wrong*. -/
inductive Adjective where
  | right
  | wrong
  deriving DecidableEq

/-- The adjective congruent with a goal: *right* for a success framing, *wrong* for a failure
framing. -/
def Goal.adjective : Goal → Adjective
  | .highSuccess => .right
  | .lowSuccess => .wrong

/-- An exam table: the number of correct answers out of the total. -/
structure ExamStimulus where
  nCorrect : ℕ
  nTotal : ℕ
  nCorrect_le : nCorrect ≤ nTotal
  nTotal_pos : 0 < nTotal

namespace ExamStimulus

variable (s s₁ s₂ : ExamStimulus)

/-- The proportion of correct answers. -/
def proportion : ℚ := s.nCorrect / s.nTotal

/-- The number of answers the adjective counts. -/
def count : Adjective → ℕ
  | .right => s.nCorrect
  | .wrong => s.nTotal - s.nCorrect

theorem count_le (a : Adjective) : s.count a ≤ s.nTotal := by
  have := s.nCorrect_le
  cases a <;> simp only [count] <;> omega

variable {s₁ s₂}

theorem proportion_le_proportion_iff (h : s₁.nTotal = s₂.nTotal) :
    s₁.proportion ≤ s₂.proportion ↔ s₁.nCorrect ≤ s₂.nCorrect := by
  unfold proportion
  rw [h, div_le_div_iff_of_pos_right (Nat.cast_pos.2 s₂.nTotal_pos), Nat.cast_le]

end ExamStimulus

open ExamStimulus

/-- Argumentative difficulty: the distance of the proportion from the goal's ideal, the
proportion itself under a failure framing and its complement under a success framing. -/
def difficulty (s : ExamStimulus) : Goal → ℚ
  | .highSuccess => 1 - s.proportion
  | .lowSuccess => s.proportion

theorem difficulty_add (s : ExamStimulus) :
    difficulty s .highSuccess + difficulty s .lowSuccess = 1 := by
  simp [difficulty]

theorem count_le_of_difficulty_le {s₁ s₂ : ExamStimulus} (g : Goal) (h : s₁.nTotal = s₂.nTotal)
    (hd : difficulty s₁ g ≤ difficulty s₂ g) : s₂.count g.adjective ≤ s₁.count g.adjective := by
  cases g
  · simp only [difficulty] at hd
    simp only [Goal.adjective, count]
    exact (proportion_le_proportion_iff h.symm).1 ((sub_le_sub_iff_left 1).1 hd)
  · have := (proportion_le_proportion_iff h).1 hd
    simp only [Goal.adjective, count]
    omega

/-! ### The quantifier scale -/

/-- The positive quantifiers of the experiment, the Horn scale ⟨some, most, all⟩. -/
inductive Quantifier where
  | some_
  | most
  | all
  deriving DecidableEq, Fintype

/-- The position of a quantifier on the scale. -/
def Quantifier.rank : Quantifier → ℕ
  | .some_ => 0
  | .most => 1
  | .all => 2

/-- The scale order: *some* below *most* below *all*. -/
instance : LinearOrder Quantifier := LinearOrder.lift' Quantifier.rank (by decide)

/-- The quantifier is truthful of the count the adjective describes. -/
def Truthful (s : ExamStimulus) (a : Adjective) : Quantifier → Prop
  | .all => s.count a = s.nTotal
  | .most => s.nTotal < 2 * s.count a
  | .some_ => 0 < s.count a

instance (s : ExamStimulus) (a : Adjective) : DecidablePred (Truthful s a) := λ q => by
  cases q <;> unfold Truthful <;> infer_instance

theorem Truthful.of_le {s : ExamStimulus} {a : Adjective} {q q' : Quantifier} (h : q' ≤ q)
    (hq : Truthful s a q) : Truthful s a q' := by
  have := s.nTotal_pos
  cases q <;> cases q' <;> simp only [Truthful] at hq ⊢ <;>
    first | omega | exact absurd h (by decide)

/-- The strongest truthful quantifier: *all* of a full count, *most* of a majority, *some* of
any positive count, and *none*, the bottom of the scale, otherwise. -/
def strongest (s : ExamStimulus) (a : Adjective) : WithBot Quantifier :=
  if s.count a = s.nTotal then ↑Quantifier.all
  else if s.nTotal < 2 * s.count a then ↑Quantifier.most
  else if 0 < s.count a then ↑Quantifier.some_
  else ⊥

theorem strongest_eq_bot_iff (s : ExamStimulus) (a : Adjective) :
    strongest s a = ⊥ ↔ s.count a = 0 := by
  have := s.nTotal_pos
  unfold strongest
  split_ifs <;> simp <;> omega

theorem strongest_truthful (s : ExamStimulus) (a : Adjective) {q : Quantifier}
    (h : strongest s a = ↑q) : Truthful s a q := by
  unfold strongest at h
  split_ifs at h with h1 h2 h3
  · cases WithBot.coe_inj.1 h; exact h1
  · cases WithBot.coe_inj.1 h; exact h2
  · cases WithBot.coe_inj.1 h; exact h3
  · exact absurd h WithBot.bot_ne_coe

theorem Truthful.le_strongest {s : ExamStimulus} {a : Adjective} {q : Quantifier}
    (hq : Truthful s a q) : ↑q ≤ strongest s a := by
  have := s.nCorrect_le
  have := s.nTotal_pos
  unfold strongest
  cases a <;> cases q <;> simp only [Truthful, count] at hq <;> split_ifs <;>
    first | exact WithBot.coe_le_coe.2 (by decide) | simp only [count] at * ; omega

/-- The strongest truthful quantifier is monotone in the count: more of the described answers,
a stronger quantifier. -/
theorem strongest_mono {s₁ s₂ : ExamStimulus} (a : Adjective) (h : s₁.nTotal = s₂.nTotal)
    (hc : s₁.count a ≤ s₂.count a) : strongest s₁ a ≤ strongest s₂ a := by
  have := s₁.count_le a
  have := s₂.count_le a
  unfold strongest
  split_ifs <;> first | exact bot_le | exact WithBot.coe_le_coe.2 (by decide) | omega

/-- Weakening with difficulty: between two tables of one size, the harder the framing toward a
goal, the weaker the strongest quantifier truthful of the goal-congruent count. -/
theorem weakening_with_difficulty {s₁ s₂ : ExamStimulus} (g : Goal) (h : s₁.nTotal = s₂.nTotal)
    (hd : difficulty s₁ g ≤ difficulty s₂ g) :
    strongest s₂ g.adjective ≤ strongest s₁ g.adjective :=
  strongest_mono _ h.symm (count_le_of_difficulty_le g h hd)

end MacuchSilvaEtAl2024
