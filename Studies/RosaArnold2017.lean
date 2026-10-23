module

public import Linglib.Data.Examples.RosaArnold2017
public import Linglib.Data.Experiments.RosaArnold2017
public import Linglib.Fragments.English.Pronouns
public import Linglib.Morphology.Word.Agree
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith

/-!
# Rosa and Arnold (2017): Predictability affects production

This file formalizes [rosa-arnold-2017]'s test of whether the predictability of a referent
affects the speaker's choice of a pronoun. Transfer verbs separate thematic role from
grammatical role, since *get* and *take* put the goal in subject position while *give* and
*hand* put it in a nonsubject position, so the design crosses the role of the continued
character with its grammatical role and with the gender contrast of the character pair, and a
rating study finds the goal expected as the next mention well above the source while subjects
are not expected above nonsubjects. The expectancy hypothesis of [arnold-2001] predicts more
pronouns for goals; the topicality account of [kehler-rohde-2013] and
[fukumura-van-gompel-2010] predicts that thematic role leaves the production probability
untouched once grammatical role is fixed. The production probability is a logistic model over
the design, the paper's regression with its two main effects: `topical_iff` states the
topicality account as the vanishing of the thematic effect, and `source_subject_gt_goal_iff`
shows that a subject source pronominalized above a nonsubject goal, the earlier finding taken as
evidence against predictability, is consistent with a positive thematic effect whenever the
subject effect exceeds it. The pronoun rates of the three experiments and the rating study are
`Data/Experiments/RosaArnold2017`; `topical_not_fits` reads the Experiment 1 contrast at fixed
grammatical role and `goal_expected` the rating study. The effect sizes, the marginal
amplification of the goal effect under Occasion and Result continuations in Experiment 2, and
the shorter latencies for goal continuations stay in prose.

## Implementation notes

* A model fits a table of rates when its log-odds order the cells as the rates do, which the
  logistic link guarantees for population rates.
* The gender contrast of an item is derived from the characters' φ-features: a pronoun is
  ambiguous exactly when the two characters agree.

## References

* [rosa-arnold-2017]
* [arnold-2001]
* [kehler-rohde-2013]
* [fukumura-van-gompel-2010]
-/

@[expose] public section

namespace RosaArnold2017

open Morphology

/-! ### The design -/

/-- A cell of the design. -/
structure Cell where
  role : Role
  gram : Gram
  gender : Gender
  deriving DecidableEq, Repr, Fintype

/-- The gender contrast of a pair of characters: `same` exactly when their φ-features agree,
the pairs a third-person singular pronoun cannot tell apart. -/
def Gender.ofPair (w₁ w₂ : Word) : Gender := if HasPhi.Agree w₁ w₂ then .same else .different

/-- Lisa, of *Lisa gave the leftover pie to Brendan*. -/
def lisa : Word :=
  ⟨"Lisa", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .feminine)⟩

/-- Brendan. -/
def brendan : Word :=
  ⟨"Brendan", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .masculine)⟩

theorem lisa_brendan :
    Gender.ofPair lisa brendan = .different ∧
      English.Pronouns.she.toPronoun.CandidateAntecedent lisa ∧
      ¬ English.Pronouns.she.toPronoun.CandidateAntecedent brendan := by
  decide

/-! ### The production model

The regressions predict the log-odds of a pronoun from subjecthood and thematic role. -/

/-- A logistic production model over the design: the log-odds of a pronoun as a baseline plus
a subject effect and a goal effect. -/
structure Model where
  base : ℚ
  subject : ℚ
  goal : ℚ

/-- The log-odds of a pronoun in a cell. -/
def Model.logit (M : Model) (c : Cell) : ℚ :=
  M.base + (if c.gram = .subject then M.subject else 0) + (if c.role = .goal then M.goal else 0)

/-- The topicality account: production is insensitive to thematic role. -/
def Model.Topical (M : Model) : Prop := M.goal = 0

theorem topical_iff (M : Model) :
    M.Topical ↔ ∀ g d, M.logit ⟨.goal, g, d⟩ = M.logit ⟨.source, g, d⟩ := by
  unfold Model.Topical
  constructor
  · intro h g d; simp [Model.logit, h]
  · intro h; simpa [Model.logit] using h .nonsubject .same

theorem source_subject_gt_goal_iff (M : Model) (d : Gender) :
    M.logit ⟨.goal, .nonsubject, d⟩ < M.logit ⟨.source, .subject, d⟩ ↔ M.goal < M.subject := by
  simp [Model.logit]

/-- A model fits a table of rates when its log-odds order the cells as the rates do. -/
def Model.Fits (M : Model) (r : Cell → ℕ) : Prop :=
  ∀ c c', M.logit c < M.logit c' ↔ r c < r c'

/-! ### The findings -/

/-- The rate of pronoun production in a cell of an experiment (Tables 1, 4, 7), in percent. -/
def rate (x : Experiment) (c : Cell) : ℕ := (rates x c.gender c.gram c.role).pronouns

theorem goal_expected : 50 < goalNextMention ∧ subjectNextMention < goalNextMention := by
  decide

theorem topical_not_fits (M : Model) (hM : M.Topical) : ¬ M.Fits (rate .retelling) := by
  intro hf
  have h := (topical_iff M).1 hM .subject .different
  have hlt := (hf ⟨.source, .subject, .different⟩ ⟨.goal, .subject, .different⟩).2
    (by decide +kernel)
  rw [h] at hlt
  exact lt_irrefl _ hlt

end RosaArnold2017
