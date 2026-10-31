module

public import Linglib.Data.Examples.RosaArnold2017
public import Linglib.Data.Experiments.RosaArnold2017
public import Linglib.Fragments.English.Pronouns
public import Linglib.Morphology.Word.Agree
public import Studies.KehlerRohde2013
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.Linarith
public import Linglib.Data.Examples.Readers

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
grammatical role and `goal_expected` the rating study. In Experiment 2 the goal effect is
significant only in Occasion and Result continuations, the group whose relations focus the end
state of the previous event, which are the relations where Kehler and Rohde's interpretation is
Goal-biased (`goalEffects_significant_iff_goalBiased`), though the interaction itself is marginal
(`not_coherenceInteraction_significant`). The effect sizes and the shorter latencies for goal
continuations stay in prose.

## Implementation notes

* A model fits a table of rates when its log-odds order the cells as the rates do, which the
  logistic link guarantees for population rates.
* The gender contrast of an item is derived from the characters' φ-features: a pronoun is
  ambiguous exactly when the two characters agree.
* The Occasion/Result group is the paper's, motivated by the end-state reasoning that Kehler and
  Rohde also use; what the two studies share is that interpretation and production split along
  it.

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
    Features.of (person := some .third) (number := some .singular) (gender := some .Fem)⟩

/-- Brendan. -/
def brendan : Word :=
  ⟨"Brendan", .PROPN,
    Features.of (person := some .third) (number := some .singular) (gender := some .Masc)⟩

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

/-! ### Coherence and the goal effect (Experiment 2) -/

/-- The coherence codes in Kehler's classification, Background having no counterpart there. -/
def CoherenceCode.toCoherence : CoherenceCode → Option Discourse.Coherence.Relation
  | .elaboration => some .elaboration
  | .explanation => some .explanation
  | .occasion => some .occasion
  | .parallel => some .parallel
  | .result => some .result
  | .violatedExpectation => some .violatedExpectation
  | .background => none

/-- The code of each of Kehler and Rohde's five relations. -/
def codeOf : KehlerRohde2013.Relation → CoherenceCode
  | .occasion => .occasion
  | .elaboration => .elaboration
  | .explanation => .explanation
  | .violatedExpectation => .violatedExpectation
  | .result => .result

theorem coherenceGroups_eq_occasionResult_iff (c : CoherenceCode) :
    (coherenceGroups c).group = .occasionResult ↔
      ∃ r ∈ c.toCoherence, KehlerRohde2013.FocusesEndState r := by
  cases c <;> decide

theorem goalEffects_significant_iff (g : CoherenceGroup) :
    (goalEffects g).p.Significant (1 / 20) ↔ g = .occasionResult := by
  revert g; decide +kernel

theorem not_coherenceInteraction_significant :
    ¬ (coherenceInteraction[0]'(by decide)).p.Significant (1 / 20) := by
  decide +kernel

/-- Across the five relations both studies code, the goal effect on production is significant
exactly where Kehler and Rohde's interpretation is Goal-biased, both following the end state. -/
theorem goalEffects_significant_iff_goalBiased (k : KehlerRohde2013.Relation) :
    (goalEffects (coherenceGroups (codeOf k)).group).p.Significant (1 / 20) ↔
      KehlerRohde2013.perfectiveSourceGiven k < 50 := by
  rw [goalEffects_significant_iff, coherenceGroups_eq_occasionResult_iff,
    KehlerRohde2013.goalBiased_iff_focusesEndState]
  cases k <;> simp [codeOf, CoherenceCode.toCoherence, KehlerRohde2013.Relation.toCoherence]

end RosaArnold2017
