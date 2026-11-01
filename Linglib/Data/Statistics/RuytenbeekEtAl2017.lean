module

public import Linglib.Data.Statistics.Schema

/-!
# RuytenbeekEtAl2017: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/RuytenbeekEtAl2017.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

A corpus count of two French interrogative requests and two eye-tracking studies in which
participants heard a sentence about a grid of shapes and either answered it with a yes/no (Study 1)
or true/false (Study 2) button or moved the shape it mentions. The response times are mixed-model
estimates with 95% confidence intervals; the interpretations table records the paper's verbal
findings, since the response proportions and fixation durations are only plotted, in figures this
manuscript does not contain. Page numbers are those of the authors' manuscript.

## Raw data

* <https://osf.io/s9mq8/>: the data of both studies, as the paper states; the project was not public
  when checked (2026-09-23)

## References

* [ruytenbeek-etal-2017]
-/

@[expose] public section

namespace RuytenbeekEtAl2017

open Data.Statistics

/-- The two experiments. -/
inductive Study where
  /-- 1: interrogatives against an imperative and a control question -/
  | one
  /-- 2: declaratives against an imperative and a control declarative -/
  | two
  deriving DecidableEq, Repr, Fintype

/-- The sentence types of the experiments, (17) to (27). -/
inductive Construction where
  /-- Imperative: Mettez le cercle rouge ... -/
  | imperative
  /-- Interrogative: Le cercle rouge est-il ...? -/
  | controlInterrogative
  /-- Can you: Pouvez-vous mettre ...? -/
  | canYou
  /-- Is it possible: Est-il possible de mettre ...? -/
  | isItPossible
  /-- You must: Vous devez mettre ... -/
  | youMust
  /-- You can: Vous pouvez mettre ... -/
  | youCan
  /-- It is possible: Il est possible de mettre ... -/
  | itIsPossible
  /-- Declarative: Le cercle rouge est ... -/
  | controlDeclarative
  deriving DecidableEq, Repr, Fintype

/-- The interrogative requests of the corpus count. -/
inductive Form where
  /-- Pouvez-vous VP ?: Can you VP?, with a singular addressee -/
  | pouvezVous
  /-- Est-il possible de VP ?: Is it possible to VP? -/
  | estIlPossible
  deriving DecidableEq, Repr, Fintype

/-- The response a response time measures. -/
inductive Response where
  /-- move: moving the shape the sentence mentions -/
  | move
  /-- yes: the yes button of Study 1 -/
  | yes
  deriving DecidableEq, Repr, Fintype

/-- How often a construction received directive interpretations, in the paper's words. -/
inductive Directiveness where
  /-- almost only: almost only directive interpretations -/
  | almostOnly
  /-- sometimes: directive interpretations beside dominant or many non-directive ones -/
  | sometimes
  /-- never: no directive interpretations -/
  | never
  deriving DecidableEq, Repr, Fintype

/-- A yes-or-no finding. -/
inductive Answer where
  /-- yes: yes -/
  | yes
  /-- no: no -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- A row of section 2.1, manuscript p. 7: the Frantext tokens after 1900 of an interrogative
request and the percentage coded as each use. -/
structure CorpusCount where
  /-- The number of tokens. -/
  tokens : ℕ
  /-- The percentage coded as indirect requests. -/
  indirectRequest : ℕ
  /-- The percentage coded as genuine questions. -/
  genuineQuestion : ℕ
  /-- The percentage coded as rhetorical questions. -/
  rhetoricalQuestion : ℕ
  deriving DecidableEq, Repr

/-- The cells of section 2.1, manuscript p. 7, by form; counted in a corpus; checked against the
page images. -/
def corpus : Form → CorpusCount
  | .pouvezVous => ⟨365, 71, 25, 4⟩
  | .estIlPossible => ⟨63, 16, 70, 14⟩

/-- A row of sections 2.3 and 3.3, manuscript pp. 11 and 15: the model estimate of the response
time of a response to a construction, with its 95% confidence interval, in milliseconds. -/
structure ResponseTime where
  /-- The study. -/
  study : Study
  /-- The construction. -/
  construction : Construction
  /-- The response. -/
  response : Response
  /-- The estimate. -/
  estimate : ℕ
  /-- The lower bound of the confidence interval, as printed. -/
  ciLow : ℕ
  /-- The upper bound, as printed. -/
  ciHigh : ℕ
  deriving DecidableEq, Repr

/-- The 10 rows of sections 2.3 and 3.3, manuscript pp. 11 and 15, in the paper's order; from an
experiment; checked against the page images. -/
def responseTimes : List ResponseTime :=
  [⟨.one, .imperative, .move, 2833, 2500, 3165⟩,
   ⟨.one, .canYou, .move, 2990, 25345, 3635⟩,  -- lower bound printed 25345, above the estimate
   ⟨.one, .isItPossible, .move, 2878, 2237, 3518⟩,
   ⟨.one, .controlInterrogative, .yes, 3707, 3194, 4221⟩,
   ⟨.one, .canYou, .yes, 4729, 4162, 5296⟩,
   ⟨.one, .isItPossible, .yes, 4409, 3903, 4916⟩,
   ⟨.two, .youMust, .move, 3133, 2675, 3591⟩,
   ⟨.two, .imperative, .move, 2953, 2509, 3397⟩,
   ⟨.two, .youCan, .move, 3146, 2590, 3701⟩,
   ⟨.two, .itIsPossible, .move, 3184, 2570, 3797⟩]

/-- A row of sections 2.3-2.4 and 3.3-3.4, manuscript pp. 10-11 and 14-15: how often a
construction received directive interpretations, and whether those drew fixations on the
answer buttons or response times above the imperative's. -/
structure Interpretation where
  /-- The study. -/
  study : Study
  /-- The construction. -/
  construction : Construction
  /-- How often it was interpreted as a directive. -/
  directive : Directiveness
  /-- Whether its directive interpretations showed activity toward answering: fixations on the
  answer buttons or longer response times than the imperative; none when it had none. -/
  answerActivity : Option Answer
  deriving DecidableEq, Repr

/-- The 9 rows of sections 2.3-2.4 and 3.3-3.4, manuscript pp. 10-11 and 14-15, in the paper's
order; from an experiment; checked against the page images. -/
def interpretations : List Interpretation :=
  [⟨.one,  -- the control directive; its fixations and response times are the baseline
     .imperative,
     .almostOnly,
     some .no⟩,
   ⟨.one,  -- the control question, from the design; its yes responses are the question baseline
     .controlInterrogative,
     .never,
     none⟩,
   ⟨.one, .canYou, .sometimes, some .no⟩,
   ⟨.one, .isItPossible, .sometimes, some .no⟩,
   ⟨.two, .youMust, .almostOnly, some .no⟩,
   ⟨.two, .imperative, .almostOnly, some .no⟩,  -- nine true/false responses excluded
   ⟨.two, .youCan, .sometimes, some .no⟩,
   ⟨.two, .itIsPossible, .sometimes, some .no⟩,
   ⟨.two, .controlDeclarative, .never, none⟩]  -- the control statement, from the design

end RuytenbeekEtAl2017
