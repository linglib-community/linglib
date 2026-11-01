module

public import Linglib.Data.Statistics.Schema

/-!
# DegenTonhauser2022: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/DegenTonhauser2022.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Six experiments on the content of the clausal complement of twenty English clause-embedding
predicates, crossing three diagnostics with two response tasks: projection by the certain-that
diagnostic on polar questions (Experiments 1a and 1b), and entailment by the inference diagnostic on
true statements (2a and 2b) and by the contradictoriness diagnostic on utterances that go on to deny
the complement (3a and 3b). The by-predicate means are plotted, not tabulated; for each experiment
the paper prints which predicates a Bayesian mixed-effects regression did not distinguish from the
reference controls.

## Raw data

* <https://github.com/judith-tonhauser/projective-probability>: materials, trial-level data and
  analysis code of all six experiments (footnote 14); the means are recomputed from
  results/5-projectivity-no-fact/data/cd.csv (1a) and results/8-projectivity-no-fact-
  binary/data/cd.csv (1b), which already apply the paper's participant exclusions

## References

* [degen-tonhauser-2022]
-/

@[expose] public section

namespace DegenTonhauser2022

open Data.Statistics

/-- The twenty clause-embedding predicates. -/
inductive Predicate where
  /-- acknowledge: a verb -/
  | acknowledge
  /-- admit: a verb -/
  | admit
  /-- announce: a verb -/
  | announce
  /-- be annoyed: an adjective with the copula -/
  | beAnnoyed
  /-- be right: an adjective with the copula -/
  | beRight
  /-- confess: a verb -/
  | confess
  /-- confirm: a verb -/
  | confirm
  /-- demonstrate: a verb -/
  | demonstrate
  /-- discover: a verb -/
  | discover
  /-- establish: a verb -/
  | establish
  /-- hear: a verb -/
  | hear
  /-- inform: a verb, its indirect object Sam in every stimulus -/
  | inform
  /-- know: a verb -/
  | know
  /-- pretend: a verb -/
  | pretend
  /-- prove: a verb -/
  | prove
  /-- reveal: a verb -/
  | reveal
  /-- say: a verb -/
  | say
  /-- see: a verb -/
  | see
  /-- suggest: a verb -/
  | suggest
  /-- think: a verb -/
  | think
  deriving DecidableEq, Repr, Fintype

/-- A category the predicates are typically taken to fall into. -/
inductive Category where
  /-- canonically factive: the complement is taken to be presupposed -/
  | canonicallyFactive
  /-- nonveridical nonfactive: the complement is taken to be neither presupposed nor entailed -/
  | nonveridicalNonfactive
  /-- veridical nonfactive: the complement is taken to be entailed but not presupposed -/
  | veridicalNonfactive
  /-- optionally factive: the complement can be presupposed -/
  | optionallyFactive
  deriving DecidableEq, Repr, Fintype

/-- The response task of an experiment. -/
inductive Task where
  /-- gradient: a slider from 'no' (0) to 'yes' (1); Experiments 1a, 2a and 3a -/
  | gradient
  /-- categorical: a forced choice of 'yes' (1) or 'no' (0); Experiments 1b, 2b and 3b -/
  | categorical
  deriving DecidableEq, Repr, Fintype

/-- A diagnostic for entailment. -/
inductive Diagnostic where
  /-- inference: whether the complement follows from a true statement of the matrix sentence;
  Experiments 2a and 2b -/
  | inference
  /-- contradictoriness: whether the matrix sentence followed by a denial of the complement is
  contradictory; Experiments 3a and 3b -/
  | contradictoriness
  deriving DecidableEq, Repr, Fintype

/-- A row of (13), p. 559: the predicates of a category. -/
structure ClassificationRow where
  /-- Its predicates, in the paper's order. -/
  predicates : List Predicate
  deriving DecidableEq, Repr

/-- The cells of (13), p. 559, by category; from an experiment; checked against the page images. -/
def classification : Category → ClassificationRow
  | .canonicallyFactive => ⟨[.beAnnoyed, .discover, .know, .reveal, .see]⟩
  | .nonveridicalNonfactive => ⟨[.pretend, .say, .suggest, .think]⟩
  | .veridicalNonfactive => ⟨[.beRight, .demonstrate]⟩
  | .optionallyFactive =>
    ⟨[.acknowledge, .admit, .announce, .confess, .confirm, .establish, .hear, .inform, .prove]⟩

/-- A row of Figures 2 and 4, pp. 562 and 565: the mean certainty rating of a predicate's
complement, the speaker taken to be certain of it. -/
structure CertaintyRow where
  /-- The mean rating. -/
  mean : Decimal
  deriving DecidableEq, Repr

/-- The cells of Figures 2 and 4, pp. 562 and 565, by task and predicate; from an experiment;
recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def certainty : Task → Predicate → CertaintyRow
  | .gradient, .acknowledge => ⟨⟨72, 2⟩⟩
  | .gradient, .admit => ⟨⟨66, 2⟩⟩
  | .gradient, .announce => ⟨⟨58, 2⟩⟩
  | .gradient, .beAnnoyed => ⟨⟨88, 2⟩⟩
  | .gradient, .beRight => ⟨⟨18, 2⟩⟩
  | .gradient, .confess => ⟨⟨64, 2⟩⟩
  | .gradient, .confirm => ⟨⟨34, 2⟩⟩
  | .gradient, .demonstrate => ⟨⟨49, 2⟩⟩
  | .gradient, .discover => ⟨⟨78, 2⟩⟩
  | .gradient, .establish => ⟨⟨36, 2⟩⟩
  | .gradient, .hear => ⟨⟨75, 2⟩⟩
  | .gradient, .inform => ⟨⟨81, 2⟩⟩
  | .gradient, .know => ⟨⟨86, 2⟩⟩
  | .gradient, .pretend => ⟨⟨15, 2⟩⟩
  | .gradient, .prove => ⟨⟨30, 2⟩⟩
  | .gradient, .reveal => ⟨⟨70, 2⟩⟩
  | .gradient, .say => ⟨⟨24, 2⟩⟩
  | .gradient, .see => ⟨⟨81, 2⟩⟩
  | .gradient, .suggest => ⟨⟨22, 2⟩⟩
  | .gradient, .think => ⟨⟨20, 2⟩⟩
  | .categorical, .acknowledge => ⟨⟨78, 2⟩⟩
  | .categorical, .admit => ⟨⟨67, 2⟩⟩
  | .categorical, .announce => ⟨⟨57, 2⟩⟩
  | .categorical, .beAnnoyed => ⟨⟨92, 2⟩⟩
  | .categorical, .beRight => ⟨⟨3, 2⟩⟩
  | .categorical, .confess => ⟨⟨58, 2⟩⟩
  | .categorical, .confirm => ⟨⟨16, 2⟩⟩
  | .categorical, .demonstrate => ⟨⟨31, 2⟩⟩
  | .categorical, .discover => ⟨⟨84, 2⟩⟩
  | .categorical, .establish => ⟨⟨19, 2⟩⟩
  | .categorical, .hear => ⟨⟨81, 2⟩⟩
  | .categorical, .inform => ⟨⟨90, 2⟩⟩
  | .categorical, .know => ⟨⟨93, 2⟩⟩
  | .categorical, .pretend => ⟨⟨7, 2⟩⟩
  | .categorical, .prove => ⟨⟨13, 2⟩⟩
  | .categorical, .reveal => ⟨⟨69, 2⟩⟩
  | .categorical, .say => ⟨⟨7, 2⟩⟩
  | .categorical, .see => ⟨⟨86, 2⟩⟩
  | .categorical, .suggest => ⟨⟨7, 2⟩⟩
  | .categorical, .think => ⟨⟨4, 2⟩⟩

/-- A row of §2.1, p. 563; §2.2, pp. 564–565: the predicates whose mean certainty rating the
regression did not distinguish from that of the main-clause controls, the 95% credible
interval for the difference containing 0. -/
structure ProjectionResult where
  /-- The predicates. -/
  indistinguishable : List Predicate
  deriving DecidableEq, Repr

/-- The cells of §2.1, p. 563; §2.2, pp. 564–565, by task; from an experiment; checked against
the page images. -/
def projectionResults : Task → ProjectionResult
  | .gradient => ⟨[]⟩
  | .categorical => ⟨[]⟩

/-- A row of §3.1, p. 571; §3.2, p. 573; §3.3, p. 576; §3.4, p. 577: the predicates whose mean
rating the regression did not distinguish from that of the controls with entailed content,
the 95% credible interval for the difference containing 0. -/
structure EntailmentResult where
  /-- The predicates, in the paper's order. -/
  indistinguishable : List Predicate
  deriving DecidableEq, Repr

/-- The cells of §3.1, p. 571; §3.2, p. 573; §3.3, p. 576; §3.4, p. 577, by diagnostic and task;
from an experiment; checked against the page images. -/
def entailmentResults : Diagnostic → Task → EntailmentResult
  | .inference, .gradient => ⟨[.prove, .beRight]⟩
  | .inference, .categorical => ⟨[.prove, .beRight, .know, .see, .discover, .confirm]⟩
  | .contradictoriness, .gradient => ⟨[]⟩
  | .contradictoriness, .categorical => ⟨[]⟩

end DegenTonhauser2022
