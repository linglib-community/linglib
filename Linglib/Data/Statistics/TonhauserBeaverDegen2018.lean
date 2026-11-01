module

public import Linglib.Data.Statistics.Schema

/-!
# TonhauserBeaverDegen2018: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/TonhauserBeaverDegen2018.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Four rating experiments on the projectivity and at-issueness of 19 projective contents of American
English: the content of 9 syntactically heterogeneous expressions (Experiments 1a and 2a) and of the
clausal complements of 12 attitude predicates (Experiments 1b and 2b). Experiments 1a and 1b
measured projectivity by the certain-that question and at-issueness by the asking-whether question
on a no-yes slider, each stimulus a polar question; responses were coded so that 1 is projecting and
not-at-issue. Experiments 2a and 2b re-measured at-issueness by an Are-you-sure dissent diagnostic
on indicative stimuli. The by-expression means are plotted, not tabulated; the paper prints the
mixed-effects estimates, the correlations, two Tukey pairwise-comparison tables and a summary table.

## Raw data

* <https://github.com/judith-tonhauser/how-projective>: materials, trial-level data and analysis
  scripts of all four experiments (footnote 8); the by-expression means and the main-clause controls
  are recomputed from results/exp1a/data/data_preprocessed.csv and
  results/exp1b/data/data_preprocessed.csv, which already apply the paper's participant exclusions

## References

* [tonhauser-beaver-degen-2018]
-/

@[expose] public section

namespace TonhauserBeaverDegen2018

open Data.Statistics

/-- The four experiments. -/
inductive Experiment where
  /-- 1a: heterogeneous expressions, asking-whether at-issueness -/
  | exp1a
  /-- 1b: clause-embedding predicates, asking-whether at-issueness -/
  | exp1b
  /-- 2a: heterogeneous expressions, dissent at-issueness -/
  | exp2a
  /-- 2b: clause-embedding predicates, dissent at-issueness -/
  | exp2b
  deriving DecidableEq, Repr, Fintype

/-- The nine heterogeneous target expressions of Experiments 1a and 2a, with their projective
content. -/
inductive Expression where
  /-- NRRC: sentence-medial non-restrictive relative clause; its content -/
  | nrrc
  /-- nominal appositive: sentence-medial nominal appositive; the appositive content -/
  | nominalAppositive
  /-- possessive NP: possessive noun phrase; the possession implication -/
  | possessiveNP
  /-- be annoyed: the content of the clausal complement -/
  | annoyed
  /-- discover: the content of the clausal complement -/
  | discover
  /-- know: the content of the clausal complement -/
  | know
  /-- only: the prejacent -/
  | only
  /-- stop: the pre-state implication -/
  | stop
  /-- be stupid to: the content of the infinitival complement -/
  | stupid
  deriving DecidableEq, Repr, Fintype

/-- The twelve clause-embedding predicates of Experiments 1b and 2b; the content is that of the
clausal complement. -/
inductive Predicate where
  /-- be annoyed: emotive factive -/
  | annoyed
  /-- notice: semi-factive -/
  | notice
  /-- be aware: factive -/
  | aware
  /-- realize: semi-factive -/
  | realize
  /-- be amused: emotive factive -/
  | amused
  /-- see: semi-factive -/
  | see
  /-- find out: semi-factive -/
  | findOut
  /-- learn: semi-factive -/
  | learn
  /-- discover: semi-factive -/
  | discover
  /-- reveal: non-factive -/
  | reveal
  /-- confess: non-factive -/
  | confess
  /-- establish: non-factive -/
  | establish
  deriving DecidableEq, Repr, Fintype

/-- The authors' trigger-class coding in the released data (the classes of Tonhauser et al.
2013). -/
inductive TriggerClass where
  /-- B: no strong contextual felicity constraint, no obligatory local effect -/
  | b
  /-- C: no strong contextual felicity constraint, obligatory local effect -/
  | c
  deriving DecidableEq, Repr, Fintype

/-- A printed significance mark; the thresholds differ between tables (*** is .001 in Table 1 and
.0001 in Tables 3 and 5). -/
inductive Significance where
  /-- ***: significant at the table's strictest threshold -/
  | threeStars
  /-- **: significant at .01 -/
  | twoStars
  /-- *: significant at .05 -/
  | oneStar
  /-- .: marginal, at .1 -/
  | marginal
  /-- n.s.: not significant -/
  | ns
  deriving DecidableEq, Repr, Fintype

/-- A row of the by-expression means plotted in the Exp. 1a mean-projectivity-against-mean-not-
at-issueness figure (fig:f-proj-ai-1a in the authors' LaTeX); the discover and know means are
printed in the summary of Exps. 1a and 1b: the mean certain-that (projectivity) and asking-
whether (not-at-issueness) ratings of an expression's content in Experiment 1a, over 210
participants and 17 lexical contents, to two places -/
structure ExpressionRating where
  /-- The authors' trigger-class coding. -/
  triggerClass : TriggerClass
  /-- Mean certain-that rating, 1 projecting. -/
  projectivity : Decimal
  /-- Mean asking-whether rating, coded 1 not-at-issue. -/
  notAtIssueness : Decimal
  deriving DecidableEq, Repr

/-- The cells of the by-expression means plotted in the Exp. 1a mean-projectivity-against-mean-
not-at-issueness figure (fig:f-proj-ai-1a in the authors' LaTeX); the discover and know means
are printed in the summary of Exps. 1a and 1b, by expression; from an experiment; recomputed
from the authors' released data by `scripts/check_statistics.py`. -/
def heterogeneous : Expression → ExpressionRating
  | .nrrc => ⟨.b, ⟨96, 2⟩, ⟨97, 2⟩⟩
  | .nominalAppositive => ⟨.b, ⟨95, 2⟩, ⟨96, 2⟩⟩
  | .possessiveNP => ⟨.b, ⟨94, 2⟩, ⟨97, 2⟩⟩
  | .annoyed => ⟨.c, ⟨96, 2⟩, ⟨97, 2⟩⟩
  | .discover => ⟨.c, ⟨86, 2⟩, ⟨87, 2⟩⟩  -- projectivity .86 printed in section 3.3
  | .know => ⟨.c, ⟨92, 2⟩, ⟨91, 2⟩⟩  -- projectivity .92 printed in section 3.3
  | .only => ⟨.c, ⟨76, 2⟩, ⟨72, 2⟩⟩
  | .stop => ⟨.c, ⟨87, 2⟩, ⟨71, 2⟩⟩
  | .stupid => ⟨.c, ⟨85, 2⟩, ⟨88, 2⟩⟩

/-- A row of the by-expression means plotted in the Exp. 1b figure (fig:f-proj-ai-1b in the
authors' LaTeX); the discover and find out means are printed in the summary of Exps. 1a and
1b: the mean certain-that and asking-whether ratings of a predicate's complement in
Experiment 1b, over 235 participants and 20 lexical contents, to two places -/
structure PredicateRating where
  /-- The authors' trigger-class coding. -/
  triggerClass : TriggerClass
  /-- Mean certain-that rating, 1 projecting. -/
  projectivity : Decimal
  /-- Mean asking-whether rating, coded 1 not-at-issue. -/
  notAtIssueness : Decimal
  deriving DecidableEq, Repr

/-- The cells of the by-expression means plotted in the Exp. 1b figure (fig:f-proj-ai-1b in the
authors' LaTeX); the discover and find out means are printed in the summary of Exps. 1a and
1b, by predicate; from an experiment; recomputed from the authors' released data by
`scripts/check_statistics.py`. -/
def predicates : Predicate → PredicateRating
  | .annoyed => ⟨.c, ⟨92, 2⟩, ⟨94, 2⟩⟩
  | .notice => ⟨.c, ⟨92, 2⟩, ⟨92, 2⟩⟩
  | .aware => ⟨.c, ⟨92, 2⟩, ⟨94, 2⟩⟩
  | .realize => ⟨.c, ⟨91, 2⟩, ⟨92, 2⟩⟩
  | .amused => ⟨.c, ⟨91, 2⟩, ⟨94, 2⟩⟩
  | .see => ⟨.c, ⟨89, 2⟩, ⟨89, 2⟩⟩
  | .findOut => ⟨.c, ⟨88, 2⟩, ⟨91, 2⟩⟩  -- projectivity .88 printed in section 3.3
  | .learn => ⟨.c, ⟨88, 2⟩, ⟨90, 2⟩⟩
  | .discover => ⟨.c, ⟨85, 2⟩, ⟨89, 2⟩⟩  -- projectivity .85 printed in section 3.3
  | .reveal => ⟨.c, ⟨78, 2⟩, ⟨87, 2⟩⟩
  | .confess => ⟨.c, ⟨69, 2⟩, ⟨81, 2⟩⟩
  | .establish => ⟨.c, ⟨42, 2⟩, ⟨61, 2⟩⟩

/-- A row of plotted with the by-expression means; the asking-whether control mean .02 is printed
in the discussion of the at-issueness diagnostics: the mean ratings of the main-clause
controls, expected at the floor on both questions -/
structure Control where
  /-- The experiment. -/
  experiment : Experiment
  /-- Mean certain-that rating. -/
  projectivity : Decimal
  /-- Mean asking-whether rating, coded 1 not-at-issue. -/
  notAtIssueness : Decimal
  deriving DecidableEq, Repr

/-- The 2 rows of plotted with the by-expression means; the asking-whether control mean .02 is
printed in the discussion of the at-issueness diagnostics, in the paper's order; from an
experiment; recomputed from the authors' released data by `scripts/check_statistics.py`. -/
def controls : List Control :=
  [⟨.exp1a, ⟨5, 2⟩, ⟨2, 2⟩⟩,
   ⟨.exp1b, ⟨6, 2⟩, ⟨3, 2⟩⟩]

/-- A row of the regression paragraphs of the four Results sections: the fixed effect of at-
issueness on projectivity in the mixed-effects linear regression, with its likelihood-ratio
test -/
structure Effect where
  /-- The estimate. -/
  beta : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The t statistic. -/
  t : Decimal
  /-- The likelihood-ratio chi-square on one degree of freedom. -/
  chiSq : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of the regression paragraphs of the four Results sections, by experiment; from an
experiment; checked against the PDF text layer only. -/
def atIssuenessEffect : Experiment → Effect
  | .exp1a => ⟨⟨37, 2⟩, ⟨10, 2⟩, ⟨370, 2⟩, ⟨920, 2⟩, ⟨.lt, ⟨3, 3⟩⟩⟩
  | .exp1b => ⟨⟨34, 2⟩, ⟨4, 2⟩, ⟨931, 2⟩, ⟨3136, 2⟩, ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp2a =>  -- simplified random-effects structure; marginal under the full structure
    ⟨⟨29, 2⟩,
     ⟨6, 2⟩,
     ⟨521, 2⟩,
     ⟨2094, 2⟩,
     ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp2b =>  -- the sign in the predicted direction
    ⟨⟨3, 2⟩,
     ⟨4, 2⟩,
     ⟨83, 2⟩,
     ⟨68, 2⟩,
     ⟨.gt, ⟨4, 1⟩⟩⟩

/-- A row of the at-issueness paragraphs of the four Results sections: Pearson correlations of
mean projectivity with mean not-at-issueness, by target expression and without collapsing
across lexical contents (at the participant level in Experiments 1) -/
structure Correlation where
  /-- r over the by-expression means. -/
  byExpression : Decimal
  /-- r without collapsing across lexical contents. -/
  byItem : Decimal
  deriving DecidableEq, Repr

/-- The cells of the at-issueness paragraphs of the four Results sections, by experiment; from an
experiment; checked against the PDF text layer only. -/
def correlations : Experiment → Correlation
  | .exp1a => ⟨⟨85, 2⟩, ⟨45, 2⟩⟩
  | .exp1b => ⟨⟨99, 2⟩, ⟨44, 2⟩⟩
  | .exp2a => ⟨⟨84, 2⟩, ⟨6, 1⟩⟩
  | .exp2b => ⟨⟨54, 2⟩, ⟨28, 2⟩⟩

/-- A row of the Participants and Data exclusion paragraphs of each experiment; data points in
the regression paragraphs: recruitment, exclusions and the number of data points analysed -/
structure Participants where
  /-- Participants recruited on Mechanical Turk. -/
  recruited : ℕ
  /-- Excluded as not self-identifying as native speakers of American English. -/
  nonNative : ℕ
  /-- Excluded for control means over three standard deviations above the group mean. -/
  outliers : ℕ
  /-- Participants analysed. -/
  analysed : ℕ
  /-- Data points in the regression. -/
  dataPoints : ℕ
  deriving DecidableEq, Repr

/-- The cells of the Participants and Data exclusion paragraphs of each experiment; data points
in the regression paragraphs, by experiment; from an experiment; checked against the PDF text
layer only. -/
def participants : Experiment → Participants
  | .exp1a => ⟨250, 29, 11, 210, 1890⟩
  | .exp1b => ⟨250, 3, 12, 235, 2820⟩
  | .exp2a => ⟨250, 6, 6, 238, 43⟩
  | .exp2b => ⟨250, 6, 6, 238, 240⟩

/-- A row of the Tukey table of the Exp. 1a Results (tab:pairwise in the authors' LaTeX); *** is
significance at .001, ** at .01, * at .05, . marginal at .1: Tukey pairwise comparisons of
the projectivity means of the Experiment 1a contents; *** at .001 -/
structure PairwiseA where
  /-- The row expression. -/
  first : Expression
  /-- The column expression. -/
  second : Expression
  /-- The printed mark. -/
  significance : Significance
  deriving DecidableEq, Repr

/-- The 36 rows of the Tukey table of the Exp. 1a Results (tab:pairwise in the authors' LaTeX);
*** is significance at .001, ** at .01, * at .05, . marginal at .1, in the paper's order;
from an experiment; checked against the PDF text layer only. -/
def pairwise1a : List PairwiseA :=
  [⟨.annoyed, .nrrc, .ns⟩,
   ⟨.nominalAppositive, .nrrc, .ns⟩,
   ⟨.nominalAppositive, .annoyed, .ns⟩,
   ⟨.possessiveNP, .nrrc, .ns⟩,
   ⟨.possessiveNP, .annoyed, .ns⟩,
   ⟨.possessiveNP, .nominalAppositive, .ns⟩,
   ⟨.know, .nrrc, .ns⟩,
   ⟨.know, .annoyed, .ns⟩,
   ⟨.know, .nominalAppositive, .ns⟩,
   ⟨.know, .possessiveNP, .ns⟩,
   ⟨.stop, .nrrc, .threeStars⟩,
   ⟨.stop, .annoyed, .threeStars⟩,
   ⟨.stop, .nominalAppositive, .twoStars⟩,
   ⟨.stop, .possessiveNP, .twoStars⟩,
   ⟨.stop, .know, .marginal⟩,
   ⟨.discover, .nrrc, .threeStars⟩,
   ⟨.discover, .annoyed, .threeStars⟩,
   ⟨.discover, .nominalAppositive, .threeStars⟩,
   ⟨.discover, .possessiveNP, .twoStars⟩,
   ⟨.discover, .know, .oneStar⟩,
   ⟨.discover, .stop, .ns⟩,
   ⟨.stupid, .nrrc, .threeStars⟩,
   ⟨.stupid, .annoyed, .threeStars⟩,
   ⟨.stupid, .nominalAppositive, .threeStars⟩,
   ⟨.stupid, .possessiveNP, .threeStars⟩,
   ⟨.stupid, .know, .twoStars⟩,
   ⟨.stupid, .stop, .ns⟩,
   ⟨.stupid, .discover, .ns⟩,
   ⟨.only, .nrrc, .threeStars⟩,
   ⟨.only, .annoyed, .threeStars⟩,
   ⟨.only, .nominalAppositive, .threeStars⟩,
   ⟨.only, .possessiveNP, .threeStars⟩,
   ⟨.only, .know, .threeStars⟩,
   ⟨.only, .stop, .threeStars⟩,
   ⟨.only, .discover, .threeStars⟩,
   ⟨.only, .stupid, .twoStars⟩]

/-- A row of the Tukey table of the Exp. 1b Results (tab:pairwise-1b in the authors' LaTeX); ***
is significance at .0001, ** at .01, * at .05, . marginal at .1: Tukey pairwise comparisons
of the projectivity means of the Experiment 1b complements; *** at .0001 -/
structure PairwiseB where
  /-- The row predicate. -/
  first : Predicate
  /-- The column predicate. -/
  second : Predicate
  /-- The printed mark. -/
  significance : Significance
  deriving DecidableEq, Repr

/-- The 66 rows of the Tukey table of the Exp. 1b Results (tab:pairwise-1b in the authors'
LaTeX); *** is significance at .0001, ** at .01, * at .05, . marginal at .1, in the paper's
order; from an experiment; checked against the PDF text layer only. -/
def pairwise1b : List PairwiseB :=
  [⟨.notice, .annoyed, .ns⟩,
   ⟨.aware, .annoyed, .ns⟩,
   ⟨.aware, .notice, .ns⟩,
   ⟨.realize, .annoyed, .ns⟩,
   ⟨.realize, .notice, .ns⟩,
   ⟨.realize, .aware, .ns⟩,
   ⟨.amused, .annoyed, .ns⟩,
   ⟨.amused, .notice, .ns⟩,
   ⟨.amused, .aware, .ns⟩,
   ⟨.amused, .realize, .ns⟩,
   ⟨.see, .annoyed, .ns⟩,
   ⟨.see, .notice, .ns⟩,
   ⟨.see, .aware, .ns⟩,
   ⟨.see, .realize, .ns⟩,
   ⟨.see, .amused, .ns⟩,
   ⟨.findOut, .annoyed, .ns⟩,
   ⟨.findOut, .notice, .ns⟩,
   ⟨.findOut, .aware, .ns⟩,
   ⟨.findOut, .realize, .ns⟩,
   ⟨.findOut, .amused, .ns⟩,
   ⟨.findOut, .see, .ns⟩,
   ⟨.learn, .annoyed, .ns⟩,
   ⟨.learn, .notice, .ns⟩,
   ⟨.learn, .aware, .ns⟩,
   ⟨.learn, .realize, .ns⟩,
   ⟨.learn, .amused, .ns⟩,
   ⟨.learn, .see, .ns⟩,
   ⟨.learn, .findOut, .ns⟩,
   ⟨.discover, .annoyed, .twoStars⟩,
   ⟨.discover, .notice, .oneStar⟩,
   ⟨.discover, .aware, .marginal⟩,
   ⟨.discover, .realize, .marginal⟩,
   ⟨.discover, .amused, .marginal⟩,
   ⟨.discover, .see, .ns⟩,
   ⟨.discover, .findOut, .ns⟩,
   ⟨.discover, .learn, .ns⟩,
   ⟨.reveal, .annoyed, .threeStars⟩,
   ⟨.reveal, .notice, .threeStars⟩,
   ⟨.reveal, .aware, .threeStars⟩,
   ⟨.reveal, .realize, .threeStars⟩,
   ⟨.reveal, .amused, .threeStars⟩,
   ⟨.reveal, .see, .threeStars⟩,
   ⟨.reveal, .findOut, .threeStars⟩,
   ⟨.reveal, .learn, .threeStars⟩,
   ⟨.reveal, .discover, .twoStars⟩,
   ⟨.confess, .annoyed, .threeStars⟩,
   ⟨.confess, .notice, .threeStars⟩,
   ⟨.confess, .aware, .threeStars⟩,
   ⟨.confess, .realize, .threeStars⟩,
   ⟨.confess, .amused, .threeStars⟩,
   ⟨.confess, .see, .threeStars⟩,
   ⟨.confess, .findOut, .threeStars⟩,
   ⟨.confess, .learn, .threeStars⟩,
   ⟨.confess, .discover, .threeStars⟩,
   ⟨.confess, .reveal, .threeStars⟩,
   ⟨.establish, .annoyed, .threeStars⟩,
   ⟨.establish, .notice, .threeStars⟩,
   ⟨.establish, .aware, .threeStars⟩,
   ⟨.establish, .realize, .threeStars⟩,
   ⟨.establish, .amused, .threeStars⟩,
   ⟨.establish, .see, .threeStars⟩,
   ⟨.establish, .findOut, .threeStars⟩,
   ⟨.establish, .learn, .threeStars⟩,
   ⟨.establish, .discover, .threeStars⟩,
   ⟨.establish, .reveal, .threeStars⟩,
   ⟨.establish, .confess, .threeStars⟩]

end TonhauserBeaverDegen2018
