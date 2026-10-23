module

public import Linglib.Core.Probability.Distributions.Bernoulli
public import Linglib.Data.Experiments.DegenTonhauser2021
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Verbs.Copular

/-!
# Degen and Tonhauser (2021): Prior beliefs modulate projection

This file formalizes Degen and Tonhauser's finding that a listener's prior belief in the
content of a clausal complement modulates how strongly that content projects, the listener's
inference about the speaker's commitment to it under a question. The hypothesis came from the
by-item variability in Tonhauser, Beaver and Degen's projection ratings and had conflicting
support, Mahler finding modulation for politically charged contents and Lorson none for the
pre-state of *stop*. Across twenty clause-embedding predicates and twenty contents each paired
with a fact raising or lowering its prior, projection was higher under the higher-prior fact
for every predicate, both within participants (Experiment 1) and between (Experiment 2), and
the participant's own prior predicted projection better than the group's or the categorical
manipulation. The account the paper sketches is Bayesian, in the spirit of Goodman and Frank's
rational speech acts and Qing, Goodman and Lassiter's projection model: projection is the
posterior credence in the content, which by Bayes' rule is strictly increasing in the prior at
fixed likelihoods, so a more likely content is taken to be more strongly committed to.

## Main statements

* `projection_strictMono`: the posterior credence in a content is strictly increasing in its
  Bernoulli prior, whatever the speaker's production likelihoods.
* `fact_raises_prior`: the fact manipulation raised every content's mean prior rating, in both
  designs.
* `prior_modulates_projection`: every predicate's complement was rated more projective under
  the higher-prior fact, in both designs.

## Implementation notes

* The means are the generated tables of `Data/Experiments/DegenTonhauser2021.json`, recomputed
  from the trial-level data of the paper's repository by `scripts/check_experiments.py`.
* The regression coefficients are not encoded: the prior manipulation raised ratings (β = 0.45),
  projection rose with the categorical fact (β = 0.14), with the group-level prior (β = 0.31)
  and with the participant's own prior (β = 0.28), the individual-level model winning by BIC,
  and Experiment 2 replicated the effect between participants (β = 0.18).

## References

* [degen-tonhauser-2021]
* [tonhauser-beaver-degen-2018]
* [mahler-2020]
* [lorson-2018]
* [goodman-frank-2016]
* [qing-goodman-lassiter-2016]
-/

@[expose] public section

namespace DegenTonhauser2021

/-! ### Projection as posterior credence -/

section Posterior

open MeasureTheory ProbabilityTheory unitInterval

variable {𝓤 : Type*} [MeasurableSpace 𝓤] [MeasurableSingletonClass 𝓤]

theorem projection_strictMono (κ : Kernel Bool 𝓤) [IsFiniteKernel κ] {u : 𝓤}
    (htrue : κ true {u} ≠ 0) (hfalse : κ false {u} ≠ 0) :
    StrictMono fun p : I ↦ ((κ†Ber(true, false, p)) u).real {true} :=
  strictMono_posterior_bernoulliMeasure true false κ (by decide) htrue hfalse

end Posterior

/-! ### The means of Experiments 1 and 2 -/

/-- The mean prior probability rating of a content, given the fact. -/
def priorMean (d : Design) (f : Fact) (c : Content) : ℚ := (prior d f c).mean.toRat

/-- The mean certainty rating of a predicate's complement, given the content's fact. -/
def certaintyMean (d : Design) (f : Fact) (p : Predicate) : ℚ := (certainty d f p).mean.toRat

/-- The manipulation worked: every content's mean prior rating was higher under its
higher-probability fact, within and between participants, the pattern of Figures 2 and A2. -/
theorem fact_raises_prior (d : Design) (c : Content) :
    priorMean d .lowerProbability c < priorMean d .higherProbability c := by
  revert d c; decide +kernel

/-- For every predicate the complement's mean certainty rating was higher under the
higher-probability fact, within and between participants, the pattern of Figures 3 and 6 that
a prior-sensitive account predicts. -/
theorem prior_modulates_projection (d : Design) (p : Predicate) :
    certaintyMean d .lowerProbability p < certaintyMean d .higherProbability p := by
  revert d p; decide +kernel

/-! ### The Fragment's predicates -/

section Fragment

open English
open English.Verbs hiding Verb
open English.Verbs.Copular

/-- The English lexical entry of a predicate. -/
def entry : Predicate → Verb
  | .acknowledge => acknowledge.toVerb
  | .admit => admit.toVerb
  | .announce => announce.toVerb
  | .beAnnoyed => beAnnoyed
  | .beRight => beRight
  | .confess => confess.toVerb
  | .confirm => confirm.toVerb
  | .demonstrate => demonstrate.toVerb
  | .discover => discover.toVerb
  | .establish => establish.toVerb
  | .hear => hear.toVerb
  | .inform => inform.toVerb
  | .know => know.toVerb
  | .pretend => pretend.toVerb
  | .prove => prove.toVerb
  | .reveal => reveal.toVerb
  | .say => say.toVerb
  | .see => see.toVerb
  | .suggest => suggest.toVerb
  | .think => think.toVerb

theorem all_predicates_take_clause_complement (p : Predicate) :
    ∃ fr ∈ (entry p).valency.frames, fr.HasFinite := by
  cases p <;> decide

end Fragment

end DegenTonhauser2021
