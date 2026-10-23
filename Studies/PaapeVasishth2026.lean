module

public import Linglib.Core.Probability.Distributions.Bernoulli
public import Linglib.Semantics.Reference.Iota

/-!
# Paape and Vasishth (2026): Context Ameliorates but Does Not Eliminate Garden-Pathing

This file formalizes the multinomial processing tree of Paape and Vasishth. A trial follows a
route through a tree of Bernoulli decisions, and the route fixes the reading-time costs, whether
the reader regresses, and the acceptability judgment. The paper fits the tree to a replication
of Altmann, Garnham, and Dennis's study, which crosses referential context with complement- and
relative-clause disambiguation. Its case for the tree is that condition means cannot tell an
effect of context on attachment from an effect on reanalysis cost.

## Main definitions

* `ReferentialContext.Supports`: a context supports an analysis when its definite refers and,
  for a relative clause, the bare definite does not.
* `tree`: the tree of Fig. 1, as a measure on routes.
* `Costs.disambiguating`, `Costs.spillover`: the cost a route pays at each region.

## Main results

* `Condition.isMatch_iff`: the match coding of the design follows from `Supports`.
* `tree_real_gardenPathed`, `tree_real_regresses`, `tree_real_accepts`: the tree's marginals.
* `integral_disambiguating_tree`: the mean cost at the disambiguating region.
* `means_not_identifiable`: halving the garden-path probability and halving the covert
  reanalysis cost can leave every condition mean equal and the mixtures different.

## Implementation notes

Which cells match is derived from when each analysis's definite refers: with two women the bare
definite fails its uniqueness presupposition, as Altmann and Steedman argue. Costs are added
above non-decision time. The mixture's component distributions, the predictor structure across
conditions, and the baseline regression probability of the text are not modeled, and the
inattentive reader's bias is a free parameter rather than the estimate from Paape and
Vasishth's earlier model. The fitted estimates and the model comparisons are not formalized.

## References

* [paape-vasishth-2026]
* [paape-vasishth-2022]
* [altmann-garnham-dennis-1992]
* [altmann-steedman-1988]
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped NNReal

namespace PaapeVasishth2026

/-! ### The design -/

/-- The string *the woman that he'd risked his life for* is disambiguated in three ways, after a
verb that takes a clausal complement or, in the control condition, after one that does not. -/
inductive Disambiguation where
  /-- *He told the woman that he'd risked his life for many people in similar fires.* -/
  | complementClause
  /-- *He told the woman that he'd risked his life for to install a smoke detector.* -/
  | relativeClause
  /-- *He asked the woman that he'd risked his life for to install a smoke detector ...* -/
  | unambiguousRelativeClause
  deriving DecidableEq

/-- A disambiguation is relative when it resolves the string to a relative clause. -/
def Disambiguation.IsRelative : Disambiguation → Prop
  | .complementClause => False
  | .relativeClause | .unambiguousRelativeClause => True

/-- Besides the fireman, the discourses of Table 1 introduce the woman he rescued and either a
man or a second woman. -/
inductive Referent where
  /-- The woman the fireman rescued. -/
  | rescued
  /-- The man of the one-woman discourse. -/
  | man
  /-- The second woman of the two-woman discourse. -/
  | otherWoman
  deriving DecidableEq, Fintype

/-- A discourse introduces one woman, with a man, or two women. -/
inductive ReferentialContext where
  /-- *An off-duty fireman was talking to a man and a woman.* -/
  | uniqueReferent
  /-- *An off-duty fireman was talking to two women.* -/
  | nonUniqueReferents
  deriving DecidableEq

namespace ReferentialContext

/-- `c.Woman r` holds when `r` is one of the women the context `c` introduces. -/
def Woman : ReferentialContext → Referent → Prop
  | .uniqueReferent, r => r = .rescued
  | .nonUniqueReferents, r => r ≠ .man

/-- The restrictor of the definite is *woman* under the complement-clause analysis and *woman
that he'd risked his life for* under a relative-clause analysis. -/
def restrictor (c : ReferentialContext) : Disambiguation → Referent → Prop
  | .complementClause => c.Woman
  | .relativeClause | .unambiguousRelativeClause => fun r ↦ c.Woman r ∧ r = .rescued

@[simp] theorem restrictor_complementClause (c : ReferentialContext) :
    c.restrictor .complementClause = c.Woman := rfl

/-- A context supports an analysis when the analysis's definite refers and, for a relative
clause, the bare definite does not. -/
def Supports (c : ReferentialContext) (d : Disambiguation) : Prop :=
  (iota (c.restrictor d)).isSome ∧ (d.IsRelative → iota c.Woman = none)

theorem iota_woman_isSome_iff (c : ReferentialContext) :
    (iota c.Woman).isSome ↔ c = .uniqueReferent := by
  rw [iota_isSome_iff]
  cases c <;> simp [Woman, ExistsUnique]
  decide

theorem iota_woman_eq_none_iff (c : ReferentialContext) :
    iota c.Woman = none ↔ c = .nonUniqueReferents := by
  rw [← Option.not_isSome_iff_eq_none, iota_woman_isSome_iff]
  cases c <;> simp

theorem iota_restrictor_isSome (c : ReferentialContext) {d : Disambiguation}
    (hd : d.IsRelative) : (iota (c.restrictor d)).isSome := by
  have hw : c.Woman .rescued := by cases c <;> simp [Woman]
  rw [iota_isSome_iff]
  cases d <;> simp only [Disambiguation.IsRelative] at hd <;>
    exact ⟨.rescued, ⟨hw, rfl⟩, fun _ h ↦ h.2⟩

end ReferentialContext

/-- A condition is a cell of the three-by-two design. -/
structure Condition where
  /-- The disambiguation of the target sentence. -/
  disambiguation : Disambiguation
  /-- The referential context of the discourse. -/
  context : ReferentialContext
  deriving DecidableEq

/-- A condition matches when its context supports its disambiguation. -/
def Condition.IsMatch (c : Condition) : Prop := c.context.Supports c.disambiguation

/-- A condition matches exactly when its context has two women and its disambiguation is a
relative clause, or one woman and a complement clause. -/
theorem Condition.isMatch_iff (c : Condition) :
    c.IsMatch ↔ (c.context = .nonUniqueReferents ↔ c.disambiguation.IsRelative) := by
  obtain ⟨d, x⟩ := c
  cases d <;> cases x <;> simp [Condition.IsMatch, ReferentialContext.Supports,
    Disambiguation.IsRelative, ReferentialContext.iota_woman_isSome_iff,
    ReferentialContext.iota_woman_eq_none_iff,
    ReferentialContext.iota_restrictor_isSome]

/-! ### The processing tree -/

/-- A garden-pathed reader reanalyzes overtly, by a regression, or covertly, either in situ at
the disambiguating region or postponed to the spillover region. -/
inductive Reanalysis where
  /-- Overt reanalysis rereads earlier material. -/
  | overt
  /-- Covert reanalysis happens in situ at the disambiguating region. -/
  | covertImmediate
  /-- Covert reanalysis is postponed to the spillover region. -/
  | covertPostponed
  deriving DecidableEq, Fintype

/-- A route runs from the root of the tree of Fig. 1 to a leaf. -/
inductive Route where
  /-- The reader is inattentive and guesses the judgment. -/
  | guess (accept : Bool)
  /-- The reader adopts the correct analysis on the first pass. -/
  | correct
  /-- The reader is garden-pathed and rejects the sentence without reanalysis. -/
  | triage
  /-- The reader is garden-pathed and reanalyzes, succeeding or failing. -/
  | reanalysis (kind : Reanalysis) (success : Bool)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Route := ⊤
instance : DiscreteMeasurableSpace Route := ⟨fun _ ↦ trivial⟩

namespace Route

/-- `o.GardenPathed` holds when the reader on route `o` is garden-pathed. -/
def GardenPathed : Route → Prop
  | .triage | .reanalysis .. => True
  | .guess _ | .correct => False

/-- `o.Regresses` holds when route `o` shows a first-pass regression, which in the tree only
overt reanalysis does. -/
def Regresses : Route → Prop
  | .reanalysis .overt _ => True
  | _ => False

/-- `o.Accepts` holds when route `o` ends in acceptance of the sentence. -/
def Accepts : Route → Prop
  | .guess b | .reanalysis _ b => b
  | .correct => True
  | .triage => False

end Route

/-- The parameters of the tree are the branching probabilities of Fig. 1. -/
structure Params where
  /-- The probability of attentive reading. -/
  attentive : I
  /-- The inattentive reader's probability of accepting. -/
  bias : I
  /-- The probability of garden-pathing. -/
  gardenPath : I
  /-- The probability of triage rather than reanalysis. -/
  triage : I
  /-- The probability of covert rather than overt reanalysis. -/
  covert : I
  /-- The probability of postponing covert reanalysis. -/
  postpone : I
  /-- The probability that overt reanalysis succeeds. -/
  overtSuccess : I
  /-- The probability that covert reanalysis succeeds. -/
  covertSuccess : I

/-- A decision node draws a Bernoulli variable with success probability `p` and continues the
route as `yes` on success and as `no` otherwise. -/
noncomputable def node (p : I) (yes no : Measure Route) : Measure Route :=
  Ber(true, false, p).bind fun b ↦ bif b then yes else no

section Node

variable (p : I) (yes no : Measure Route)

theorem node_eq : node p yes no = toNNReal p • yes + toNNReal (σ p) • no :=
  bernoulliMeasure_bind _ _ _ .of_discrete

@[simp] theorem node_zero : node 0 yes no = no := by simp [node_eq]

@[simp] theorem node_one : node 1 yes no = yes := by simp [node_eq]

@[simp] theorem node_dirac (x y : Route) : node p (dirac x) (dirac y) = Ber(x, y, p) :=
  node_eq ..

instance [IsProbabilityMeasure yes] [IsProbabilityMeasure no] :
    IsProbabilityMeasure (node p yes no) :=
  ⟨by simp [node_eq]⟩

theorem node_real_apply [IsFiniteMeasure yes] [IsFiniteMeasure no] (s : Set Route) :
    (node p yes no).real s = p * yes.real s + (1 - p) * no.real s := by
  rw [node_eq, measureReal_add_apply]
  simp [coe_symm_eq]

theorem integral_node {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure yes] [IsFiniteMeasure no] (f : Route → E) :
    ∫ o, f o ∂node p yes no = (p : ℝ) • ∫ o, f o ∂yes + (1 - p : ℝ) • ∫ o, f o ∂no := by
  rw [node_eq, integral_add_measure .of_finite .of_finite]
  simp [NNReal.smul_def, coe_symm_eq]

end Node

/-- Reanalysis of kind `r` succeeds with probability `s`. -/
noncomputable abbrev reanalyze (r : Reanalysis) (s : I) : Measure Route :=
  Ber(.reanalysis r true, .reanalysis r false, s)

/-- The tree of Fig. 1 is the distribution of routes its decision nodes generate. -/
noncomputable def tree (p : Params) : Measure Route :=
  node p.attentive
    (node p.gardenPath
      (node p.triage (dirac .triage)
        (node p.covert
          (node p.postpone (reanalyze .covertPostponed p.covertSuccess)
            (reanalyze .covertImmediate p.covertSuccess))
          (reanalyze .overt p.overtSuccess)))
      (dirac .correct))
    Ber(.guess true, .guess false, p.bias)

instance (p : Params) : IsProbabilityMeasure (tree p) := by unfold tree; infer_instance

section Marginals

variable (p : Params)

/-- Garden-pathing has the probability of attentive reading times that of garden-pathing. -/
theorem tree_real_gardenPathed :
    (tree p).real {o | o.GardenPathed} = p.attentive * p.gardenPath := by
  simp [tree, node_real_apply, Route.GardenPathed]

/-- A regression has the probability of overt reanalysis. -/
theorem tree_real_regresses : (tree p).real {o | o.Regresses} =
    p.attentive * p.gardenPath * (1 - p.triage) * (1 - p.covert) := by
  simp [tree, node_real_apply, Route.Regresses]
  ring

/-- Acceptance collects the accepting guess, the correct first pass, and the successful
reanalyses, and its probability does not depend on postponement. -/
theorem tree_real_accepts : (tree p).real {o | o.Accepts} =
    (1 - p.attentive) * p.bias + p.attentive * (1 - p.gardenPath + p.gardenPath *
      (1 - p.triage) * ((1 - p.covert) * p.overtSuccess + p.covert * p.covertSuccess)) := by
  simp [tree, node_real_apply, Route.Accepts]
  ring

end Marginals

/-! ### Reading times as a mixture -/

/-- The costs of Fig. 1 are reading time added above non-decision time. -/
structure Costs where
  /-- The cost of attending. -/
  attention : ℝ≥0
  /-- The cost of being garden-pathed. -/
  gardenPath : ℝ≥0
  /-- The cost of launching a regression. -/
  regression : ℝ≥0
  /-- The cost of covert reanalysis. -/
  covert : ℝ≥0

namespace Costs

variable (k : Costs)

/-- `k.disambiguating o` is the cost route `o` pays at the disambiguating region. -/
def disambiguating : Route → ℝ
  | .guess _ => 0
  | .correct => k.attention
  | .triage | .reanalysis .covertPostponed _ => k.attention + k.gardenPath
  | .reanalysis .overt _ => k.attention + k.gardenPath + k.regression
  | .reanalysis .covertImmediate _ => k.attention + k.gardenPath + k.covert

/-- `k.spillover o` is the cost route `o` pays at the spillover region, which only postponed
covert reanalysis incurs. -/
def spillover : Route → ℝ
  | .reanalysis .covertPostponed _ => k.covert
  | _ => 0

end Costs

section Means

variable (p : Params) (k : Costs)

/-- The mean cost at the disambiguating region adds the attention cost of attentive reading to
the garden-path probability times the expected cost of a garden-pathed trial. -/
theorem integral_disambiguating_tree : ∫ o, k.disambiguating o ∂tree p =
    p.attentive * (k.attention + p.gardenPath * (k.gardenPath + (1 - p.triage) *
      ((1 - p.covert) * k.regression + p.covert * (1 - p.postpone) * k.covert))) := by
  simp only [tree, integral_node, integral_bernoulliMeasure, integral_dirac,
    Costs.disambiguating, smul_eq_mul]
  ring

theorem integral_spillover_tree : ∫ o, k.spillover o ∂tree p =
    p.attentive * p.gardenPath * (1 - p.triage) * p.covert * p.postpone * k.covert := by
  simp only [tree, integral_node, integral_bernoulliMeasure, integral_dirac, Costs.spillover,
    smul_eq_mul]
  ring

theorem monotone_integral_gardenPath :
    Monotone fun g ↦ ∫ o, k.disambiguating o ∂tree {p with gardenPath := g} := by
  intro g g' h
  have := nonneg p.covert
  have := unitInterval.one_sub_nonneg p.triage
  have := unitInterval.one_sub_nonneg p.covert
  have := unitInterval.one_sub_nonneg p.postpone
  simp only [integral_disambiguating_tree]
  gcongr
  unit_interval

theorem monotone_integral_covert :
    Monotone fun c ↦ ∫ o, Costs.disambiguating {k with covert := c} o ∂tree p := by
  refine fun c c' h ↦ integral_mono .of_finite .of_finite fun o ↦ ?_
  rcases o with _ | _ | _ | ⟨_ | _ | _, _⟩ <;> simp [Costs.disambiguating, h]

end Means

/-- Condition means cannot locate an effect of context. From garden-path probability `1 / 2`
and covert reanalysis cost `800`, illustrative values, an effect on attachment that halves the
probability and an effect on reanalysis that halves the cost leave the same mean cost at both
regions and the same rates of regression and acceptance, but different mixtures over route
costs, `800` on a quarter of the trials against `400` on half of them. -/
theorem means_not_identifiable :
    ∃ (p : Params) (k : Costs) (g : I) (c : ℝ≥0), g < p.gardenPath ∧ c < k.covert ∧
      ∫ o, k.disambiguating o ∂tree {p with gardenPath := g} =
        ∫ o, Costs.disambiguating {k with covert := c} o ∂tree p ∧
      ∫ o, k.spillover o ∂tree {p with gardenPath := g} =
        ∫ o, Costs.spillover {k with covert := c} o ∂tree p ∧
      (tree {p with gardenPath := g}).real {o | o.Regresses} = (tree p).real {o | o.Regresses} ∧
      (tree {p with gardenPath := g}).real {o | o.Accepts} = (tree p).real {o | o.Accepts} ∧
      (tree {p with gardenPath := g}).map k.disambiguating ≠
        (tree p).map (Costs.disambiguating {k with covert := c}) := by
  refine ⟨
    { attentive := 1, bias := 0, gardenPath := ⟨1 / 2, by norm_num⟩, triage := 0, covert := 1,
      postpone := 0, overtSuccess := 1, covertSuccess := 1 },
    { attention := 0, gardenPath := 0, regression := 0, covert := 800 }, ⟨1 / 4, by norm_num⟩,
    400, Subtype.mk_lt_mk.mpr (by norm_num), by norm_num, ?_, ?_, ?_, ?_, fun h ↦ ?_⟩
  · simp only [integral_disambiguating_tree]
    norm_num
  · simp only [integral_spillover_tree]
    norm_num
  · simp only [tree_real_regresses]
    norm_num
  · simp only [tree_real_accepts]
    norm_num
  · have := congrArg (·.real {400}) h
    simp [tree, Costs.disambiguating] at this

end PaapeVasishth2026
