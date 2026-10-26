module

public import Linglib.Data.Experiments.Schema

/-!
# RonderosEtAl2024: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/RonderosEtAl2024.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

A visual-world experiment in the paradigm of [sedivy-etal-1999] with speakers of English, Hindi and
Hungarian: a four-object display is previewed for three seconds, a definite description with a
colour, material or scalar adjective follows, and the participant clicks on its referent. CONDITION
(Contrast, No-Contrast) is run in two blocks and crossed with ADJECTIVE TYPE. Fixations are analysed
over the noun window, time-locked to noun onset and offset by 200 ms: by a cluster-based permutation
test on target looks and by a mixed model of the target-advantage score, for the effect of condition
within each adjective type; the looks to target and competitor together in the No-Contrast condition
are modelled with scalar adjectives as the intercept. Language is a grouping unit of the models, so
the statistics are pooled over the three languages. The interaction cluster and the control model of
the time before the noun are not recorded.

## Raw data

* <https://osf.io/apxtj/>: data, analysis scripts and materials, as the paper states; the project
  was public when checked (2026-09-28)

## References

* [ronderos-etal-2024]
-/

@[expose] public section

namespace RonderosEtAl2024

open Data.Experiments

/-- The factor CONDITION: whether the display holds an object of the target's kind that lacks the
property. -/
inductive Condition where
  /-- Contrast: an object of the target's kind lacking the property, and an object of another
  kind sharing it -/
  | contrast
  /-- No-Contrast: only the object of another kind sharing the property -/
  | noContrast
  deriving DecidableEq, Repr, Fintype

/-- The factor ADJECTIVE TYPE. -/
inductive AdjType where
  /-- color: black, blue, brown, green, orange, red, white, yellow -/
  | color
  /-- material: cotton, glass, gold, leather, metal, paper, plastic, wooden, woolen -/
  | material
  /-- scalar: large, narrow, short, small, tall, thick, thin, wide -/
  | scalar
  deriving DecidableEq, Repr, Fintype

/-- A row of Results, p. 1222: the cluster of time bins in the noun window over which condition
affects looks to the target, for an adjective type. -/
structure Cluster where
  /-- The start of the cluster, in milliseconds into the noun window. -/
  onset : Option ℕ
  /-- The end of the cluster, in milliseconds into the noun window. -/
  offset : Option ℕ
  /-- The total sum of t values over the cluster. -/
  tSum : Option Decimal
  /-- The cluster's permutation p-value. -/
  p : Option PValue
  deriving DecidableEq, Repr

/-- The cells of Results, p. 1222, by adjType; checked against the page images. -/
def clusters : AdjType → Cluster
  | .color => ⟨some 240, some 600, some ⟨3961, 2⟩, some ⟨.lt, ⟨1, 2⟩⟩⟩
  | .scalar => ⟨some 260, some 500, some ⟨3307, 2⟩, some ⟨.lt, ⟨1, 2⟩⟩⟩
  | .material => ⟨none, none, none, none⟩  -- no clusters whatsoever

/-- A row of Results, p. 1222: the effect of condition on the target-advantage score over the
noun window, the proportion of time on the target less that on the competitor, for an
adjective type. -/
structure TargetAdvantage where
  /-- The estimate of the effect of condition. -/
  beta : Decimal
  /-- The p-value, from the Satterthwaite approximation. -/
  p : PValue
  /-- The t statistic. -/
  t : Decimal
  deriving DecidableEq, Repr

/-- The cells of Results, p. 1222, by adjType; checked against the page images. -/
def targetAdvantage : AdjType → TargetAdvantage
  | .color => ⟨⟨24, 2⟩, ⟨.lt, ⟨5, 2⟩⟩, ⟨241, 2⟩⟩
  | .scalar => ⟨⟨19, 2⟩, ⟨.lt, ⟨5, 2⟩⟩, ⟨202, 2⟩⟩
  | .material => ⟨⟨10, 2⟩, ⟨.eq, ⟨28, 2⟩⟩, ⟨108, 2⟩⟩

/-- A row of Results, p. 1223: the difference from scalar adjectives in the looks to target and
competitor together over the noun window of the No-Contrast condition, for an adjective type. -/
structure BaselineLooks where
  /-- The adjective type compared with scalar adjectives. -/
  adjType : AdjType
  /-- The estimate of the difference. -/
  beta : Decimal
  /-- The p-value. -/
  p : PValue
  /-- The z statistic. -/
  z : Decimal
  deriving DecidableEq, Repr

/-- The 2 rows of Results, p. 1223, in the paper's order; checked against the page images. -/
def baselineLooks : List BaselineLooks :=
  [⟨.color, ⟨25, 2⟩, ⟨.lt, ⟨1, 2⟩⟩, ⟨280, 2⟩⟩,
   ⟨.material, ⟨24, 2⟩, ⟨.lt, ⟨5, 2⟩⟩, ⟨240, 2⟩⟩]

end RonderosEtAl2024
