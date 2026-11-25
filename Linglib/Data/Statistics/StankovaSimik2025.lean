module

public import Linglib.Data.Statistics.Schema

/-!
# StankovaSimik2025: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/StankovaSimik2025.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Naturalness ratings of Czech negative polar questions on a seven-point scale from 75 native
speakers: a main experiment crossing verb position, indefinite and context, and subexperiments on
the particles *náhodou* and *copak*. The paper reports the fixed effects of cumulative link mixed
models with random intercepts for items and participants.

## References

* [stankova-simik-2025]
-/

@[expose] public section

namespace StankovaSimik2025

open Data.Statistics

/-- The fitted models, one for each verb position of the main experiment and one for each
particle. -/
inductive Model where
  /-- V1: the interrogative questions of the main experiment -/
  | v1
  /-- nonV1: the declarative questions of the main experiment -/
  | nonV1
  /-- náhodou: the interrogative questions with *náhodou* -/
  | nahodou
  /-- copak: the questions with *copak* -/
  | copak
  deriving DecidableEq, Repr, Fintype

/-- The effects the paper reports a test for. -/
inductive Effect where
  /-- indefinite: the main effect of the indefinite, concord item or polarity item -/
  | indefinite
  /-- context: the main effect of the context -/
  | context
  /-- context × indefinite: the interaction of context and indefinite -/
  | interaction
  /-- context within PPI: the simple effect of context at the polarity item, from a post-hoc
  model -/
  | contextWithinPPI
  /-- context within NCI: the simple effect of context at the concord item, from a post-hoc model -/
  | contextWithinNCI
  deriving DecidableEq, Repr, Fintype

/-- The native speakers of Czech who filled in the questionnaire. (§5, p. 5; checked against the
PDF text layer only.) -/
def participants : ℕ := 75

/-- The top of the Likert scale, completely natural. (§5, p. 6; checked against the PDF text
layer only.) -/
def scaleMax : ℕ := 7

/-- The median rating of an interrogative negative question with a polarity item after positive
evidence, as in (14). (§5.3, p. 8; checked against the PDF text layer only.) -/
def medianPositive : ℕ := 6

/-- The median rating of the same condition after a neutral context. (§5.3, p. 8; checked against
the PDF text layer only.) -/
def medianNeutral : ℕ := 5

/-- A row of §5.2, p. 7; §6.1, p. 10; §6.2, p. 12: The Wald tests of the fixed effects that the
paper reports. -/
structure Test where
  /-- The model. -/
  model : Model
  /-- The effect tested. -/
  effect : Effect
  /-- The z statistic. -/
  z : Decimal
  /-- The p-value as printed. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The 9 rows of §5.2, p. 7; §6.1, p. 10; §6.2, p. 12, in the paper's order; from an experiment;
checked against the page images. -/
def tests : List Test :=
  [⟨.v1, .indefinite, ⟨-15674, 3⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.v1, .context, ⟨-1374, 3⟩, ⟨.eq, ⟨169, 3⟩⟩⟩,
   ⟨.v1, .interaction, ⟨2933, 3⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.v1, .contextWithinPPI, ⟨-3522, 3⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.v1, .contextWithinNCI, ⟨1104, 3⟩, ⟨.eq, ⟨27, 2⟩⟩⟩,
   ⟨.nonV1, .context, ⟨8674, 3⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.nonV1, .indefinite, ⟨6208, 3⟩, ⟨.lt, ⟨1, 2⟩⟩⟩,
   ⟨.nahodou, .indefinite, ⟨-12845, 3⟩, ⟨.lt, ⟨1, 3⟩⟩⟩,
   ⟨.copak, .context, ⟨9372, 3⟩, ⟨.lt, ⟨1, 3⟩⟩⟩]

end StankovaSimik2025
