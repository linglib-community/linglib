module

public import Linglib.Data.Statistics.Schema

/-!
# Narrog2010: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Narrog2010.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The changes of modal meaning that the chapter tabulates from the 76-language sample of [bybee-
perkins-pagliuca-1994], and the totals it draws from them.

## References

* [narrog-2010]
-/

@[expose] public section

namespace Narrog2010

open Data.Statistics

/-- The labels of source and new meanings in the chapter's table of changes. -/
inductive Label where
  /-- future/prediction: a future or prediction marker -/
  | futurePrediction
  /-- root possibility: possibility given the circumstances -/
  | rootPossibility
  /-- root/epistemic possibility: root or epistemic possibility -/
  | rootEpistemicPossibility
  /-- obligation: obligation of unspecified strength -/
  | obligation
  /-- ability/root possibility: ability or root possibility -/
  | abilityRootPossibility
  /-- strong obligation: obligation of the kind English must expresses -/
  | strongObligation
  /-- weak obligation: obligation of the kind English should expresses -/
  | weakObligation
  /-- imperative: the imperative mood -/
  | imperative
  /-- permission: deontic possibility -/
  | permission
  /-- admonitive: the admonitive mood, a warning or prohibition -/
  | admonitive
  /-- epistemic possibility: epistemic possibility -/
  | epistemicPossibility
  /-- certainty: strong epistemic necessity -/
  | certainty
  /-- probability: weak epistemic necessity -/
  | probability
  deriving DecidableEq, Repr, Fintype

/-- The changes of the sample that the chapter counts. (section 4, p. 405; checked against the
page images.) -/
def listedChanges : ℕ := 42

/-- The changes whose source is ability or situational possibility. (section 4, p. 405; checked
against the page images.) -/
def possibilitySourceChanges : ℕ := 18

/-- The changes whose source is obligation. (section 4, p. 405; checked against the page images.) -/
def obligationSourceChanges : ℕ := 9

/-- A row of Table 2, p. 396: a change of modal meaning, with the number of grams of the sample
that show it, one gram per language. -/
structure Change where
  /-- The source meaning. -/
  source : Label
  /-- The new meaning. -/
  target : Label
  /-- The grams showing the change. -/
  grams : ℕ
  deriving DecidableEq, Repr

/-- The 8 rows of Table 2, p. 396, in the paper's order; from a sample of languages coded from
their descriptions; checked against the page images. -/
def changes : List Change :=
  [⟨.futurePrediction, .imperative, 13⟩,
   ⟨.rootPossibility, .permission, 9⟩,
   ⟨.rootEpistemicPossibility, .admonitive, 5⟩,
   ⟨.obligation, .imperative, 4⟩,
   ⟨.abilityRootPossibility, .epistemicPossibility, 4⟩,
   ⟨.strongObligation, .certainty, 3⟩,
   ⟨.weakObligation, .probability, 2⟩,
   ⟨.futurePrediction, .probability, 2⟩]  -- Printed as prediction/future.

end Narrog2010
