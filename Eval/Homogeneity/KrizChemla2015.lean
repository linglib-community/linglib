module

public import Eval.Basic
public import Eval.Homogeneity.Account

/-!
# Scoring accounts of homogeneity on Križ and Chemla (2015)

The data are the gap tests of Table 2 of [kriz-chemla-2015], read from
`Data/Experiments/KrizChemla2015`: for each environment of the definite and each gap condition,
whether the experiments found a truth-value gap, outside the A2 and B2 tests of *no* that the
paper discounts (`_root_.KrizChemla2015.GapTest.Discounted`). An account predicts a gap in a
configuration when it gives every item realizing the configuration the value 0, and no gap when it
gives none of them 0 (`gaps`). Spector's supervaluation fits every configuration
(`verdict_supervaluation`). The literal meaning against its global exhaustification misses the
gaps under negation, under *no* and in the GAP?? configuration of *exactly 2*
(`verdict_exhaustification`), and the supervaluation over each individual's resolution and the universal
presupposition predict a gap in its GAP? configuration, where none was found (`verdict_pointwise`,
`verdict_presupposition`). The accounts that need a context are silent (`verdict_contextual`).

## References

* [kriz-chemla-2015]
-/

@[expose] public section

namespace Eval.Homogeneity.KrizChemla2015

open _root_.KrizChemla2015 (Embedding Condition Item tested gapTests misprinted)

/-- The tested items that realize a configuration, the faulty ones and the misprinted one aside. -/
def itemsOf (e : Embedding) (c : Condition) : List Item :=
  tested.filter fun i ↦ i.embedding = e ∧ i.condition = c ∧ i.status ≠ .faulty ∧ i ≠ misprinted

/-- What Table 2 found in a configuration, over its tests outside the discounted ones, when they
agree. -/
def found (e : Embedding) (c : Condition) : Option Bool :=
  let ts := gapTests.filter fun t ↦ t.embedding = e ∧ t.condition = c ∧ ¬ t.Discounted
  if ts.isEmpty then none
  else if ts.all (·.found = .yes) then some true
  else if ts.all (·.found = .no) then some false
  else none

/-- Each configuration of [kriz-chemla-2015] scored by whether an account predicts a gap on its
items. -/
def gaps : Eval.Experiment Account (Embedding × Condition) Bool where
  observed ec := found ec.1 ec.2
  predicted a ec :=
    match (itemsOf ec.1 ec.2).mapM fun i ↦ a.value ec.1.tree i.display with
    | none => none
    | some vs =>
      if vs.isEmpty then none
      else if vs.all (· = 0) then some true
      else if vs.all (· ≠ 0) then some false
      else none

/-- Table 2 found a gap in every GAP and GAP?? configuration and none in the GAP? one, setting aside
the A2 and B2 tests of *no*, whose sentences lacked negative inversion (fn 10) and found none. -/
theorem gaps_observed :
    gaps.observed (.unembedded, .gap) = some true ∧
      gaps.observed (.negation, .gap) = some true ∧
      gaps.observed (.all, .gap) = some true ∧
      gaps.observed (.no, .gap) = some true ∧
      gaps.observed (.exactly, .gap) = some true ∧
      gaps.observed (.exactly, .gapQ) = some false ∧
      gaps.observed (.exactly, .gapQQ) = some true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The supervaluation fits every configuration. -/
theorem verdict_supervaluation :
    gaps.verdict .supervaluation (.unembedded, .gap) = .correct ∧
      gaps.verdict .supervaluation (.negation, .gap) = .correct ∧
      gaps.verdict .supervaluation (.all, .gap) = .correct ∧
      gaps.verdict .supervaluation (.no, .gap) = .correct ∧
      gaps.verdict .supervaluation (.exactly, .gap) = .correct ∧
      gaps.verdict .supervaluation (.exactly, .gapQ) = .correct ∧
      gaps.verdict .supervaluation (.exactly, .gapQQ) = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Supervaluating over each individual's resolution predicts a gap in the GAP? configuration of
*exactly 2*, where none was found, and fits the rest. -/
theorem verdict_pointwise :
    gaps.verdict .pointwise (.unembedded, .gap) = .correct ∧
      gaps.verdict .pointwise (.negation, .gap) = .correct ∧
      gaps.verdict .pointwise (.all, .gap) = .correct ∧
      gaps.verdict .pointwise (.no, .gap) = .correct ∧
      gaps.verdict .pointwise (.exactly, .gap) = .correct ∧
      gaps.verdict .pointwise (.exactly, .gapQ) = .wrong ∧
      gaps.verdict .pointwise (.exactly, .gapQQ) = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The literal meaning against its global exhaustification misses the gaps under negation, under
*no* and in the GAP?? configuration, and fits the rest. -/
theorem verdict_exhaustification :
    gaps.verdict .exhaustification (.unembedded, .gap) = .correct ∧
      gaps.verdict .exhaustification (.negation, .gap) = .wrong ∧
      gaps.verdict .exhaustification (.all, .gap) = .correct ∧
      gaps.verdict .exhaustification (.no, .gap) = .wrong ∧
      gaps.verdict .exhaustification (.exactly, .gap) = .correct ∧
      gaps.verdict .exhaustification (.exactly, .gapQ) = .correct ∧
      gaps.verdict .exhaustification (.exactly, .gapQQ) = .wrong := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The universal projection of a homogeneity presupposition predicts a gap in the GAP?
configuration, where none was found, and fits the rest. -/
theorem verdict_presupposition :
    gaps.verdict .presupposition (.unembedded, .gap) = .correct ∧
      gaps.verdict .presupposition (.negation, .gap) = .correct ∧
      gaps.verdict .presupposition (.all, .gap) = .correct ∧
      gaps.verdict .presupposition (.no, .gap) = .correct ∧
      gaps.verdict .presupposition (.exactly, .gap) = .correct ∧
      gaps.verdict .presupposition (.exactly, .gapQ) = .wrong ∧
      gaps.verdict .presupposition (.exactly, .gapQQ) = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The accounts that need a context are silent here, since the experiments fixed no question for
the context to raise. -/
theorem verdict_contextual :
    gaps.verdict .nonImplicature (.unembedded, .gap) = .silent ∧
      gaps.verdict .nonImplicature (.negation, .gap) = .silent ∧
      gaps.verdict .nonImplicature (.all, .gap) = .silent ∧
      gaps.verdict .nonImplicature (.no, .gap) = .silent ∧
      gaps.verdict .nonImplicature (.exactly, .gap) = .silent ∧
      gaps.verdict .nonImplicature (.exactly, .gapQ) = .silent ∧
      gaps.verdict .nonImplicature (.exactly, .gapQQ) = .silent ∧
      gaps.verdict .implicature (.unembedded, .gap) = .silent ∧
      gaps.verdict .implicature (.negation, .gap) = .silent ∧
      gaps.verdict .implicature (.all, .gap) = .silent ∧
      gaps.verdict .implicature (.no, .gap) = .silent ∧
      gaps.verdict .implicature (.exactly, .gap) = .silent ∧
      gaps.verdict .implicature (.exactly, .gapQ) = .silent ∧
      gaps.verdict .implicature (.exactly, .gapQQ) = .silent ∧
      gaps.verdict .implicatureEnriched (.unembedded, .gap) = .silent ∧
      gaps.verdict .implicatureEnriched (.negation, .gap) = .silent ∧
      gaps.verdict .implicatureEnriched (.all, .gap) = .silent ∧
      gaps.verdict .implicatureEnriched (.no, .gap) = .silent ∧
      gaps.verdict .implicatureEnriched (.exactly, .gap) = .silent ∧
      gaps.verdict .implicatureEnriched (.exactly, .gapQ) = .silent ∧
      gaps.verdict .implicatureEnriched (.exactly, .gapQQ) = .silent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Eval.Homogeneity.KrizChemla2015
