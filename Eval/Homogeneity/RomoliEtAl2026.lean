module

public import Eval.Basic
public import Eval.Homogeneity.Account

/-!
# Scoring accounts of homogeneity on Romoli et al. (2026)

The data are the tests of Romoli et al.'s Experiment 3, read from
`Data/Experiments/RomoliEtAl2026`: on the target pictures of *exactly two boys opened their
presents*, where a non-maximal reading weakens the positive or the negative part of its meaning,
whether the context affected the negative part, the CONTEXT term with the negative part as the
reference level of POLARITY, and whether it affected the two parts differently. An effect is
found when its χ² test is significant at the .05 level (`found`). Experiments 1 and 2 are those
of Augurzky et al. and are scored there; the reanalysis changes no test's significance
(`RomoliEtAl2026.significant_iff_augurzky`).

An account predicts a context effect for a part when on some target picture for it it accepts
the sentence in one context and not the other (`contexts`). The non-implicature approach predicts
both parts affected, in opposite directions, and fits both tests (`verdict_nonImplicature`).
Guerrini and Wehbe's presuppositional exhaustification predicts the positive part alone affected
and is refuted by both (`verdict_presuppositionalExh`), and the context-free accounts by the
context effect (`verdict_contextFree`). The implicature approach as Augurzky et al. state it does
not reach *exactly two* (`verdict_implicature`).

## References

* [romoli-etal-2026]
* [augurzky-etal-2023]
-/

@[expose] public section

namespace Eval.Homogeneity.RomoliEtAl2026

open _root_.RomoliEtAl2026 (Effect Item Polarity pictures sentences tests)

/-- The target pictures of Experiment 3 for a level of POLARITY. -/
def targets (pol : Polarity) : List Item :=
  pictures.filter fun p ↦ p.experiment = .three ∧ pol ∈ p.targetFor

/-- Whether the test of an effect in Experiment 3 was significant at the .05 level. -/
def found (e : Effect) : Bool :=
  decide ((tests .three e).p.toRat < 1 / 20)

/-- Whether an account predicts a context effect for a level of POLARITY of Experiment 3, which it
does when on some target picture for it it accepts the sentence under the existential question,
which the prohibition raises, and not under the universal one, which the requirement raises, or
the reverse; none where linglib does not state its verdicts in a context. -/
def contextEffect (a : Account) (pol : Polarity) : Option Bool :=
  ((targets pol).mapM fun (p : Item) ↦ do
    let e ← a.accepts (sentences .three pol).quantifier .existential p.opened
    let u ← a.accepts (sentences .three pol).quantifier .universal p.opened
    pure (e != u)).map fun (es : List Bool) ↦ es.any id

/-- The context effect on the negative part of *exactly two* and its interaction with polarity in
Experiment 3 of [romoli-etal-2026], scored by whether an account predicts them. -/
def contexts : Eval.Experiment Account Effect Bool where
  observed e := some (found e)
  predicted a e := do
    let pos ← contextEffect a .positive
    let neg ← contextEffect a .negative
    match e with
    | .context => some neg
    | .interaction => some (pos != neg)
    | .polarity => none

/-- Experiment 3 found a context effect on the negative part and no interaction with polarity. -/
theorem contexts_observed :
    contexts.observed .context = some true ∧ contexts.observed .interaction = some false := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The non-implicature approach predicts that the context affects both parts, which fits both
tests. -/
theorem verdict_nonImplicature :
    contexts.verdict .nonImplicature .context = .correct ∧
      contexts.verdict .nonImplicature .interaction = .correct := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- Presuppositional exhaustification predicts that the context affects the positive part alone,
which both tests refute. -/
theorem verdict_presuppositionalExh :
    contexts.verdict .presuppositionalExhaustification .context = .wrong ∧
      contexts.verdict .presuppositionalExhaustification .interaction = .wrong := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The context-free accounts predict no context effect, which the effect on the negative part
refutes and the absent interaction fits. -/
theorem verdict_contextFree :
    contexts.verdict .supervaluation .context = .wrong ∧
      contexts.verdict .supervaluation .interaction = .correct ∧
      contexts.verdict .pointwise .context = .wrong ∧
      contexts.verdict .pointwise .interaction = .correct ∧
      contexts.verdict .exhaustification .context = .wrong ∧
      contexts.verdict .exhaustification .interaction = .correct ∧
      contexts.verdict .presupposition .context = .wrong ∧
      contexts.verdict .presupposition .interaction = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The implicature approach as [augurzky-etal-2023] state it, and Križ and Spector's
non-maximality, are not stated on these pictures, so they are silent. -/
theorem verdict_implicature :
    contexts.verdict .implicature .context = .silent ∧
      contexts.verdict .implicature .interaction = .silent ∧
      contexts.verdict .implicatureEnriched .context = .silent ∧
      contexts.verdict .implicatureEnriched .interaction = .silent ∧
      contexts.verdict .krizSpector .context = .silent ∧
      contexts.verdict .krizSpector .interaction = .silent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Eval.Homogeneity.RomoliEtAl2026
