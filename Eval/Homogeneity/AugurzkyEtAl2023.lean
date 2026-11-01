module

public import Eval.Basic
public import Eval.Homogeneity.Account

/-!
# Scoring accounts of homogeneity on Augurzky et al. (2023)

The data are the tests of Augurzky et al.'s two picture-verification experiments, read from
`Data/Statistics/AugurzkyEtAl2023`: on the mixed pictures, where some boys opened all their
presents and some opened only some, whether the context, a family rule raising whether any or
whether all presents were opened, affected the judgments of the negative quantifier, *no* in
Experiment 1 and *not every* in Experiment 2, and whether it affected them differently for
*every*. POLARITY is treatment-coded with the negative quantifier as reference level, so the
CONTEXT term is the simple effect on that quantifier, as Romoli et al. name it. An effect is
found when its χ² test is significant at the .05 level (`found`).

An account predicts a context effect for a quantifier when on some mixed picture it accepts the
sentence in one context and not the other, the CONTEXT term when it predicts one for the negative
quantifier, and the interaction when it predicts one for one quantifier and not the other
(`contexts`). The context-free accounts of Križ and Chemla predict no context effect and fit
only Experiment 2's absent interaction (`verdict_contextFree`). The non-implicature approach is
refuted by Experiment 1's interaction (`verdict_nonImplicature`). The implicature approach, and
Guerrini and Wehbe's presuppositional exhaustification, which agrees with it under these
quantifiers, are refuted by the context effects on both negative quantifiers and by Experiment 2's
absent interaction (`verdict_implicature`, `verdict_presuppositionalExh`); with the scalar
implicature of *not every* the implicature approach misses only the context effect on *no*
(`verdict_implicatureEnriched`).

## References

* [augurzky-etal-2023]
* [romoli-etal-2026]
-/

@[expose] public section

namespace Eval.Homogeneity.AugurzkyEtAl2023

open _root_.AugurzkyEtAl2023 (Quantifier Context Effect Picture pictures tests)

/-- An experiment of [augurzky-etal-2023]. -/
abbrev Run := _root_.AugurzkyEtAl2023.Experiment

/-- The mixed pictures of an experiment's quantifier. -/
def mixed (x : Run) (q : Quantifier) : List Picture :=
  pictures.filter fun p ↦ p.experiment = x ∧ p.quantifier = q ∧ p.truth = .mixed

/-- The quantifiers of an experiment. -/
def quantifiers (x : Run) : List Quantifier :=
  [.every, .no, .notEvery].filter fun q ↦ mixed x q ≠ []

/-- Whether the test of an effect on the mixed pictures of an experiment was significant at the
.05 level. -/
def found (x : Run) (e : Effect) : Option Bool :=
  (tests.find? fun t ↦ t.experiment = x ∧ t.model = .mixed ∧ t.effect = e).map fun t ↦
    decide (t.p.Significant (1 / 20))

/-- Whether an account predicts a context effect for a quantifier, which it does when on some
mixed picture it accepts the sentence in one context and not the other; none where linglib does
not state its verdicts in a context. -/
def contextEffect (a : Account) (x : Run) (q : Quantifier) : Option Bool :=
  ((mixed x q).mapM fun (p : Picture) ↦ do
    let e ← a.accepts (.ofAugurzky q) .existential p.opened
    let u ← a.accepts (.ofAugurzky q) .universal p.opened
    pure (e != u)).map fun (es : List Bool) ↦ es.any id

/-- The context effect on the negative quantifier and its interaction with polarity in each
experiment of [augurzky-etal-2023], scored by whether an account predicts them. -/
def contexts : Eval.Experiment Account (Run × Effect) Bool where
  observed xe := found xe.1 xe.2
  predicted a xe := do
    let pos ← contextEffect a xe.1 .every
    let neg ← ((quantifiers xe.1).filter (· ≠ .every)).mapM (contextEffect a xe.1)
    match xe.2 with
    | .context => some (neg.any id)
    | .interaction => some (neg.any (· != pos))
    | _ => none

/-- Both experiments found a context effect on the negative quantifier, and only Experiment 1
found it to interact with polarity. -/
theorem contexts_observed :
    contexts.observed (.one, .context) = some true ∧
      contexts.observed (.one, .interaction) = some true ∧
      contexts.observed (.two, .context) = some true ∧
      contexts.observed (.two, .interaction) = some false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The context-free accounts predict no context effect, so only the absent interaction of
Experiment 2 fits them. -/
theorem verdict_contextFree :
    contexts.verdict .supervaluation (.one, .context) = .wrong ∧
      contexts.verdict .supervaluation (.one, .interaction) = .wrong ∧
      contexts.verdict .supervaluation (.two, .context) = .wrong ∧
      contexts.verdict .supervaluation (.two, .interaction) = .correct ∧
      contexts.verdict .pointwise (.one, .context) = .wrong ∧
      contexts.verdict .pointwise (.one, .interaction) = .wrong ∧
      contexts.verdict .pointwise (.two, .context) = .wrong ∧
      contexts.verdict .pointwise (.two, .interaction) = .correct ∧
      contexts.verdict .exhaustification (.one, .context) = .wrong ∧
      contexts.verdict .exhaustification (.one, .interaction) = .wrong ∧
      contexts.verdict .exhaustification (.two, .context) = .wrong ∧
      contexts.verdict .exhaustification (.two, .interaction) = .correct ∧
      contexts.verdict .presupposition (.one, .context) = .wrong ∧
      contexts.verdict .presupposition (.one, .interaction) = .wrong ∧
      contexts.verdict .presupposition (.two, .context) = .wrong ∧
      contexts.verdict .presupposition (.two, .interaction) = .correct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The non-implicature approach predicts that the context affects every quantifier alike, so
Experiment 1's interaction refutes it. -/
theorem verdict_nonImplicature :
    contexts.verdict .nonImplicature (.one, .context) = .correct ∧
      contexts.verdict .nonImplicature (.one, .interaction) = .wrong ∧
      contexts.verdict .nonImplicature (.two, .context) = .correct ∧
      contexts.verdict .nonImplicature (.two, .interaction) = .correct := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The implicature approach predicts that the context affects *every* alone, so the context
effects on *no* and *not every* and Experiment 2's absent interaction refute it. -/
theorem verdict_implicature :
    contexts.verdict .implicature (.one, .context) = .wrong ∧
      contexts.verdict .implicature (.one, .interaction) = .correct ∧
      contexts.verdict .implicature (.two, .context) = .wrong ∧
      contexts.verdict .implicature (.two, .interaction) = .wrong := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- With the scalar implicature of *not every*, the implicature approach predicts the context to
affect *every* and *not every* and not *no*, so only the context effect on *no* refutes it. -/
theorem verdict_implicatureEnriched :
    contexts.verdict .implicatureEnriched (.one, .context) = .wrong ∧
      contexts.verdict .implicatureEnriched (.one, .interaction) = .correct ∧
      contexts.verdict .implicatureEnriched (.two, .context) = .correct ∧
      contexts.verdict .implicatureEnriched (.two, .interaction) = .correct := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Presuppositional exhaustification agrees with the implicature approach under these
quantifiers (`RomoliEtAl2026.asymmetric_iff_implicature`), and is refuted alike. -/
theorem verdict_presuppositionalExh :
    contexts.verdict .presuppositionalExhaustification (.one, .context) = .wrong ∧
      contexts.verdict .presuppositionalExhaustification (.one, .interaction) = .correct ∧
      contexts.verdict .presuppositionalExhaustification (.two, .context) = .wrong ∧
      contexts.verdict .presuppositionalExhaustification (.two, .interaction) = .wrong := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Križ and Spector's non-maximality is not stated on these pictures, so they are silent. -/
theorem verdict_krizSpector :
    contexts.verdict .krizSpector (.one, .context) = .silent ∧
      contexts.verdict .krizSpector (.one, .interaction) = .silent ∧
      contexts.verdict .krizSpector (.two, .context) = .silent ∧
      contexts.verdict .krizSpector (.two, .interaction) = .silent := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Eval.Homogeneity.AugurzkyEtAl2023
