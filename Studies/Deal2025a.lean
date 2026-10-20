/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Deal2024

/-!
# Deal (2025): Current models of Agree

Deal traces the Agree operation from Chomsky's uninterpretable features to the interaction and
satisfaction theory, and states the latter as an algorithm, (30) of the appendix, which
`Minimalist.Probe.Spec.agree` implements. The appendix adds dynamic interaction to the main text's
algorithm: a goal bearing a feature marked for it resets the probe's interaction condition to that
feature and the features it dominates. In the 2024 derivations a feature copied from a goal instead
joins a set of features that every later goal must bear. This file runs the grammars of the 2024
PCC typology through (30) and compares the outcomes.

## Main results

* `Deal2025a.forall_licit_iff_iff`: (30) licenses the same clitic combinations as the 2024
  derivations for every grammar except the insatiable ones marking both [SPKR] and [ADDR] for
  dynamic interaction.
* `Deal2025a.inclusive_divergence`: for those grammars an inclusive direct object lets an
  inclusive indirect object interact in 2024, but under (30) it installs the features dominated
  by both [SPKR] and [ADDR], which are none.
* `Deal2025a.licit_iff_on_cells`: on the six cells of table (1) the two agree for every grammar,
  so the typology tables (53) and (57) are the same under (30).

## References

* [deal-2025a]
* [deal-2024]
-/

@[expose] public section

namespace Deal2025a

open Deal2024 Minimalist PersonSegment Clause

/-- The probe of a 2024 grammar as a specification of (30), [INT:φ] with its satisfaction
feature. -/
def toSpec (g : Grammar) : Probe.Spec PersonSegment := ⟨Finset.univ, g.satisfaction.toFinset⟩

/-- A clitic combination ⟨IO, DO⟩ is licit under (30) when the probe, meeting the direct object
first, interacts with both objects. -/
def Licit (g : Grammar) (s : Scenario Person) : Prop :=
  ((toSpec g).agree (spec ·.1) g.dynamic [s.low, s.high].zipIdx).interacted.map (·.2) = [0, 1]

instance (g : Grammar) : DecidablePred (Licit g) := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The two algorithms agree on every combination exactly when the grammar has a satisfaction
condition or does not mark both [SPKR] and [ADDR] for dynamic interaction. -/
theorem forall_licit_iff_iff (g : Grammar) :
    (∀ s, Licit g s ↔ Deal2024.Licit g s) ↔
      ¬ (g.satisfaction = none ∧ .speaker ∈ g.dynamic ∧ .addressee ∈ g.dynamic) := by
  revert g
  decide +kernel

/-- With no satisfaction condition and [SPKR] and [ADDR] both dynamic, an inclusive direct object
leaves an inclusive indirect object visible in 2024 but blocks every indirect object under (30). -/
theorem inclusive_divergence :
    Deal2024.Licit ⟨none, {.speaker, .addressee}⟩ ⟨.firstInclusive, .firstInclusive⟩ ∧
      ¬ Licit ⟨none, {.speaker, .addressee}⟩ ⟨.firstInclusive, .firstInclusive⟩ := by
  decide +kernel

/-- On the six cells of table (1) the two algorithms agree for every grammar. -/
theorem licit_iff_on_cells (g : Grammar) :
    ∀ s ∈ PCC.distinctPairs, Licit g s ↔ Deal2024.Licit g s := by
  revert g
  decide +kernel

end Deal2025a
