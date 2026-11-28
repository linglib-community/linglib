module

public import Linglib.Syntax.Category.Determiner.Basic

/-!
# Fering determiner inventory

Fering (North Frisian, ISO `frr`) has two full paradigms of the definite article, which Ebert
describes: the A-form (*a/at*), the weak article marking situational uniqueness, and the D-form
(*di/det*), the strong article marking anaphoric reference, including covarying (donkey) uses.

## References

* [ebert-1971]
* [schwarz-2013], §3 and §5.2
-/

@[expose] public section

namespace Fering.Determiners

/-- The A-form *a/at* expones the uses on which its referent is unique in the situation, and
bridging to a part of an antecedent, as from a church to *a törem* 'the tower'. -/
def aForm : Article :=
  { form := "a", definiteness := {.definite}, exponent := .dedicatedMorpheme,
    uses := {.immediateSituation, .largerSituation, .bridging .partWhole} }

/-- The D-form *di/det* expones the uses on which it refers back to an antecedent, and bridging by
a relation, as from a painting to *di mooler* 'the painter'. -/
def dForm : Article :=
  { form := "di", definiteness := {.definite}, exponent := .dedicatedMorpheme,
    uses := {.anaphoric, .bridging .relational} }

/-- The Fering determiners are the A-form and the D-form of the definite article. -/
def inventory : Determiner.Inventory := [.article aForm, .article dForm]

theorem strengths_inventory : inventory.strengths = Finset.univ := by decide

theorem not_isSyncretic_inventory : ¬ inventory.IsSyncretic := by decide

end Fering.Determiners
