module

public import Mathlib.Order.UpperLower.Basic
public import Linglib.Syntax.Case.Dependent
public import Linglib.Fragments.HindiUrdu.Case

/-!
# Bobaljik (2008): Where's Phi? Agreement as a Postsyntactic Operation

This file formalizes the claim that the finite verb agrees with the highest accessible noun
phrase in its domain, where accessibility is a matter of morphological case. The categories of
morphological case are those of Marantz's realization hierarchy, and they are ordered for
agreement the other way round: unmarked case is more accessible than dependent case, and
dependent case more accessible than lexical case. A language chooses how far down this order
its verb can see. Since morphological case is assigned after the syntax, agreement, which
feeds on it, is postsyntactic as well.

Stated over case categories, Moravcsik's hierarchy of agreement controllers holds of
ergative and accusative languages alike. It also explains a gap among the splits between
case and agreement. An ergative case system gives absolutive agreement when only unmarked case
is accessible and subject agreement when dependent case is accessible too, as in Nepali, while
an accusative case system gives subject agreement at every setting. Ergative agreement over
accusative case cannot be derived.

## Main declarations

* `CaseCategory`: the categories of morphological case, in their order of accessibility.
* `controller`: the highest accessible noun phrase of a domain.
* `controls`: whether an argument of a clause with the given alignment controls agreement.

## Main results

* `isUpperSet_accessible`: if a category is accessible, so is every category above it.
* `isAccusative_controls_accusative`, `isErgative_controls_ergative_unmarked`,
  `isAccusative_controls_ergative_dependent`: the predicted agreement alignments.
* `not_isErgative_controls_accusative`: no setting derives ergative agreement from accusative
  case.
* `controller_quirky`: below a subject with lexical case the verb agrees with the object.

## Implementation notes

Case is assigned by the dependent case rules of `Syntax/Case/Dependent.lean`. Case valued by
agreement with a functional head, which those rules also provide for, counts as unmarked.

## References

* [bobaljik-2008]
* [marantz-1991]
-/

@[expose] public section

namespace Bobaljik2008

open Case DependentCase

/-- The categories of morphological case, in their order of accessibility for agreement, with
lexical case the least accessible and unmarked case the most. -/
inductive CaseCategory where
  | lexical
  | dependent
  | unmarked
  deriving DecidableEq, Repr, Fintype

namespace CaseCategory

instance : LinearOrder CaseCategory := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- The category of a case, by what valued it. -/
def ofMechanism : Mechanism → CaseCategory
  | .lexical => .lexical
  | .dependent => .dependent
  | .unmarked | .agree => .unmarked

end CaseCategory

variable {α : Type*}

theorem isUpperSet_accessible (t : CaseCategory) : IsUpperSet {c | t ≤ c} := isUpperSet_Ici t

/-- The controller of agreement is the highest noun phrase of the domain whose case is
accessible. Noun phrases whose case is not accessible are invisible and do not intervene. -/
def controller (t : CaseCategory) (domain : Valuation α (Case × Mechanism)) : Option ℕ :=
  domain.findIdx? fun s ↦ s.2.any fun v ↦ t ≤ .ofMechanism v.2

/-- Whether an argument controls agreement in a clause of the given alignment, in a language
whose least accessible category is `t`. -/
def controls (a : Alignment.AlignmentType) (t : CaseCategory) : ArgumentRole → Bool
  | .S => controller t (assignCases a (fun _ ↦ none) [ArgumentRole.S]) = some 0
  | .A => controller t (assignCases a (fun _ ↦ none) [ArgumentRole.A, .P]) = some 0
  | .P => controller t (assignCases a (fun _ ↦ none) [ArgumentRole.A, .P]) = some 1
  | .R | .T => false

/-! ### The predicted agreement alignments -/

theorem isAccusative_controls_accusative (t : CaseCategory) :
    Alignment.IsAccusative (controls .accusative t) := by
  cases t <;> decide

theorem isErgative_controls_ergative_unmarked :
    Alignment.IsErgative (controls .ergative .unmarked) := by
  decide

theorem isAccusative_controls_ergative_dependent :
    Alignment.IsAccusative (controls .ergative .dependent) := by
  decide

theorem not_isErgative_controls_accusative (t : CaseCategory) :
    ¬ Alignment.IsErgative (controls .accusative t) :=
  (isAccusative_controls_accusative t).not_isErgative

/-! ### Case against grammatical function -/

theorem controller_quirky (c : Case) (t : CaseCategory) (ht : t ≠ .lexical) :
    controller t (assignCases .accusative (fun r ↦ if r = ArgumentRole.A then some c else none)
      [ArgumentRole.A, .P]) = some 1 := by
  cases t <;> first | exact absurd rfl ht | rfl

theorem hindi_controller :
    controller .unmarked (assignCases (HindiUrdu.alignment .perfective) (fun _ ↦ none)
      [ArgumentRole.A, .P]) = some 1 ∧
    controller .unmarked (assignCases (HindiUrdu.alignment .imperfective) (fun _ ↦ none)
      [ArgumentRole.A, .P]) = some 0 := by
  decide

end Bobaljik2008
