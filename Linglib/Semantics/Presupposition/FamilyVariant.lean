module

public import Linglib.Core.Relation.SetRel
public import Linglib.Data.Examples.Schema
public import Linglib.Syntax.Person.Basic

/-!
# The family of sentences

The family of sentences of a trigger is the sentence unembedded and under each of the
entailment-cancelling operators, negation, a polar question, the antecedent of a conditional and an
epistemic possibility modal, in the terms of Chierchia and McConnell-Ginet and of Tonhauser, Beaver,
Roberts and Simons; a content projects when the embedded members still carry it. A member of the
family is named by the position of its sentence (`FamilyVariant`). Each member evaluates its
sentence along a relation, the identity except under the modal (`FamilyVariant.rel`), and these
relations are reflexive when the modal's is, so that a requirement on the local context of the
sentence is a requirement on the context of the member. Example rows record a sentence's
environment, whether the content projected, and the person of the matrix subject, and the readers
here type those features.

## References

* [chierchia-mcconnell-ginet-1990]
* [tonhauser-beaver-roberts-simons-2013]
-/

@[expose] public section

namespace Presupposition

/-- A member of the family of sentences is named by the position of its sentence, unembedded or
under an entailment-cancelling operator. -/
inductive FamilyVariant where
  | unembedded
  | negation
  | question
  | conditionalAntecedent
  | epistemicModal
  deriving DecidableEq, Repr, Fintype

namespace FamilyVariant

/-- The relation along which a member of the family evaluates its sentence, where `M` is the
accessibility of the possibility modal. The other members evaluate the sentence at the member's own
world. -/
def rel {W : Type*} (M : SetRel W W) : FamilyVariant → SetRel W W
  | epistemicModal => M
  | _ => .id

instance {W : Type*} (M : SetRel W W) [M.IsRefl] (e : FamilyVariant) : (e.rel M).IsRefl := by
  cases e
  case epistemicModal => exact ‹M.IsRefl›
  all_goals exact SetRel.isRefl_id

/-- Where the modal's accessibility is the identity, every member evaluates its sentence at its own
world. -/
@[simp] theorem rel_id {W : Type*} (e : FamilyVariant) : e.rel (SetRel.id : SetRel W W) = .id := by
  cases e <;> rfl

/-- The members of the family as example rows record them, by the environment of the sentence. -/
def table : List (String × FamilyVariant) :=
  [("atomic", unembedded), ("negation", negation), ("question", question),
    ("conditional antecedent", conditionalAntecedent), ("epistemic modal", epistemicModal)]

end FamilyVariant

end Presupposition

namespace Datum

open Presupposition

/-- The member of the family a row's sentence is, by its recorded environment. -/
def environment? (e : Datum) : Option FamilyVariant :=
  e.parse? "environment" FamilyVariant.table

/-- Whether the row's content projected, as the row records it. -/
def projective? (e : Datum) : Option Bool :=
  e.parse? "projective" [("yes", true), ("no", false)]

/-- The person of the row's matrix subject. -/
def person? (e : Datum) : Option Person :=
  e.parse? "person" [("1", .first), ("2", .second), ("3", .third)]

end Datum
