module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Comparative argument roles

The comparative concepts S, A, P, T and R of alignment typology, in the sense Haspelmath calls
Comrie's. A and P are the arguments of a language's major two-argument construction that
represent the agent and the patient when it expresses an action, S is the argument of an
intransitive clause coded like the single argument of a one-argument predicate, and T and R are
the theme and the recipient of a physical-transfer verb such as 'give', together with whatever
arguments are coded like them. Transitivity is defined from the roles, a transitive clause being
one with an A and a P. Dixon's O is P.

Role rank puts A above P and R above T, and Haspelmath's role-reference associations say that a
role's usual referential prominence follows its rank.

## Main definitions

* `ArgumentRole`: the five roles.
* `ArgumentRole.core`: S, A and P, the roles monotransitive alignment compares.
* `ArgumentRole.Outranks`, `ArgumentRole.IsHigherRanked`, `ArgumentRole.IsLowerRanked`: role
  rank.
* `ArgumentRole.MoreUsualFor`: the order of prominence values by how usual they are for a role.

## Implementation notes

The roles are coding slots, not semantic roles (`ArgumentStructure.ThetaRole`): the A of a
language's transitive construction need not be an agent. The library's classifiers,
`ArgumentStructure.Valency.role` and `ArgumentFrame.argumentRole`, read the roles off the number
of core arguments, taking transitivity as given. Haspelmath calls this procedure Dixon's and
argues against it; on the major two-argument construction it agrees with the definitions above.
It departs from them on transfer verbs: `ArgumentFrame.argumentRole` names the objects of a
double-object frame R and T in English order, and makes the sole object of an NP + PP frame P, so
the theme of *give a book to her* is P rather than T.

## References

* [comrie-1978]
* [dixon-1994]
* [haspelmath-2011]
* [haspelmath-2021]
-/

@[expose] public section

/-- The comparative argument roles of [haspelmath-2011]: the sole argument of an intransitive
clause, the two arguments of a transitive one, and the two objects of a ditransitive one. -/
inductive ArgumentRole where
  /-- The argument of an intransitive clause coded like the single argument of a one-argument
  predicate. -/
  | S
  /-- The argument of the major two-argument construction that represents the agent when the
  construction expresses an action. -/
  | A
  /-- The argument of the major two-argument construction that represents the patient when the
  construction expresses an action. -/
  | P
  /-- The recipient of a physical-transfer verb, or an argument coded like it. -/
  | R
  /-- The theme of a physical-transfer verb, or an argument coded like it. -/
  | T
  deriving DecidableEq, Repr, Fintype

namespace ArgumentRole

/-- The roles S, A and P, whose coding monotransitive alignment compares. -/
def core : Finset ArgumentRole := {.S, .A, .P}

@[simp] theorem mem_core {r : ArgumentRole} : r ∈ core ↔ r = .S ∨ r = .A ∨ r = .P := by
  simp [core]

/-! ### Role rank -/

/-- Role rank, [haspelmath-2021]'s (7): in a monotransitive construction A ranks above P, and in
a ditransitive one R ranks above T. The sole argument S is unranked. -/
inductive Outranks : ArgumentRole → ArgumentRole → Prop
  | monotransitive : Outranks .A .P
  | ditransitive : Outranks .R .T

theorem outranks_iff {r s : ArgumentRole} : r.Outranks s ↔ r = .A ∧ s = .P ∨ r = .R ∧ s = .T :=
  ⟨by rintro (_ | _) <;> simp, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> constructor⟩

instance : DecidableRel Outranks := fun _ _ ↦ decidable_of_iff' _ outranks_iff

/-- The role is the higher-ranked argument of its construction, A or R. -/
def IsHigherRanked (r : ArgumentRole) : Prop := ∃ s, r.Outranks s

/-- The role is the lower-ranked argument of its construction, P or T. -/
def IsLowerRanked (r : ArgumentRole) : Prop := ∃ s : ArgumentRole, s.Outranks r

instance : DecidablePred IsHigherRanked := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

instance : DecidablePred IsLowerRanked := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

theorem IsHigherRanked.not_isLowerRanked {r : ArgumentRole} :
    r.IsHigherRanked → ¬ r.IsLowerRanked := by
  decide +revert

theorem IsLowerRanked.not_isHigherRanked {r : ArgumentRole} :
    r.IsLowerRanked → ¬ r.IsHigherRanked :=
  fun h h' ↦ h'.not_isLowerRanked h

/-- Prominence `x` is a more usual association than `y` for role `r`, [haspelmath-2021]'s (9): a
higher-ranked role tends to be referentially prominent and a lower-ranked one non-prominent, so
nothing is more usual for S. -/
def MoreUsualFor {α : Type*} [LT α] (r : ArgumentRole) (x y : α) : Prop :=
  (r.IsHigherRanked ∧ y < x) ∨ (r.IsLowerRanked ∧ x < y)

instance {α : Type*} [LT α] [DecidableLT α] (r : ArgumentRole) (x y : α) :
    Decidable (r.MoreUsualFor x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

end ArgumentRole
