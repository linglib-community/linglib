/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Discourse roles

This file defines the two discourse roles, speaker and addressee. They index the agents of a
two-party commitment model, as in Gunlogson's and Farkas and Bruce's discourse contexts, and a
person category is a set of them together with a count of others, as in Cysouw's paradigms. A
role's counterpart is the other participant, `Discourse.Role.other`, an involution without fixed
points, so [a statement about every role is a statement about a role and its
counterpart](##Discourse.Role.forall_role'). The lemmas follow those of `Bool` and `not`.

## References

* [gunlogson-2001]
* [farkas-bruce-2010]
* [cysouw-2003]
-/

@[expose] public section

namespace Discourse

/-- A discourse role is one of the two participants of a speech act, its speaker or its
addressee. -/
inductive Role where
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Role

/-- The other participant: the addressee of the speaker and the speaker of the addressee. -/
def other : Role → Role
  | .speaker => .addressee
  | .addressee => .speaker

@[simp] theorem other_speaker : other .speaker = .addressee := rfl
@[simp] theorem other_addressee : other .addressee = .speaker := rfl
@[simp] theorem other_other : ∀ r : Role, r.other.other = r := by decide

theorem other_involutive : Function.Involutive other := other_other
theorem other_injective : Function.Injective other := other_involutive.injective
@[simp] theorem other_inj {r s : Role} : r.other = s.other ↔ r = s := other_injective.eq_iff
theorem other_ne_self : ∀ r : Role, r.other ≠ r := by decide
theorem self_ne_other (r : Role) : r ≠ r.other := (other_ne_self r).symm
theorem eq_other_of_ne : ∀ {r s : Role}, r ≠ s → r = s.other := by decide
theorem eq_other_iff {r s : Role} : r = s.other ↔ r ≠ s :=
  ⟨fun h ↦ h ▸ other_ne_self s, eq_other_of_ne⟩

instance : Nontrivial Role := ⟨⟨.speaker, .addressee, nofun⟩⟩

theorem card : Fintype.card Role = 2 := rfl

theorem forall_role' {p : Role → Prop} (r : Role) : (∀ s, p s) ↔ p r ∧ p r.other :=
  ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨h₁, h₂⟩ s ↦ by cases r <;> cases s <;> assumption⟩

@[simp] theorem forall_role {p : Role → Prop} : (∀ r, p r) ↔ p .speaker ∧ p .addressee :=
  forall_role' .speaker

theorem exists_role' {p : Role → Prop} (r : Role) : (∃ s, p s) ↔ p r ∨ p r.other :=
  ⟨fun ⟨s, hs⟩ ↦ by cases s <;> cases r <;> first | exact .inl ‹_› | exact .inr ‹_›,
    fun h ↦ by cases h <;> exact ⟨_, ‹_›⟩⟩

@[simp] theorem exists_role {p : Role → Prop} : (∃ r, p r) ↔ p .speaker ∨ p .addressee :=
  exists_role' .speaker

end Role

end Discourse
