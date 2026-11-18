/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.PartialUnify
public import Linglib.Syntax.Person.Basic
public import Mathlib.Data.Fintype.Powerset

/-!
# Person specifications

A form is specified in person for the participant sets its referents may have. A referent has
one participant set; a form may cover several, as a first person form with no clusivity covers
the speaker alone and the speaker with the addressee. A specification is thus a nonempty family
of participant sets, and one is more specific than another when it covers fewer. The
unspecified form covers them all and is the least specification. Two specifications
[unify to what both cover](##Person.Specification.unify_ofPerson_first_inclusive) and are
[incompatible when they share nothing](##Person.Specification.not_compat_first_second), so a
form with no clusivity [agrees with an inclusive
referent](##Person.Specification.ofPerson_first_le_inclusive) and a first person form with no
second.

## Implementation notes

The order is that of `{s : Finset α // s.Nonempty}ᵒᵈ` in `Core/Order/PartialUnify.lean`, the
smaller family the larger element. The empty family is not a specification, so that
incompatible specifications have no common extension.

## References

* [harbour-2016]
* [cysouw-2003]
-/

@[expose] public section

open SpeechAct

namespace Person

/-- A person specification: the nonempty family of participant sets a form covers, a more
specific specification covering fewer. -/
abbrev Specification := {S : Finset (Finset Role) // S.Nonempty}ᵒᵈ

namespace Specification

/-- The participant sets a specification covers. -/
def sets (x : Specification) : Finset (Finset Role) := (OrderDual.ofDual x).1

theorem le_iff {x y : Specification} : x ≤ y ↔ y.sets ⊆ x.sets := Iff.rfl

instance : DecidableLE Specification := fun x y ↦ inferInstanceAs (Decidable (y.sets ⊆ x.sets))

/-- The unspecified form covers every participant set. -/
instance : OrderBot Specification where
  bot := OrderDual.toDual ⟨Finset.univ, Finset.univ_nonempty⟩
  bot_le x := Finset.subset_univ x.sets

@[simp] theorem sets_bot : (⊥ : Specification).sets = Finset.univ := rfl

/-- The specification of a person value: the participant sets it covers. -/
def ofPerson (p : Person) : Specification :=
  OrderDual.toDual ⟨p.participantSets, p.participantSets_nonempty⟩

@[simp] theorem sets_ofPerson (p : Person) : (ofPerson p).sets = p.participantSets := rfl

theorem ofPerson_injective : Function.Injective ofPerson := fun _ _ h ↦
  participantSets_injective (congrArg sets h)

/-- The specification of the general first person. -/
abbrev first : Specification := ofPerson .first

/-- The specification of the inclusive first person. -/
abbrev firstInclusive : Specification := ofPerson .firstInclusive

/-- The specification of the exclusive first person. -/
abbrev firstExclusive : Specification := ofPerson .firstExclusive

/-- The specification of the second person. -/
abbrev second : Specification := ofPerson .second

/-- The specification of the third person. -/
abbrev third : Specification := ofPerson .third

/-- The specification of a referent with the participants `s`. -/
def ofParticipants (s : Finset Role) : Specification :=
  OrderDual.toDual ⟨{s}, Finset.singleton_nonempty s⟩

@[simp] theorem sets_ofParticipants (s : Finset Role) : (ofParticipants s).sets = {s} := rfl

/-- A specification covers a referent exactly when it covers the referent's participants. -/
theorem le_ofParticipants_iff {x : Specification} {s : Finset Role} :
    x ≤ ofParticipants s ↔ s ∈ x.sets :=
  Finset.singleton_subset_iff

/-- A specification is printed as the participant sets it covers. -/
instance : Repr Specification where
  reprPrec x _ :=
    repr <| [((∅ : Finset Role), "other"), ({.speaker}, "speaker"), ({.addressee}, "addressee"),
      ({.speaker, .addressee}, "speaker+addressee")].filterMap fun p ↦
        if p.1 ∈ x.sets then some p.2 else none

/-- A specification is a speech-act participant's when every participant set it covers is
nonempty. -/
def IsSAP (x : Specification) : Prop := ∀ s ∈ x.sets, s.Nonempty

instance : DecidablePred IsSAP := fun x ↦ inferInstanceAs (Decidable (∀ s ∈ x.sets, s.Nonempty))

theorem isSAP_ofPerson {p : Person} : IsSAP (ofPerson p) ↔ p.IsSAP := Iff.rfl

theorem not_isSAP_bot : ¬ IsSAP ⊥ := by decide

/-- A first person form with no clusivity covers an inclusive referent. -/
theorem ofPerson_first_le_inclusive : ofPerson .first ≤ ofPerson .firstInclusive := by decide

theorem ofPerson_first_le_exclusive : ofPerson .first ≤ ofPerson .firstExclusive := by decide

theorem not_exclusive_le_inclusive : ¬ ofPerson .firstExclusive ≤ ofPerson .firstInclusive := by
  decide

/-- The first person with no clusivity and the inclusive unify to the inclusive. -/
theorem unify_ofPerson_first_inclusive :
    PartialUnify.unify (ofPerson .first) (ofPerson .firstInclusive) =
      ↑(ofPerson .firstInclusive) := by
  decide

/-- The first and the second person have no common extension. -/
theorem not_compat_first_second : ¬ Compat (ofPerson .first) (ofPerson .second) := by
  decide

end Specification

end Person
