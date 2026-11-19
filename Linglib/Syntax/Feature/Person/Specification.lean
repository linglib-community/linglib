/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Compat
public import Linglib.Syntax.Feature.Person.Basic
public import Linglib.Syntax.Feature.Person.Clusivity
public import Mathlib.Data.Fintype.Powerset

/-!
# Person specifications

A *person specification* is the set of participant sets a form can be used for. A referent has
one participant set, but a form may cover several: English *we* covers the speaker alone and
the speaker with the addressee, while an inclusive pronoun covers only the second.

A specification that covers fewer participant sets is more specific, so
[the first person is less specific than the
inclusive](##Person.Specification.ofPerson_first_le_inclusive). Two specifications are
compatible when some participant set is covered by both;
[the first and the second person are not](##Person.Specification.not_compat_first_second). The
person slot of an agreement bundle is a specification (`Syntax/Feature/Bundle.lean`).

## Main definitions

* `Person.Specification`: a nonempty set of participant sets, more specific when smaller.
* `Person.Specification.sets`: the participant sets a specification covers.
* `Person.Specification.ofPerson`: the specification of a person value.
* `Person.Specification.ofParticipants`: the specification of a single referent.
* `Person.Specification.toPerson?`: the person value a specification is that of, if any.
* `Person.Specification.IsSAP`: every participant set it covers includes a participant.

## Implementation notes

The order is that of `{s : Finset α // s.Nonempty}ᵒᵈ` in `Core/Order/Compat.lean`, the
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

/-- A person value is read as the specification of what it covers. -/
instance : Coe Person Specification := ⟨ofPerson⟩

theorem ofPerson_injective : Function.Injective ofPerson := fun _ _ h ↦
  participantSets_injective (congrArg sets h)

/-- The person value a specification is that of, if any. -/
def toPerson? (x : Specification) : Option Person :=
  [Person.first, .second, .third].find? fun p ↦ ofPerson p = x

@[simp] theorem toPerson?_ofPerson (p : Person) : (ofPerson p).toPerson? = some p := by
  revert p; decide

theorem toPerson?_bot : (⊥ : Specification).toPerson? = none := by decide

/-- The specification of a referent with the participants `s`. -/
def ofParticipants (s : Finset Role) : Specification :=
  OrderDual.toDual ⟨{s}, Finset.singleton_nonempty s⟩

@[simp] theorem sets_ofParticipants (s : Finset Role) : (ofParticipants s).sets = {s} := rfl

/-- The specification of the general first person. -/
abbrev first : Specification := ofPerson .first

/-- The specification of the inclusive first person: the speaker with the addressee. -/
abbrev firstInclusive : Specification := ofParticipants {.speaker, .addressee}

/-- The specification of the exclusive first person: the speaker without the addressee. -/
abbrev firstExclusive : Specification := ofParticipants {.speaker}

/-- The specification of the second person. -/
abbrev second : Specification := ofPerson .second

/-- The specification of the third person. -/
abbrev third : Specification := ofPerson .third

/-- A specification covers a referent exactly when it covers the referent's participants. -/
theorem le_ofParticipants_iff {x : Specification} {s : Finset Role} :
    x ≤ ofParticipants s ↔ s ∈ x.sets :=
  Finset.singleton_subset_iff

/-- The specification of an optional person narrowed by an optional clusivity: the participant
sets of the person, all of them where there is none, that satisfy the clusivity. It is
unspecified where no participant set does, as for the second person with the exclusive. -/
def ofPersonClusivity (p : Option Person) (c : Option Clusivity) : Specification :=
  if h : (Clusivity.restrict c (p.elim Finset.univ participantSets)).Nonempty then
    OrderDual.toDual ⟨_, h⟩
  else ⊥

@[simp] theorem ofPersonClusivity_none_none : ofPersonClusivity none none = ⊥ := by decide

@[simp] theorem ofPersonClusivity_some_none (p : Person) :
    ofPersonClusivity (some p) none = ofPerson p := by
  revert p; decide

theorem ofPersonClusivity_first_inclusive :
    ofPersonClusivity (some .first) (some .inclusive) = firstInclusive := by
  decide

theorem ofPersonClusivity_first_exclusive :
    ofPersonClusivity (some .first) (some .exclusive) = firstExclusive := by
  decide

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
theorem ofPerson_first_le_inclusive : first ≤ firstInclusive := by decide

theorem ofPerson_first_le_exclusive : first ≤ firstExclusive := by decide

theorem not_exclusive_le_inclusive : ¬ firstExclusive ≤ firstInclusive := by decide

/-- The first person with no clusivity and the inclusive unify to the inclusive. -/
theorem isLUB_first_inclusive : IsLUB {first, firstInclusive} firstInclusive := by
  decide

/-- The first and the second person have no common extension. -/
theorem not_compat_first_second : ¬ Compat first second := by
  decide

end Specification

end Person

namespace Clusivity

/-- With no person specified, the inclusive participant sets are those of the second person and
of the inclusive first person. -/
theorem restrict_inclusive_univ :
    restrict (some inclusive) Finset.univ =
      Person.second.participantSets ∪ {{.speaker, .addressee}} := by
  decide

end Clusivity
