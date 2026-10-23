module

public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Person.Lattice
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-!
# Referential person categories

The eight referential person categories. A category is a configuration of the speech-act
participants a referent contains and of the others it contains, none, one or several: the three
singular participants and the five attested groups. The two groups this excludes, several
speakers and an audience with no one else, are the configurations `Category.WellFormed` rejects.

## Main definitions

* `Person.Category`: the eight categories.
* `Category.toConfig`: the configuration of a category, a bijection onto the well-formed ones.
* `Category.IsSingular`, `Category.IsGroup`, `Category.IsFirstPersonComplex`,
  `Category.IsInclusive`: the classes of categories read off the configuration.
* `Category.person`: the person projection, keeping clusivity on the groups.
* `Category.ofPersonNumber`: the categories a (person, number) coordinate pair realizes.
* `Category.sharedPerson`, `Category.sharedNumber`: the coordinates a set of categories
  shares, neutral values where they differ.

## Main results

* `Category.toConfig_bijective`: the categories are exactly the well-formed configurations.
* `Category.ofPersonNumber_person`: every category is recovered from its person at some number.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

@[expose] public section

namespace Person

/-- The eight referential person categories, the three singular participants and the five
attested groups. -/
inductive Category where
  /-- The speaker alone, Cysouw's 1. -/
  | speaker
  /-- The addressee alone, Cysouw's 2. -/
  | addressee
  /-- A single other, Cysouw's 3. -/
  | other
  /-- The minimal inclusive, speaker and addressee only, Cysouw's 1+2. -/
  | speakerAddressee
  /-- The augmented inclusive, speaker and addressee with others, Cysouw's 1+2+3. -/
  | speakerAddresseeOthers
  /-- The exclusive, speaker with others but not the addressee, Cysouw's 1+3. -/
  | speakerOthers
  /-- The addressee with others, Cysouw's 2+3. -/
  | addresseeOthers
  /-- Several others, Cysouw's 3+3. -/
  | others
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Category

variable {c : Category}

/-! ### Configurations -/

/-- The speech-act participants a category contains. -/
def participants : Category → Finset Discourse.Role
  | speaker | speakerOthers => {.speaker}
  | addressee | addresseeOthers => {.addressee}
  | speakerAddressee | speakerAddresseeOthers => {.speaker, .addressee}
  | other | others => ∅

/-- A category contains no others, one, or several, several counting as two. -/
def otherCount : Category → Fin 3
  | speaker | addressee | speakerAddressee => 0
  | other | speakerOthers | addresseeOthers | speakerAddresseeOthers => 1
  | others => 2

/-- A configuration of participants and others is a category iff it is nonempty and has
several others only on their own. The speaker and the addressee are unique individuals, so a
group of speakers or of addressees does not arise, and a participant with one other or with
several forms one group. -/
def WellFormed (x : Finset Discourse.Role × Fin 3) : Prop :=
  (x.1.Nonempty ∨ x.2 ≠ 0) ∧ (x.2 = 2 → x.1 = ∅)

instance : DecidablePred WellFormed := fun _ ↦ by unfold WellFormed; infer_instance

/-- The configuration of a category. -/
def toConfig (c : Category) : {x // WellFormed x} :=
  ⟨(c.participants, c.otherCount), by cases c <;> decide +kernel⟩

theorem toConfig_bijective : Function.Bijective toConfig :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- All eight categories in canonical order, singular then group. -/
def all : List Category :=
  [.speaker, .addressee, .other, .speakerAddressee, .speakerAddresseeOthers, .speakerOthers,
    .addresseeOthers, .others]

/-! ### Predicates -/

/-- The members of a category, several others counting as two. -/
def card (c : Category) : ℕ := c.participants.card + c.otherCount

/-- A singular category has one member. -/
def IsSingular (c : Category) : Prop := c.card = 1

/-- A group category has several members. -/
def IsGroup (c : Category) : Prop := 2 ≤ c.card

/-- The category includes the speaker. -/
def IncludesSpeaker (c : Category) : Prop := .speaker ∈ c.participants

/-- The category includes the addressee. -/
def IncludesAddressee (c : Category) : Prop := .addressee ∈ c.participants

/-- The first person complex consists of the groups including the speaker. -/
def IsFirstPersonComplex (c : Category) : Prop := c.IncludesSpeaker ∧ c.IsGroup

/-- An inclusive category includes both the speaker and the addressee. -/
def IsInclusive (c : Category) : Prop := c.IncludesSpeaker ∧ c.IncludesAddressee

instance : DecidablePred IsSingular := fun _ ↦ by unfold IsSingular; infer_instance
instance : DecidablePred IsGroup := fun _ ↦ by unfold IsGroup; infer_instance
instance : DecidablePred IncludesSpeaker := fun _ ↦ by unfold IncludesSpeaker; infer_instance
instance : DecidablePred IncludesAddressee := fun _ ↦ by
  unfold IncludesAddressee; infer_instance
instance : DecidablePred IsFirstPersonComplex := fun _ ↦ by
  unfold IsFirstPersonComplex; infer_instance
instance : DecidablePred IsInclusive := fun _ ↦ by unfold IsInclusive; infer_instance

theorem isGroup_iff_not_isSingular : c.IsGroup ↔ ¬ c.IsSingular := by
  revert c; decide +kernel

theorem IsInclusive.isFirstPersonComplex (h : c.IsInclusive) : c.IsFirstPersonComplex := by
  revert h; revert c; decide +kernel

theorem IsFirstPersonComplex.includesSpeaker (h : c.IsFirstPersonComplex) :
    c.IncludesSpeaker :=
  h.1

theorem IsInclusive.includesSpeaker (h : c.IsInclusive) : c.IncludesSpeaker := h.1

/-! ### The person projection -/

/-- The person of a category is the person of its participants, clusivity being a property of
groups. -/
def person (c : Category) : Person :=
  if c.IsGroup then Person.ofParticipants c.participants
  else (Person.ofParticipants c.participants).coarsen

theorem person_includesSpeaker_iff (c : Category) :
    c.person.IncludesSpeaker ↔ c.IncludesSpeaker := by
  cases c <;> decide +kernel

theorem participants_mem_participantSets_person (c : Category) :
    c.participants ∈ c.person.participantSets := by
  cases c <;> decide

theorem person_separates_clusivity :
    Category.speakerAddresseeOthers.person ≠ Category.speakerOthers.person := by decide +kernel

/-- The categories a (person, number) coordinate pair can realize. Clusivity rides on the
person value and the minimal/augmented coordinates give the minimal/augmented inclusives
directly (Tagalog *kata* = `(firstInclusive, minimal)` ↦ `{speakerAddressee}`). A
clusivity-unmarked non-singular first person is the syncretism
`{speakerAddressee, speakerAddresseeOthers, speakerOthers}` (English *we*), general number is
noncommittal between the singular and the group category (`(second, general)` ↦
`{addressee, addresseeOthers}`), and a singular bearing clusivity realizes nothing. -/
def ofPersonNumber : Person → Number → Finset Category
  | .first, .singular | .first, .minimal => {.speaker}
  | .first, .dual => {.speakerAddressee, .speakerOthers}
  | .first, .general => {.speaker, .speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .first, _ => {.speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .firstInclusive, .singular => ∅
  | .firstInclusive, .minimal | .firstInclusive, .dual => {.speakerAddressee}
  | .firstInclusive, .general => {.speakerAddressee, .speakerAddresseeOthers}
  | .firstInclusive, _ => {.speakerAddresseeOthers}
  | .firstExclusive, .singular => ∅
  | .firstExclusive, _ => {.speakerOthers}
  | .second, .singular | .second, .minimal => {.addressee}
  | .second, .general => {.addressee, .addresseeOthers}
  | .second, _ => {.addresseeOthers}
  | .third, .singular | .third, .minimal => {.other}
  | .third, .general => {.other, .others}
  | .third, _ => {.others}

theorem ofPersonNumber_person (c : Category) : ∃ n, ofPersonNumber c.person n = {c} := by
  cases c
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.minimal, rfl⟩
  · exact ⟨.augmented, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩

/-! ### The person and number of a set of categories

A form that can denote several categories, the polite German *Sie* for an addressee or
addressees or English *we* for any group containing the speaker, has a person and a number
only up to the values neutral between them, the clusivity-unmarked `first` and the
noncommittal `general`. -/

/-- The person shared by a set of referential categories is the common value of `person` where
there is one, `first` for categories differing only in clusivity, and `none` for the empty set
and for categories disagreeing on the speech-act roles they include. -/
def sharedPerson (s : Finset Category) : Option Person :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.IncludesSpeaker then
    if ∀ c ∈ s, c.person = .firstInclusive then some .firstInclusive
    else if ∀ c ∈ s, c.person = .firstExclusive then some .firstExclusive
    else some .first
  else if ∀ c ∈ s, c.IncludesAddressee ∧ ¬ c.IncludesSpeaker then some .second
  else if ∀ c ∈ s, ¬ c.IncludesSpeaker ∧ ¬ c.IncludesAddressee then some .third
  else none

/-- The number shared by a set of referential categories is singular or plural when the
categories agree, `general` when they mix individuals and groups, and `none` for the empty set.
Cysouw's categories do not separate dual from plural, so the projection is at that
granularity. -/
def sharedNumber (s : Finset Category) : Option Number :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.IsSingular then some .singular
  else if ∀ c ∈ s, c.IsGroup then some .plural
  else some .general

theorem sharedPerson_singleton (c : Category) : sharedPerson {c} = some c.person := by
  cases c <;> decide

theorem sharedPerson_ofPersonNumber (p : Person) (n : Number)
    (h : (ofPersonNumber p n).Nonempty) : sharedPerson (ofPersonNumber p n) = some p := by
  revert h; revert p n; decide

theorem sharedNumber_ofPersonNumber_eq_general (p : Person) (n : Number)
    (h : sharedNumber (ofPersonNumber p n) = some .general) : n = .general := by
  revert h; revert p n; decide

end Category

end Person
