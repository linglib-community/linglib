module

public import Linglib.Syntax.Person.Basic
public import Linglib.Syntax.Person.Clusivity
public import Linglib.Syntax.Person.Lattice
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-!
# Referential person categories

Cysouw's eight referential person categories configure the speech-act participants a referent
contains with the others it contains, none, one or several: the three singular participants and the
five attested groups. [They are exactly the well-formed
configurations](##Person.Category.toConfig_bijective), the two groups this excludes being several
speakers and an audience with no one else. A category has a person and, when it is a group
with the speaker, a clusivity (`Person.Category.person`, `Person.Category.clusivity`), and
[every category is recovered from the two at some
number](##Person.Category.ofPersonNumber_person).

Person and clusivity together lie strictly between two partitions of the categories,
[coarser](##Person.Category.person_eq_of_participants_eq_of_isGroup_iff) than participants
together with being a group and [finer](##Person.Category.participants_eq_of_person_eq) than
participants alone. The speaker alone and the speaker with others share their participants, so
they are one person where a person is a set of participants, as for Harbour and for Dalrymple
and Kaplan, and differ in clusivity where the exclusive is a group, as here.

## References

* [cysouw-2003]
* [harbour-2016]
* [dalrymple-kaplan-2000]
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
def participants : Category → Finset SpeechAct.Role
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
def WellFormed (x : Finset SpeechAct.Role × Fin 3) : Prop :=
  (x.1.Nonempty ∨ x.2 ≠ 0) ∧ (x.2 = 2 → x.1 = ∅)

instance : DecidablePred WellFormed := fun _ ↦ by unfold WellFormed; infer_instance

/-- The configuration of a category. -/
def toConfig (c : Category) : {x // WellFormed x} :=
  ⟨(c.participants, c.otherCount), by cases c <;> decide +kernel⟩

/-- The categories are exactly the well-formed configurations. -/
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

/-- The person of a category: first with the speaker, otherwise second with the addressee,
otherwise third. -/
def person (c : Category) : Person := (Person.ofParticipants c.participants).coarsen

/-- The clusivity of a category: a group with the speaker includes or excludes the addressee,
clusivity being a property of groups. -/
def clusivity (c : Category) : Option Clusivity :=
  if c.IsGroup ∧ .speaker ∈ c.participants then
    some (if .addressee ∈ c.participants then .inclusive else .exclusive)
  else none

theorem person_includesSpeaker_iff (c : Category) :
    c.person.IncludesSpeaker ↔ c.IncludesSpeaker := by
  cases c <;> decide +kernel

theorem participants_mem_participantSets_person (c : Category) :
    c.participants ∈ c.person.participantSets := by
  cases c <;> decide

theorem clusivity_separates :
    Category.speakerAddresseeOthers.clusivity ≠ Category.speakerOthers.clusivity := by decide

/-- A clusivity a category has holds of its participants. -/
theorem holds_of_mem_clusivity {c : Category} {cl : Clusivity} (h : cl ∈ c.clusivity) :
    cl.Holds c.participants := by
  revert h; revert c cl; decide

/-- Categories of one person and one clusivity have the same participants. -/
theorem participants_eq_of_person_eq {a b : Category} (h : a.person = b.person)
    (hc : a.clusivity = b.clusivity) : a.participants = b.participants := by
  revert a b; decide

/-- Categories with the same participants that are both groups or both individuals have one
person and one clusivity. -/
theorem person_eq_of_participants_eq_of_isGroup_iff {a b : Category}
    (h : a.participants = b.participants) (hg : a.IsGroup ↔ b.IsGroup) :
    a.person = b.person ∧ a.clusivity = b.clusivity := by
  revert a b; decide

/-- The speaker and the addressee together are a group. -/
theorem isGroup_of_participants_eq_univ {c : Category} (h : c.participants = Finset.univ) :
    c.IsGroup := by
  revert c; decide

/-- Both refinements are strict: the speaker alone and with others share their participants and
not their clusivity, and the addressee alone and with others share their person and clusivity
and are not both groups. -/
theorem person_strictly_between :
    (Category.speaker.participants = Category.speakerOthers.participants ∧
      Category.speaker.clusivity ≠ Category.speakerOthers.clusivity) ∧
    (Category.addressee.person = Category.addresseeOthers.person ∧
      Category.addressee.clusivity = Category.addresseeOthers.clusivity ∧
      ¬ (Category.addressee.IsGroup ↔ Category.addresseeOthers.IsGroup)) := by
  decide

/-- The categories a person, an optional clusivity and a number can realize. The
minimal/augmented coordinates give the minimal/augmented inclusives directly (Tagalog *kata* is
first person, inclusive, minimal, `{speakerAddressee}`). A non-singular first person with no
clusivity is the syncretism `{speakerAddressee, speakerAddresseeOthers, speakerOthers}` (English
*we*), except that the speaker and the addressee alone are two and minimal, so the trial, the
augmented and the unit augmented realize only the groups with others. General number is
noncommittal between the singular and the group category (the second person at the general
number is `{addressee, addresseeOthers}`). A singular or minimal with the exclusive realizes
nothing, and neither does a clusivity on the second or the third person. -/
def ofPersonNumber : Person → Option Clusivity → Number → Finset Category
  | .first, none, .singular | .first, none, .minimal => {.speaker}
  | .first, none, .dual => {.speakerAddressee, .speakerOthers}
  | .first, none, .trial | .first, none, .augmented | .first, none, .unitAugmented =>
    {.speakerAddresseeOthers, .speakerOthers}
  | .first, none, .general =>
    {.speaker, .speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .first, none, _ => {.speakerAddressee, .speakerAddresseeOthers, .speakerOthers}
  | .first, some .inclusive, .singular => ∅
  | .first, some .inclusive, .minimal | .first, some .inclusive, .dual => {.speakerAddressee}
  | .first, some .inclusive, .general => {.speakerAddressee, .speakerAddresseeOthers}
  | .first, some .inclusive, _ => {.speakerAddresseeOthers}
  | .first, some .exclusive, .singular | .first, some .exclusive, .minimal => ∅
  | .first, some .exclusive, _ => {.speakerOthers}
  | .second, none, .singular | .second, none, .minimal => {.addressee}
  | .second, none, .general => {.addressee, .addresseeOthers}
  | .second, none, _ => {.addresseeOthers}
  | .third, none, .singular | .third, none, .minimal => {.other}
  | .third, none, .general => {.other, .others}
  | .third, none, _ => {.others}
  | _, _, _ => ∅

/-- `ofPersonNumber` inverts the person and clusivity projections, recovering every category from
its coordinates at some number value. -/
theorem ofPersonNumber_person (c : Category) :
    ∃ n, ofPersonNumber c.person c.clusivity n = {c} := by
  cases c
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.singular, rfl⟩
  · exact ⟨.minimal, rfl⟩
  · exact ⟨.augmented, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩
  · exact ⟨.plural, rfl⟩

/-- A category without others has exactly its participants, so a number value of fixed
cardinality realizes it only at that cardinality. -/
theorem exactCard_eq_card_of_mem_ofPersonNumber :
    ∀ p cl n c, c ∈ ofPersonNumber p cl n → c.otherCount = 0 →
      ∀ k ∈ n.exactCard, (k : ℕ) = c.card := by
  decide

/-- No category is both minimal and augmented, whatever the person values: `[−minimal]` is the
complement of `[+minimal]`. -/
theorem disjoint_ofPersonNumber_minimal_augmented (p q : Person) (c d : Option Clusivity) :
    Disjoint (ofPersonNumber p c .minimal) (ofPersonNumber q d .augmented) := by
  revert p q c d; decide

/-! ### The person and number of a set of categories

A form that can denote several categories, the polite German *Sie* for an addressee or
addressees or English *we* for any group containing the speaker, has a person and a number
only up to the values neutral between them, the clusivity-unmarked `first` and the
noncommittal `general`. -/

/-- The person shared by a set of referential categories: first where all include the speaker,
second where all include the addressee and not the speaker, third where none includes either,
and `none` for the empty set and for categories disagreeing on the roles they include. -/
def sharedPerson (s : Finset Category) : Option Person :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.IncludesSpeaker then some .first
  else if ∀ c ∈ s, c.IncludesAddressee ∧ ¬ c.IncludesSpeaker then some .second
  else if ∀ c ∈ s, ¬ c.IncludesSpeaker ∧ ¬ c.IncludesAddressee then some .third
  else none

/-- The clusivity shared by a set of referential categories: one that all of them have, and
`none` for the empty set and for categories that differ in clusivity or have none. -/
def sharedClusivity (s : Finset Category) : Option Clusivity :=
  if s = ∅ then none
  else if ∀ c ∈ s, c.clusivity = some .inclusive then some .inclusive
  else if ∀ c ∈ s, c.clusivity = some .exclusive then some .exclusive
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

theorem sharedClusivity_singleton (c : Category) : sharedClusivity {c} = c.clusivity := by
  cases c <;> decide

theorem sharedPerson_ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number)
    (h : (ofPersonNumber p cl n).Nonempty) : sharedPerson (ofPersonNumber p cl n) = some p := by
  revert h; revert p cl n; decide

theorem sharedClusivity_ofPersonNumber (p : Person) (cl : Option Clusivity) (n : Number)
    (h : (ofPersonNumber p cl n).Nonempty) : sharedClusivity (ofPersonNumber p cl n) = cl := by
  revert h; revert p cl n; decide

theorem sharedNumber_ofPersonNumber_eq_general (p : Person) (cl : Option Clusivity) (n : Number)
    (h : sharedNumber (ofPersonNumber p cl n) = some .general) : n = .general := by
  revert h; revert p cl n; decide

end Category

end Person
