module

public import Linglib.Fragments.English.Particles
public import Linglib.Fragments.Slavic.Russian.QuestionParticles
public import Linglib.Fragments.Turkish.QuestionParticles
public import Linglib.Morphology.Word.Comparative
public import Studies.Haspelmath2023

/-!
# Haspelmath (2023): Types of clitics in the world's languages

A clitic is a bound morph that is neither an affix nor a root, where an affix always occurs on
roots of one class. A clitic is an enclitic when it can occur at the end of a free form but not at
the beginning, a proclitic when it can occur at the beginning but not at the end, an ambiclitic
when it can occur at both, and an interclitic when it can occur at neither. A second-position
clitic must occur directly after the first word of its clause. These are properties of a morph's
distribution over the free forms of its language, `Morphology.Comparative.Inventory`, and this
file checks them against the paper's examples and against the attachment the fragments record
for the same morphs.

## Main definitions

* `Haspelmath2023c.IsEnclitic`, `IsProclitic`, `IsAmbiclitic`, `IsInterclitic`: the positional
  types of a clitic.
* `Haspelmath2023c.IsSecondPosition`: a clitic that follows the first word of every free form
  it occurs in.

## Main results

* `Haspelmath2023c.isClitic_iff`: every clitic is of exactly one positional type.
* `Haspelmath2023c.li_followsFirstWord`: Russian *li* directly follows the first word of its
  question.
* `Haspelmath2023c.mi_isEnclitic`: Turkish *mI* is an enclitic.
* `Haspelmath2023c.however_isAmbiclitic`: English *however* is an ambiclitic.

## Implementation notes

* An ambiclitic is taken to occur both at the end and at the beginning of free forms, so that the
  four positional types are exclusive.
* Second position is stated for the first word, the first maximal run of morphs joined as
  affixes; the first nominal or adverbial expression and clitic clusters are not represented.
* The Turkish verb forms are segmented into a stem and the past suffix, which the paper writes
  unsegmented. An adverb is a free morph with no root class.
* The roots of each inventory are its contentful morphs, as in `Studies.Haspelmath2023`.

## TODO

* Read the free forms from example rows in boundary notation.
* `Morphology.Comparative.Inventory.IsAffix` holds of *li* on the three Russian questions, in each
  of which the noun *Anna* follows it: occurrence on a root does not distinguish the word a morph
  follows from the word it precedes, and the affixes it is reached through are those of any set
  the definition maps into itself. `Haspelmath2023c.IsSecondPosition` of *li* waits on a
  definition of the affix that reads the three questions as the paper does, with *li* on the
  verb, the noun and the adverb before it.

## References

* [haspelmath-2023c]
* [haspelmath-2023]
* [haspelmath-2021c]
-/

@[expose] public section

namespace Haspelmath2023c

open Morphology Morphology.Comparative

/-! ### Positional types -/

section Positional

variable {M : Type*} (L : Inventory M) (root : M → Prop) (x : M)

/-- The morph occurs at the end of a free form. -/
def OccursFinally : Prop := ∃ w ∈ L.forms, w.getLast? = some x

/-- The morph occurs at the beginning of a free form. -/
def OccursInitially : Prop := ∃ w ∈ L.forms, w.head? = some x

/-- An enclitic is a clitic that can occur at the end of a free form but not at the beginning. -/
def IsEnclitic : Prop := L.IsClitic root x ∧ OccursFinally L x ∧ ¬ OccursInitially L x

/-- A proclitic is a clitic that can occur at the beginning of a free form but not at the end. -/
def IsProclitic : Prop := L.IsClitic root x ∧ OccursInitially L x ∧ ¬ OccursFinally L x

/-- An ambiclitic is a clitic that can occur at the end of a free form and at the beginning. -/
def IsAmbiclitic : Prop := L.IsClitic root x ∧ OccursFinally L x ∧ OccursInitially L x

/-- An interclitic is a clitic that can occur neither at the end of a free form nor at the
beginning. -/
def IsInterclitic : Prop := L.IsClitic root x ∧ ¬ OccursFinally L x ∧ ¬ OccursInitially L x

variable {L root x}

/-- Every clitic is an enclitic, a proclitic, an ambiclitic or an interclitic. -/
theorem isClitic_iff :
    L.IsClitic root x ↔
      IsEnclitic L root x ∨ IsProclitic L root x ∨ IsAmbiclitic L root x ∨
        IsInterclitic L root x := by
  unfold IsEnclitic IsProclitic IsAmbiclitic IsInterclitic
  by_cases hf : OccursFinally L x <;> by_cases hi : OccursInitially L x <;> simp [hf, hi]

theorem IsEnclitic.not_isProclitic (h : IsEnclitic L root x) : ¬ IsProclitic L root x :=
  fun h' ↦ h.2.2 h'.2.1

/-- A morph that is a free form is not a clitic. -/
theorem not_isClitic_of_mem_forms (h : [x] ∈ L.forms) : ¬ L.IsClitic root x := fun hc ↦ hc.1 h

section Decidable

variable (L root x) [DecidableEq M] [DecidablePred root]

instance : Decidable (OccursFinally L x) := inferInstanceAs (Decidable (∃ w ∈ L.forms, _))

instance : Decidable (OccursInitially L x) := inferInstanceAs (Decidable (∃ w ∈ L.forms, _))

instance : Decidable (IsEnclitic L root x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsProclitic L root x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsAmbiclitic L root x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance : Decidable (IsInterclitic L root x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end Positional

/-- The morph directly follows the first word of the form, the first run of morphs joined as
affixes. -/
def FollowsFirstWord (x : Morph) (w : List Morph) : Prop :=
  ((Morph.wordsAt .affix w).drop 1).head? = some [x]

instance (x : Morph) (w : List Morph) : Decidable (FollowsFirstWord x w) :=
  inferInstanceAs (Decidable (_ = _))

/-- A second-position clitic is a clitic that directly follows the first word of every free form
it occurs in. -/
def IsSecondPosition (L : Inventory Morph) (root : Morph → Prop) (x : Morph) : Prop :=
  L.IsClitic root x ∧ ∀ w ∈ L.forms, x ∈ w → FollowsFirstWord x w

instance (L : Inventory Morph) (root : Morph → Prop) [DecidablePred root] (x : Morph) :
    Decidable (IsSecondPosition L root x) :=
  inferInstanceAs (Decidable (_ ∧ ∀ w ∈ L.forms, _))

/-! ### Russian *li* -/

/-- The Russian action root *pročita* 'read'. -/
def procita : Morph := .root "pročita"
/-- The Russian action root *čita* 'read'. -/
def cita : Morph := .root "čita"
/-- The Russian past suffix *-la*. -/
def la : Morph := .suff "la"
/-- The Russian object root *Anna*. -/
def anna : Morph := .root "Anna"
/-- The Russian object root *knigu* 'book'. -/
def knigu : Morph := .root "knigu"
/-- The Russian adverb *včera* 'yesterday'. -/
def vcera : Morph := .free "včera"

/-- The Russian questions *Pročita-la li Anna knigu?*, *Knigu li Anna pročita-la?* and
*Včera li Anna čita-la?*, with the fragment's morph for *li*. -/
def russian : Inventory Morph where
  forms :=
    [[procita, la] ++ Russian.QuestionParticles.li.morphs ++ [anna, knigu],
     knigu :: Russian.QuestionParticles.li.morphs ++ [anna, procita, la],
     vcera :: Russian.QuestionParticles.li.morphs ++ [anna, cita, la]]
  rootClass m :=
    if m = procita ∨ m = cita then some .action
    else if m = anna ∨ m = knigu then some .object else none

/-- Russian *li* directly follows the first word of each question, a verb, a noun or an adverb,
which is the placement the fragment records. -/
theorem li_followsFirstWord :
    (∀ m ∈ Russian.QuestionParticles.li.morphs, ∀ w ∈ russian.forms, FollowsFirstWord m w) ∧
      .second ∈ Russian.QuestionParticles.li.placements := by
  decide

theorem la_isAffix : russian.IsAffix russian.IsContentful la := by decide

/-! ### Turkish *mI* -/

/-- The Turkish action root *gel* 'come'. -/
def gel : Morph := .root "gel"
/-- The Turkish action root *öl* 'die'. -/
def ol : Morph := .root "öl"
/-- The Turkish past suffix -DI. -/
def di : Morph := .suff "DI"
/-- The Turkish object root *Ali*. -/
def ali : Morph := .root "Ali"
/-- The Turkish adverb *dün* 'yesterday'. -/
def dun : Morph := .free "dün"

/-- The Turkish questions *geldi mi?*, *öldü mü?*, *Ali mi?* and *dün mü?*, with the fragment's
morph for *mI*. -/
def turkish : Inventory Morph where
  forms :=
    [[gel, di] ++ Turkish.QuestionParticles.mi.morphs,
     [ol, di] ++ Turkish.QuestionParticles.mi.morphs,
     ali :: Turkish.QuestionParticles.mi.morphs,
     dun :: Turkish.QuestionParticles.mi.morphs]
  rootClass m := if m = gel ∨ m = ol then some .action else if m = ali then some .object else none

/-- Turkish *mI* follows a verb, a noun and an adverb and ends each question, so it is an
enclitic, the attachment the fragment records. -/
theorem mi_isEnclitic :
    ∀ m ∈ Turkish.QuestionParticles.mi.morphs,
      IsEnclitic turkish turkish.IsContentful m ∧ m.kind = .bound .after .clitic := by
  decide

/-- On the verb forms alone *mI* would be an affix: it is its occurrence on a noun that makes it
a clitic. -/
theorem mi_isAffix_of_verbs :
    ∀ m ∈ Turkish.QuestionParticles.mi.morphs,
      ({ turkish with forms := turkish.forms.take 2 } : Inventory Morph).IsAffix
        turkish.IsContentful m := by
  decide

/-! ### English -/

/-- The English object root *friend*. -/
def friend : Morph := .root "friend"
/-- The English object root *house*. -/
def house : Morph := .root "house"
/-- The English article *the*. -/
def the : Morph := .procl "the"
/-- The English object root *boy*. -/
def boy : Morph := .root "boy"
/-- The English pronoun *I*. -/
def i : Morph := .procl "I"
/-- The English action root *like*. -/
def like : Morph := .root "like"
/-- The English property root *new*. -/
def new : Morph := .root "new"
/-- The English object root *bike*. -/
def bike : Morph := .root "bike"

open Haspelmath2023 (my s_gen «to» infinitives) in
/-- The English forms *my friend's*, *my friend's house* and *the boy I like's new bike*. -/
def genitives : Inventory Morph where
  forms := [[my, friend, s_gen], [my, friend, s_gen, house], [the, boy, i, like, s_gen, new, bike]]
  rootClass m :=
    if m = friend ∨ m = house ∨ m = boy ∨ m = bike then some .object
    else if m = like then some .action else if m = new then some .property else none

open Haspelmath2023 (s_gen «to» infinitives) in
theorem s_isEnclitic_to_isProclitic :
    IsEnclitic genitives genitives.IsContentful s_gen ∧
      IsProclitic infinitives infinitives.IsContentful «to» := by
  decide

/-- The English possessive *our*. -/
def our : Morph := .procl "our"
/-- The English property root *ambitious*. -/
def ambitious : Morph := .root "ambitious"
/-- The English object root *proposal*. -/
def proposal : Morph := .root "proposal"
/-- The English action root *fail*. -/
def fail : Morph := .root "fail"
/-- The English past suffix *-ed*. -/
def ed : Morph := .suff "ed"
/-- English *however*, written as a word. -/
def however : Morph := .free "however"

/-- The English sentences with *however* at the beginning, in the middle and at the end. -/
def howevers : Inventory Morph where
  forms :=
    [[however, our, ambitious, proposal, fail, ed], [our, ambitious, proposal, however, fail, ed],
     [our, ambitious, proposal, fail, ed, however]]
  rootClass m :=
    if m = proposal then some .object else if m = fail then some .action
    else if m = ambitious then some .property else none

/-- English *however* does not occur on its own and stands at either end of a sentence, so it is
an ambiclitic, though it is written and labelled as a free word. -/
theorem however_isAmbiclitic :
    IsAmbiclitic howevers howevers.IsContentful however ∧ however.kind = .free := by
  decide

/-- A response word is used on its own, so it is not a clitic. -/
theorem yes_not_isClitic (L : Inventory Morph) (root : Morph → Prop)
    (h : [English.PolarityParticles.yes] ∈ L.forms) :
    ¬ L.IsClitic root English.PolarityParticles.yes :=
  not_isClitic_of_mem_forms h

end Haspelmath2023c
