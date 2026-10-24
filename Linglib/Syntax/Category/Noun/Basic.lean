module

public import Linglib.Syntax.Gender.Basic
public import Linglib.Morphology.Word.Basic
public import Mathlib.Data.Finset.Option

/-!
# Noun

The noun as a lexical entry: its citation form and its gloss, everything a noun of any
language carries. A proper name extends the entry with the natural gender its pronouns agree
with, where it has one, and projects as a third-person `PROPN` token; it is its own type rather
than a flag on the noun, since a name has no countability or plural and the syntax projects it
as a different head. A language with gender extends the entry with the controller gender in
its own carrier, the gender the language's assignment rules give the noun, and with the
gender of its referents where they have one, the one facet every system with a semantic core
reads; the facets particular rules read besides, animacy, rationality, declension class or
accent, are the fields of the fragments' further extensions. A noun's gender is natural when
it is the gender of its referents. A classified noun records the ways a numeral counts it:
without a classifier, as in *three cups*, or with one, as in Mandarin *sān běn shū* 'three CL
book'. A noun that no numeral counts in either way, such as *milk*, is counted only through a
measure word, as in *three cups of milk*, and a count noun is one some numeral counts.

## Main definitions

* `Noun`: the noun entry.
* `ProperName`: the entry of a name, with its natural gender and its `Word` token.
* `GenderedNoun G`: the entry with its controller gender over the carrier `G` and the gender of
  its referents.
* `GenderedNoun.IsNaturalGender`: the gender is the referents', under a labelling of the carrier.
* `ClassifiedNoun C`: the entry with the ways a numeral counts it, over the carrier `C` of
  classifiers.
* `ClassifiedNoun.IsCount`, `ClassifiedNoun.IsBareCount`, `ClassifiedNoun.classifiers`: some
  numeral counts the noun, a numeral counts it without a classifier, and the classifiers it is
  counted with.

## Implementation notes

The general concept takes the plain name and the specializations extend it, as in mathlib. A
fragment's extension is its own `Noun`, in its namespace; a file that opens that namespace
qualifies the name, the root `Noun` being in scope too. A noun that is count in one use and
mass in another, *many seeds* and *much seed*, has an entry for each class.

`IsCount` is a diagnostic of the numeral construction. It sorts Mandarin nouns by whether they
take a count-classifier, with Cheng and Sybesma, where Chierchia makes every Mandarin noun mass,
and in a language whose numerals combine with every noun it makes every noun count. A language
without classifiers takes `C := Empty`, so a numeral counts its nouns without one or not at
all.

## References

* [cheng-sybesma-1999]
* [chierchia-1998]
-/

@[expose] public section

/-- A noun entry records a citation form and a gloss. -/
structure Noun where
  /-- The citation form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr

/-- A proper name is a noun that names its referent, with the natural gender its pronouns agree
with, where it has one. -/
structure ProperName extends Noun where
  /-- The natural gender, where the name has one. -/
  gender : Option Gender.Label := none
  deriving DecidableEq, Repr

/-- The word token of a name is a third-person `PROPN` with the name's gender. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := Morphology.Features.of (person := some .third) (gender := n.gender) }

/-- A noun with its controller gender over the carrier `G` and the gender of its referents,
where they have one. -/
structure GenderedNoun (G : Type*) extends Noun where
  /-- The controller gender, the agreements the noun takes. -/
  gender : G
  /-- The gender of the referents, where they have one. -/
  naturalGender : Option Gender.Label := none
  deriving DecidableEq, Repr

namespace GenderedNoun

variable {G : Type*} (label : G → Gender.Label) (n : GenderedNoun G)

/-- A noun's gender is natural when, under the carrier's comparative labelling, it is the
gender of its referents. -/
def IsNaturalGender : Prop := n.naturalGender = some (label n.gender)

instance : Decidable (n.IsNaturalGender label) := inferInstanceAs (Decidable (_ = _))

end GenderedNoun

/-- A noun with the ways a numeral counts it, over the carrier `C` of the language's
classifiers. -/
structure ClassifiedNoun (C : Type*) extends Noun where
  /-- A numeral counts the noun without a classifier when `none` is a member, and with the
  classifier `c` when `some c` is. -/
  counters : Finset (Option C)
  deriving DecidableEq

namespace ClassifiedNoun

variable {C : Type*} (n : ClassifiedNoun C)

/-- A noun is count when some numeral counts it, by itself or through a classifier. -/
def IsCount : Prop := n.counters.Nonempty

instance : Decidable n.IsCount := Finset.decidableNonempty

/-- A noun is counted bare when a numeral counts it without a classifier. -/
def IsBareCount : Prop := none ∈ n.counters

instance [DecidableEq C] : Decidable n.IsBareCount := inferInstanceAs (Decidable (_ ∈ _))

/-- The classifiers a noun is counted with. -/
def classifiers : Finset C := Finset.eraseNone n.counters

@[simp] theorem mem_classifiers {c : C} : c ∈ n.classifiers ↔ some c ∈ n.counters :=
  Finset.mem_eraseNone

end ClassifiedNoun
