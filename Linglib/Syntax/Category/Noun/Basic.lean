module

public import Linglib.Syntax.Gender.Basic
public import Linglib.Semantics.Reference.Sex
public import Linglib.Morphology.Word.Basic
public import Mathlib.Data.Finset.Option

/-!
# Noun

The noun as a lexical entry: its citation form and its gloss, everything a noun of any
language carries. A proper name extends the entry with the sex it restricts its referent to,
where it does, and projects as a third-person `PROPN` token; it is its own type rather than a
flag on the noun, since a name has no countability or plural and the syntax projects it as a
different head. A language with gender extends the entry with the controller gender in its own
carrier, the gender the language's assignment rules give the noun, and with the sex the noun
restricts its referents to where it does, Corbett's sex-differentiable nouns, the facet every
sex-based semantic core reads; the facets particular rules read besides, animacy, rationality,
declension class or accent, are the fields of the fragments' further extensions. Whether a
noun's gender is natural is a question about its language's semantic rules
(`Gender.IsNatural`). A classified noun records the ways a numeral counts it:
without a classifier, as in *three cups*, or with one, as in Mandarin *sān běn shū* 'three CL
book'. A noun that no numeral counts in either way, such as *milk*, is counted only through a
measure word, as in *three cups of milk*, and a count noun is one some numeral counts.

## Main definitions

* `Noun`: the noun entry.
* `ProperName`: the entry of a name, with the sex it restricts its referent to and its `Word`
  token.
* `GenderedNoun G`: the entry with its controller gender over the carrier `G` and the sex it
  restricts its referents to.
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
* [corbett-1991]
-/

@[expose] public section

/-- A noun entry records a citation form and a gloss. -/
structure Noun where
  /-- The citation form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  deriving DecidableEq, Repr

/-- A proper name is a noun that names its referent, restricted to a sex where it is. -/
structure ProperName extends Noun where
  /-- The sex the name restricts its referent to, where it does. -/
  sex : Option Sex := none
  deriving DecidableEq, Repr

/-- The word token of a name is a third-person `PROPN`, masculine or feminine by the sex it
restricts its referent to. -/
def ProperName.toWord (n : ProperName) : Morphology.Word :=
  { form := n.form, cat := .PROPN
    features := Morphology.Features.of (person := some .third)
      (gender := n.sex.map fun | .male => .masculine | .female => .feminine) }

/-- A noun with its controller gender over the carrier `G` and the sex it restricts its referents
to, where it does. -/
structure GenderedNoun (G : Type*) extends Noun where
  /-- The controller gender, the agreements the noun takes. -/
  gender : G
  /-- The sex the noun restricts its referents to, where it does: *vrač* 'doctor' and *sibling*
  restrict none. -/
  sex : Option Sex := none
  deriving DecidableEq, Repr

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
