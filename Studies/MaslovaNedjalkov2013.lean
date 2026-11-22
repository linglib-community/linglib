module

public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Languages
public import Linglib.Data.Examples.MaslovaNedjalkov2013
public import Linglib.Data.Examples.Readers
public import Linglib.Data.WALS.Features.F106A
public import Linglib.Syntax.Reciprocal
public import Linglib.Fragments.English.Reciprocals
public import Linglib.Fragments.German.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Voice
public import Linglib.Fragments.Mandarin.Reciprocals
public import Linglib.Fragments.Romance.French.Clitics
public import Linglib.Fragments.Romance.French.Reciprocals
public import Linglib.Fragments.Romance.Spanish.Clitics
public import Linglib.Fragments.Romance.Spanish.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Voice
public import Linglib.Fragments.Swahili.Reciprocals
public import Linglib.Fragments.Wambaya.Reciprocals
public import Linglib.Fragments.Wambaya.Voice

/-!
# Maslova and Nedjalkov (2013): Reciprocal Constructions

A reciprocal construction is *iconic* when it repeats the verb, once for each of the simple
situations that make up the reciprocal one, and *non-iconic* when a reciprocal marker in a single
clause does that work. A non-iconic construction is *reflexive* when it can also express the
reflexive meaning and *non-reflexive* otherwise. The map of [maslova-nedjalkov-2013] assigns a
language one of four values by two parameters, whether it has a reflexive reciprocal construction
and whether it has a non-reflexive one: neither (no non-iconic construction), only non-reflexive
ones, both (the mixed type), or only reflexive ones.

The two parameters are properties of a value of the map, `HasReflexive` and `HasNonReflexive`,
and determine it (`ofProps_eq_iff`). The value of an inventory of reciprocal markers, `ofInventory`,
is the one whose parameters are read off the markers that are not iconic, by whether their forms
are among those of the language's reflexive exponents; every language of the sample whose
reciprocal and reflexive exponents the fragments record has the value the map gives it
(`ofInventory_eq_wals`). In the chapter's examples the kind of a marker is in its gloss, a
reciprocal marker glossed as reflexive too or not: the marker an example shows is of a kind the
map's value for the language has (`value_of_shows`), an example with the reciprocal meaning
repeats a lexeme exactly when it has no reciprocal marker (`repeatsLexeme_iff_unmarked`), and the
two Lithuanian examples carry the reflexive reciprocal marker though neither has both meanings
(`lithuanian_unambiguous`).

## Implementation notes

The reflexive exponents are the fragments' reflexive pronouns, clitics, prefixes and voice
markers, compared with the reciprocal markers by form. Identity of form does not tell polysemy
from accidental homophony, and the chapter's criterion is the same formal one. An example shows
only some of a language's constructions, so `value_of_shows` bounds the map's value by an example
and does not compute it: the Cantonese example is iconic and the Lithuanian ones show the
reflexive marker alone, while the map gives Cantonese only non-reflexive constructions and
Lithuanian the mixed type. A slash in a gloss separates the meanings of one morpheme. The
statements of the chapter about the distribution of the values over areas are about regions and
a sample of 100 languages that the map's data do not delimit, and are not formalized.

## TODO

Mandarin, which the map gives only non-reflexive constructions, is left out of `Language` until
its fragment records the adverb *hùxiāng*: the one marker it records is iconic
(`ofInventory_mandarin`).

## References

* [E. Maslova and V. P. Nedjalkov, *Reciprocal Constructions* (2013)][maslova-nedjalkov-2013]
-/

@[expose] public section

namespace MaslovaNedjalkov2013

open Reciprocal Data.WALS.F106A

/-! ### The two parameters -/

/-- The value is one of a language with a reflexive reciprocal construction. -/
def HasReflexive (v : ReciprocalType) : Prop := v = .mixed ∨ v = .identicalToReflexive

/-- The value is one of a language with a non-reflexive reciprocal construction. -/
def HasNonReflexive (v : ReciprocalType) : Prop := v = .distinctFromReflexive ∨ v = .mixed

instance : DecidablePred HasReflexive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred HasNonReflexive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The value of a language that has a reflexive reciprocal construction if `r` and a
non-reflexive one if `n`. -/
def ofProps (r n : Prop) [Decidable r] [Decidable n] : ReciprocalType :=
  if r then if n then .mixed else .identicalToReflexive
  else if n then .distinctFromReflexive else .noReciprocalConstruction

section

variable {r n : Prop} [Decidable r] [Decidable n] {v w : ReciprocalType}

/-- A value of the map is determined by whether the language has a reflexive reciprocal
construction and whether it has a non-reflexive one. -/
theorem ofProps_eq_iff : ofProps r n = v ↔ (HasReflexive v ↔ r) ∧ (HasNonReflexive v ↔ n) := by
  unfold ofProps HasReflexive HasNonReflexive
  cases v <;> split_ifs <;> simp_all

@[simp]
theorem hasReflexive_ofProps : HasReflexive (ofProps r n) ↔ r := (ofProps_eq_iff.1 rfl).1

@[simp]
theorem hasNonReflexive_ofProps : HasNonReflexive (ofProps r n) ↔ n := (ofProps_eq_iff.1 rfl).2

@[simp]
theorem ofProps_hasReflexive_hasNonReflexive : ofProps (HasReflexive v) (HasNonReflexive v) = v :=
  ofProps_eq_iff.2 ⟨.rfl, .rfl⟩

theorem ofProps_eq_noReciprocalConstruction_iff :
    ofProps r n = .noReciprocalConstruction ↔ ¬ r ∧ ¬ n := by
  simp [ofProps_eq_iff, HasReflexive, HasNonReflexive]

end

/-! ### The value of an inventory -/

/-- A marker is iconic when its exponent repeats the verb, as a compound of two copies does. -/
def Iconic (m : Marker) : Prop := m.strategy = .compoundVerb

instance : DecidablePred Iconic := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The value of an inventory of reciprocal markers against a language's reflexive forms `F`: the
language has a reflexive reciprocal construction when the form of some non-iconic marker is among
them, and a non-reflexive one when the form of some non-iconic marker is not. -/
def ofInventory (inv : Finset Marker) (F : Finset (List Morphology.Morph)) : ReciprocalType :=
  ofProps (∃ m ∈ inv, ¬ Iconic m ∧ m.morphs ∈ F) (∃ m ∈ inv, ¬ Iconic m ∧ m.morphs ∉ F)

variable {inv : Finset Marker} {F : Finset (List Morphology.Morph)}

@[simp]
theorem hasReflexive_ofInventory :
    HasReflexive (ofInventory inv F) ↔ ∃ m ∈ inv, ¬ Iconic m ∧ m.morphs ∈ F :=
  hasReflexive_ofProps

@[simp]
theorem hasNonReflexive_ofInventory :
    HasNonReflexive (ofInventory inv F) ↔ ∃ m ∈ inv, ¬ Iconic m ∧ m.morphs ∉ F :=
  hasNonReflexive_ofProps

theorem ofInventory_eq_noReciprocalConstruction_iff :
    ofInventory inv F = .noReciprocalConstruction ↔ ∀ m ∈ inv, Iconic m := by
  rw [ofInventory, ofProps_eq_noReciprocalConstruction_iff]
  constructor
  · rintro ⟨hr, hn⟩ m hm
    by_contra hi
    by_cases hF : m.morphs ∈ F
    exacts [hr ⟨m, hm, hi, hF⟩, hn ⟨m, hm, hi, hF⟩]
  · exact fun h ↦ ⟨fun ⟨m, hm, hi, _⟩ ↦ hi (h m hm), fun ⟨m, hm, hi, _⟩ ↦ hi (h m hm)⟩

/-! ### The sample -/

/-- The languages of the chapter's sample whose reciprocal markers a fragment records. -/
inductive Language where
  | english | french | german | greek | russian | spanish | swahili | wambaya
  deriving DecidableEq

/-- The WALS code under which the chapter's data lists the language. -/
def Language.walsCode : Language → String
  | .english => "eng" | .french => "fre" | .german => "ger" | .greek => "grk"
  | .russian => "rus" | .spanish => "spa" | .swahili => "swa" | .wambaya => "wam"

/-- The language's reciprocal markers, from its fragment. -/
def Language.markers : Language → Finset Marker
  | .english => English.Reciprocals.markers
  | .french => French.Reciprocals.markers
  | .german => German.Reciprocals.markers
  | .greek => Greek.StandardModern.Reciprocals.markers
  | .russian => Russian.Reciprocals.markers
  | .spanish => Spanish.Reciprocals.markers
  | .swahili => Swahili.Reciprocals.markers
  | .wambaya => Wambaya.Reciprocals.markers

/-- The forms of the language's reflexive exponents, taken from its fragments, are those of its
reflexive pronouns and clitics as free forms, the Swahili object-slot prefix, and the markers of
its reflexive voices. -/
def Language.reflexives : Language → Finset (List Morphology.Morph)
  | .english => English.Pronouns.reflexives.image fun r ↦ [.free r.form]
  | .french => {[.free French.Clitics.se.form]}
  | .german => {[.free German.Pronouns.sich.form]}
  | .greek => {Greek.StandardModern.reflexive.marker}
  | .russian => {Russian.reflexive.marker, [.free Russian.Reciprocals.sebja.form]}
  | .spanish => Spanish.Clitics.reflexive.image fun r ↦ [.free r.form]
  | .swahili => {[Swahili.Reciprocals.reflexivePrefix]}
  | .wambaya => {Wambaya.reflexive.marker}

/-! ### The fragments' inventories -/

-- English has only non-reflexive reciprocals and German is of the mixed type (§2.2).
theorem ofInventory_english :
    ofInventory English.Reciprocals.markers (Language.reflexives .english) =
      .distinctFromReflexive := by
  decide

theorem ofInventory_german :
    ofInventory German.Reciprocals.markers (Language.reflexives .german) = .mixed := by
  decide

theorem ofInventory_mandarin :
    ofInventory Mandarin.Reciprocals.markers F = .noReciprocalConstruction :=
  ofInventory_eq_noReciprocalConstruction_iff.2 (by decide)

/-- Every language of the sample whose reciprocal and reflexive exponents the fragments record
has the value the map gives it. -/
theorem ofInventory_eq_wals (l : Language) :
    allData.lookup l.walsCode = some (ofInventory l.markers l.reflexives) := by
  cases l <;> decide +kernel

/-! ### The chapter's examples -/

/-- The meanings a morpheme's gloss gives it, a slash separating those of a polysemous one. -/
def meanings (m : GlossedMorpheme) : List (List Char) :=
  (Gloss.elements m.gloss).flatMap (Gloss.split ['/'])

/-- The example has a reciprocal marker that is glossed as reflexive too. -/
def ShowsReflexive (e : Datum) : Prop :=
  ∃ w ∈ e.glossedWords, ∃ m ∈ w.glossedMorphemes,
    "RECP".toList ∈ meanings m ∧ "REFL".toList ∈ meanings m

/-- The example has a reciprocal marker that is not glossed as reflexive. -/
def ShowsNonReflexive (e : Datum) : Prop :=
  ∃ w ∈ e.glossedWords, ∃ m ∈ w.glossedMorphemes,
    "RECP".toList ∈ meanings m ∧ "REFL".toList ∉ meanings m

/-- The example repeats a lexeme: two of its morphemes have the same lexical gloss. -/
def RepeatsLexeme (e : Datum) : Prop :=
  ¬ (e.glossedWords.flatMap fun w ↦ w.glosses.filter (¬ Gloss.IsLabel ·)).Nodup

instance : DecidablePred ShowsReflexive :=
  fun e ↦ inferInstanceAs (Decidable (∃ w ∈ e.glossedWords, _))
instance : DecidablePred ShowsNonReflexive :=
  fun e ↦ inferInstanceAs (Decidable (∃ w ∈ e.glossedWords, _))
instance : DecidablePred RepeatsLexeme := fun _ ↦ inferInstanceAs (Decidable (¬ _))

/-- The WALS codes of the languages of the chapter's examples. -/
def walsCodes : List (Glottocode × String) :=
  [(.cantonese, "cnt"), (.southernYukaghir, "yko"), (.imbaburaHighlandQuichua, "qim"),
    (.amele, "ame"), (.godié, "gdi"), (.kalaallisut, "grw"), (.ngiyambaa, "ngi"), (.wari, "war"),
    (.lithuanian, "lit")]

/-- The value the map gives the language of an example. -/
def value? (e : Datum) : Option ReciprocalType :=
  (e.byLanguage walsCodes).bind (List.lookup · allData)

/-- The marker an example shows is of a kind the map's value for its language has, and the map
has a value for the language of each of the twelve examples. -/
theorem value_of_shows :
    (∀ e ∈ Examples.all, ∀ v ∈ value? e,
      (ShowsReflexive e → HasReflexive v) ∧ (ShowsNonReflexive e → HasNonReflexive v)) ∧
      Datum.ReadCount value? Examples.all 12 := by
  decide +kernel

/-- An example with the reciprocal meaning is iconic, repeating a lexeme, exactly when it has no
reciprocal marker. -/
theorem repeatsLexeme_iff_unmarked :
    ∀ e ∈ Examples.all, Examples.reading e .reciprocal = some .acceptable →
      (RepeatsLexeme e ↔ ¬ ShowsReflexive e ∧ ¬ ShowsNonReflexive e) := by
  decide +kernel

theorem showsReflexive_of_reading :
    ∀ e ∈ Examples.all, Examples.reading e .reflexive = some .acceptable → ShowsReflexive e := by
  decide +kernel

/-- Both Lithuanian examples carry the reflexive reciprocal marker, and neither has both the
reciprocal and the reflexive meaning. -/
theorem lithuanian_unambiguous :
    ∀ e ∈ Examples.all.filter (·.language = .lithuanian),
      ShowsReflexive e ∧ ∃ r ∈ [.reciprocal, .reflexive],
        Examples.reading e r = some .unacceptable := by
  decide +kernel

theorem length_lithuanian : (Examples.all.filter (·.language = .lithuanian)).length = 2 := by
  decide +kernel

end MaslovaNedjalkov2013
