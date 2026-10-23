module

public import Linglib.Fragments.Latin.Case
public import Linglib.Fragments.Latin.Gender

/-!
# Latin noun declension

Latin nouns inflect for six cases and two numbers, and the endings fuse case and number, and in
the first two declensions gender as well. Five declensions are traditionally recognised, named
for historical stem classes that are no longer transparent: ā-stems, o-stems, the third
declension with its consonant stems and i-stems, u-stems and ē-stems. The paradigms here are
the seven of Blake's table of Latin case paradigms.

No paradigm distinguishes all six cases. Two syncretisms predominate: nominative and accusative
fall together in every neuter and in many plurals, and dative and ablative fall together in
every plural, in the singular of the second declension and in the singular of the i-stems. The
vocative differs from the nominative only in the singular of non-neuter second-declension
nouns.

## Main declarations

* `Latin.Declension.forms`: the forms of the six cases, in the order of the school paradigms.
* `Latin.Declension.Noun`: a noun with its declension, genders and the form of each case in each
  number.
* `separatesPoints_paradigms`, `not_injective`: the paradigms of the table separate the six
  cases, though no one of them does.
* `nom_acc_syncretic_of_neuter`, `plural_dat_abl_syncretic`, `singular_dat_abl_syncretic_iff`,
  `singular_nom_voc_syncretic_iff`: the syncretisms, read off the forms.

## Implementation notes

Blake's table gives two forms for the ablative singular and the accusative plural of *cīvis*.
`Noun.singular` and `Noun.plural` hold the first, the i-stem form, and `civis.variant` the second.
The genders of the four nouns whose columns the table leaves unlabelled are the dictionary ones.

## References

* [blake-1994]
* [blake-2001]
-/

@[expose] public section

namespace Latin.Declension


/-- The declensions, the third split into consonant stems and i-stems. -/
inductive Class where
  | first
  | second
  | thirdConsonant
  | thirdI
  | fourth
  | fifth
  deriving DecidableEq, Repr

/-- The forms of the six cases, in the order of the school paradigms. -/
def forms (nom voc acc gen dat abl : String) : Case → String
  | .nom => nom
  | .voc => voc
  | .acc => acc
  | .gen => gen
  | .dat => dat
  | .abl => abl

/-- A noun by the form of each case in each number. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The declension. -/
  cls : Class
  /-- The genders the noun takes, two for a noun of common gender. -/
  genders : Finset Gender.Value
  /-- The singular form in each case. -/
  singular : Case → String
  /-- The plural form in each case. -/
  plural : Case → String

/-- The noun is neuter. -/
def Noun.IsNeuter (n : Noun) : Prop := n.genders = {.neut}

instance (n : Noun) : Decidable n.IsNeuter := inferInstanceAs (Decidable (_ = _))

/-- *domina* 'mistress', first declension. -/
def domina : Noun where
  gloss := "mistress"
  cls := .first
  genders := {.fem}
  singular := forms "domina" "domina" "dominam" "dominae" "dominae" "dominā"
  plural := forms "dominae" "dominae" "dominās" "dominārum" "dominīs" "dominīs"

/-- *dominus* 'master', second declension. -/
def dominus : Noun where
  gloss := "master"
  cls := .second
  genders := {.masc}
  singular := forms "dominus" "domine" "dominum" "dominī" "dominō" "dominō"
  plural := forms "dominī" "dominī" "dominōs" "dominōrum" "dominīs" "dominīs"

/-- *bellum* 'war', second declension neuter. -/
def bellum : Noun where
  gloss := "war"
  cls := .second
  genders := {.neut}
  singular := forms "bellum" "bellum" "bellum" "bellī" "bellō" "bellō"
  plural := forms "bella" "bella" "bella" "bellōrum" "bellīs" "bellīs"

/-- *cōnsul* 'consul', third declension consonant stem. -/
def consul : Noun where
  gloss := "consul"
  cls := .thirdConsonant
  genders := {.masc}
  singular := forms "cōnsul" "cōnsul" "cōnsulem" "cōnsulis" "cōnsulī" "cōnsule"
  plural := forms "cōnsulēs" "cōnsulēs" "cōnsulēs" "cōnsulum" "cōnsulibus" "cōnsulibus"

/-- *cīvis* 'citizen', third declension i-stem, of common gender. -/
def civis : Noun where
  gloss := "citizen"
  cls := .thirdI
  genders := {.masc, .fem}
  singular := forms "cīvis" "cīvis" "cīvem" "cīvis" "cīvī" "cīvī"
  plural := forms "cīvēs" "cīvēs" "cīvīs" "cīvium" "cīvibus" "cīvibus"

/-- The consonant-stem forms *cīvis* also takes: *cīve* in the ablative singular and *cīvēs* in
the accusative plural. -/
def civis.variant : Noun :=
  { civis with
    singular := Function.update civis.singular .abl "cīve"
    plural := Function.update civis.plural .acc "cīvēs" }

/-- *manus* 'hand', fourth declension. -/
def manus : Noun where
  gloss := "hand"
  cls := .fourth
  genders := {.fem}
  singular := forms "manus" "manus" "manum" "manūs" "manuī" "manū"
  plural := forms "manūs" "manūs" "manūs" "manuum" "manibus" "manibus"

/-- *diēs* 'day', fifth declension, masculine, and feminine of an appointed day. -/
def dies : Noun where
  gloss := "day"
  cls := .fifth
  genders := {.masc, .fem}
  singular := forms "diēs" "diēs" "diem" "diēī" "diēī" "diē"
  plural := forms "diēs" "diēs" "diēs" "diērum" "diēbus" "diēbus"

/-- The nouns of Blake's table. -/
def nouns : List Noun := [domina, dominus, bellum, consul, civis, manus, dies]

/-! ### The cases the paradigms distinguish -/

/-- The paradigms of the table, singular and plural, separate the six cases: any two cases differ
in some form of some noun, which is how the traditional description establishes them
([blake-2001] §2.2.1). -/
theorem separatesPoints_paradigms :
    {p | ∃ n ∈ nouns, p = n.singular ∨ p = n.plural}.SeparatesPoints := by
  intro c d h
  have : ∀ c d : Case, c ≠ d →
      ∃ n ∈ nouns, n.singular c ≠ n.singular d ∨ n.plural c ≠ n.plural d := by
    decide
  obtain ⟨n, hn, h | h⟩ := this c d h
  exacts [⟨_, ⟨n, hn, .inl rfl⟩, h⟩, ⟨_, ⟨n, hn, .inr rfl⟩, h⟩]

/-- No one paradigm of the table distinguishes all six cases. -/
theorem not_injective :
    ∀ n ∈ nouns, ¬ Function.Injective n.singular ∧ ¬ Function.Injective n.plural := by
  decide

/-! ### Syncretism -/

/-- A neuter does not distinguish nominative and accusative in either number. -/
theorem nom_acc_syncretic_of_neuter :
    ∀ n ∈ nouns, n.IsNeuter →
      n.singular .nom = n.singular .acc ∧ n.plural .nom = n.plural .acc := by
  decide

/-- No plural distinguishes dative and ablative. -/
theorem plural_dat_abl_syncretic : ∀ n ∈ nouns, n.plural .dat = n.plural .abl := by
  decide

/-- The singular fails to distinguish dative and ablative in the second declension and the
i-stems, and nowhere else. -/
theorem singular_dat_abl_syncretic_iff :
    ∀ n ∈ nouns,
      n.singular .dat = n.singular .abl ↔ n.cls = .second ∨ n.cls = .thirdI := by
  decide

/-- The vocative singular differs from the nominative in the non-neuters of the second
declension, and nowhere else. -/
theorem singular_nom_voc_syncretic_iff :
    ∀ n ∈ nouns,
      n.singular .nom = n.singular .voc ↔ ¬ (n.cls = .second ∧ ¬ n.IsNeuter) := by
  decide

theorem plural_nom_voc_syncretic : ∀ n ∈ nouns, n.plural .nom = n.plural .voc := by
  decide

theorem plural_nom_acc_syncretic :
    (∀ n ∈ nouns, n.cls = .thirdConsonant ∨ n.cls = .fourth ∨ n.cls = .fifth →
      n.plural .nom = n.plural .acc) ∧
    civis.variant.plural .nom = civis.variant.plural .acc := by
  decide

end Latin.Declension
