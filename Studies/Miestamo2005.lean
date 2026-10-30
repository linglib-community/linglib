module

public import Linglib.Data.WALS.Features.F113A
public import Linglib.Data.Examples.Miestamo2005
public import Linglib.Data.Examples.Cole1982
public import Linglib.Fragments.Finnish.Negation
public import Linglib.Fragments.Japanese.Negation
public import Linglib.Fragments.Turkish.Negation
public import Linglib.Fragments.Burmese.Negation
public import Linglib.Fragments.Mandarin.Negation
public import Linglib.Fragments.English.Negation
public import Linglib.Fragments.Maori.Negation
public import Linglib.Fragments.Hixkaryana.Negation
public import Linglib.Fragments.German.Negation
public import Linglib.Fragments.Romance.Italian.Negation
public import Linglib.Fragments.Romance.French.Negation
public import Linglib.Fragments.Slavic.Russian.Negation
public import Linglib.Fragments.Romance.Spanish.Negation
public import Linglib.Fragments.Quechua.Negation
public import Linglib.Fragments.Tunica.Negation
public import Linglib.Data.Examples.Readers

/-!
# Miestamo (2005): Standard Negation

This file formalizes Miestamo's typology of standard negation. The negation of a declarative
verbal main clause is symmetric when the negative differs from an affirmative only by the presence
of the negative marker and asymmetric when further structural differences accompany it. A pair is
symmetric when its negative is its affirmative with the marker inserted (`IsSymmetric`), and a
construction is symmetric in its paradigm when its negative is some affirmative of the paradigm
with the marker inserted (`IsSymmetricIn`), as the English negative of a simple tense is
symmetric with the emphatic affirmative. Paradigms are asymmetric by the asymmetries found in
them, symmetric paradigms being identified only by their absence (`ParadigmAsymmetric`): a
paradigm neutralizes when distinct affirmatives share their negative (`Neutralizes`) and displaces
when the negative of one member is built on the affirmative of another while the negatives stay
distinct (`Displaces`). Paradigmatic asymmetry is therefore not neutralization: Tunica builds the
negative of the habitual on the semelfactive and keeps the two apart by their markers
(`exists_paradigmAsymmetric_not_neutralizes`). A language is of type Sym when neither its
constructions nor its paradigms show asymmetry, of type Asy when every construction is
asymmetric, and of type SymAsy otherwise (`languageType`), so the definitional cells of the
book's fourth table follow (`languageType_eq_symmetric_iff`, `languageType_eq_asymmetric_iff`).

The types are instantiated on the book's examples, the rows of `Data.Examples.Miestamo2005`, each
language's pairs being its negative rows with the affirmatives they cite and its fragment's standard
negator as the marker, the German and Italian paradigms by their first person singular. Spanish,
German, Italian, French and Russian are of type Sym. The Finnish negative auxiliary takes the ending
of the finite verb and leaves the lexical verb without it; the plain Japanese negative inflects as
an adjective, a less finite form than the verb; Maori negates with an initial negative verb, and
Hixkaryana deverbalizes the lexical verb under an added copula: finiteness asymmetries, and type
Asy. Mandarin and Turkish mix symmetric and asymmetric constructions. Burmese replaces its three
postverbal tense–aspect markers with one negative suffix, asymmetric in construction and
neutralizing in paradigm. The English negative is symmetric with the emphatic affirmative, not with
the plain one, to which it adds *do*, and the paradigm loses the emphatic distinction of the simple
tenses. The Imbabura Quechua negative is the polar interrogative with *mana* added, and has the
interrogative's validator *-chu* where the declarative has *-mi*, on Cole's examples.

## Implementation notes

A row's morphs are the forms of its text split at word and morph boundaries, and a pair compares
forms; each language's theorem states that its rows are formed into pairs (`Formed`), so that no
pair a row cites is lost. Forms that Miestamo sets aside as phonological are cited in one shape
(`cite`): the Turkish negative *-mE-* as *-mA-* and the glide of the future *-yecek*, the Tunica
vowel loss of *lɔ'ta-w-ɛhɛ* and its negative as *-aha*, the Hixkaryana *-hra* as *-hɨra*, and the
French elided *n'*. The Mandarin constructions are compared through what each negator adds and
excludes, the book giving no minimal pairs for them. The subtypes of asymmetry are not represented:
`Adds` identifies an added element, the mark of the finite-element constructions, but which category
a lost or changed marker belongs to is not recorded in a pair. Different-system asymmetry and
paradigmatic gaps are not represented either, and nor are the representative sample and its
frequency tables.

## TODO

The Quechua asymmetry is paradigmatic displacement onto the interrogative, A/NonReal/Displc; its
statement as `Displaces` needs an affirmative interrogative and a negative interrogative of one
predicate and person, which the examples entered here do not give; Cole's grammar may supply them.

## References

* [miestamo-2005]
* [cole-1982]
-/

@[expose] public section

namespace Miestamo2005

open Negation

variable {α : Type*}

/-! ### Pairs from the rows -/

/-- A morph form, as its characters. -/
abbrev Form := List Char

/-- The form of a string. -/
def toForm (s : String) : Form := s.toList

/-- An affirmative and the negative a marker forms from it, as the forms of their morphs in
surface order. -/
structure Pair where
  /-- The marker of the negative. -/
  marker : Marker
  /-- The affirmative. -/
  affirmative : List Form
  /-- The negative. -/
  negative : List Form
  deriving DecidableEq

/-- The forms of a marker's morphs. -/
def Pair.markerForms (p : Pair) : List Form := p.marker.morphs.map (toForm ·.form)

/-- The forms set aside as phonological, by language, with the shape they are cited in. -/
def citations : List (Glottocode × String × String) :=
  [("nucl1301", "me", "mA"), ("nucl1301", "yecek", "ecek"), ("tuni1252", "w", "wi"),
    ("tuni1252", "ɛhɛ", "aha"), ("hixk1239", "hra", "hɨra"), ("stan1290", "n'", "ne")]

/-- The citation form of a morph in a language. -/
def cite (l : Glottocode) (f : Form) : Form :=
  match citations.find? fun c ↦ c.1 = l ∧ toForm c.2.1 = f with
  | some c => toForm c.2.2
  | none => f

/-- The cited forms of the morphs of a row's text. -/
def forms (e : Datum) : List Form :=
  (Morphology.Morph.wordsOf e.primaryText).flatten.map (cite e.language)

/-- The standard negators of a language, from its fragment. -/
def standard : Glottocode → List Marker
  | "stan1288" => Spanish.Negation.standard
  | "stan1295" => German.Negation.standard
  | "ital1282" => Italian.Negation.standard
  | "stan1290" => French.Negation.standard
  | "russ1263" => Russian.Negation.standard
  | "finn1318" => Finnish.Negation.standard
  | "nucl1643" => Japanese.Negation.standard
  | "maor1246" => Maori.Negation.standard
  | "hixk1239" => Hixkaryana.Negation.standard
  | "nucl1301" => Turkish.Negation.standard
  | "nucl1310" => Burmese.Negation.standard
  | "stan1293" => English.Negation.standard
  | "tuni1252" => Tunica.Negation.standard
  | _ => []

/-- The rows of a language. -/
def rows (l : Glottocode) : List Datum := Examples.all.filter (·.language = l)

/-- The pairs a negative row forms with the affirmatives among `rs` it cites, the marker being the
standard negator whose morphs the negative contains. -/
def pairsOf (rs : List Datum) (n : Datum) : List Pair :=
  let fn := forms n
  (n.features "affirmative").filterMap fun a ↦ do
    let e ← rs.find? (·.id = a)
    let m ← (standard n.language).find? fun m ↦ m.morphs.all (toForm ·.form ∈ fn)
    pure ⟨m, forms e, fn⟩

/-- The pairs of a language. -/
def pairs (l : Glottocode) : List Pair := (rows l).flatMap (pairsOf (rows l))

/-- A language's rows are formed into pairs when it has rows and each negative forms a pair with
every affirmative it cites. -/
def Formed (l : Glottocode) : Prop :=
  rows l ≠ [] ∧ ∀ n ∈ rows l, (pairsOf (rows l) n).length = (n.features "affirmative").length

instance (l : Glottocode) : Decidable (Formed l) := inferInstanceAs (Decidable (_ ∧ _))

/-! ### Constructions -/

/-- A construction is symmetric when the negative is the affirmative with the negative marker
inserted: the affirmative is a sublist of the negative, and the two differ by exactly the
marker's morphs. -/
def IsSymmetric (p : Pair) : Prop :=
  p.affirmative.Sublist p.negative ∧ p.negative.Perm (p.affirmative ++ p.markerForms)

instance : DecidablePred IsSymmetric := fun p ↦
  inferInstanceAs (Decidable (p.affirmative.Sublist p.negative ∧
    p.negative.Perm (p.affirmative ++ p.markerForms)))

/-- A construction is symmetric in a paradigm when its negative is some affirmative of the
paradigm with its marker inserted. -/
def IsSymmetricIn (ps : List Pair) (p : Pair) : Prop :=
  ∃ q ∈ ps, IsSymmetric { p with affirmative := q.affirmative }

instance (ps : List Pair) : DecidablePred (IsSymmetricIn ps) := fun p ↦
  inferInstanceAs (Decidable (∃ q ∈ ps, IsSymmetric { p with affirmative := q.affirmative }))

theorem IsSymmetric.isSymmetricIn {ps : List Pair} {p : Pair} (hp : p ∈ ps)
    (h : IsSymmetric p) : IsSymmetricIn ps p :=
  ⟨p, hp, h⟩

/-- The negative contains an element, other than the marker, that the affirmative lacks, as the
constructions that add a finite element do. -/
def Adds (p : Pair) : Prop :=
  ∃ x ∈ p.negative, x ∉ p.markerForms ∧ x ∉ p.affirmative

instance : DecidablePred Adds := fun p ↦
  inferInstanceAs (Decidable (∃ x ∈ p.negative, x ∉ p.markerForms ∧ x ∉ p.affirmative))

theorem not_isSymmetric_of_adds {p : Pair} (h : Adds p) : ¬ IsSymmetric p := by
  obtain ⟨x, hx, hm, ha⟩ := h
  exact fun hs ↦ by simpa [ha, hm] using hs.2.subset hx

/-! ### Paradigms -/

/-- A paradigm neutralizes when distinct affirmatives share their negative. -/
def Neutralizes (ps : List Pair) : Prop :=
  ∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative = q.negative

/-- A paradigm displaces when the negative of one member is the affirmative of another with the
first member's marker inserted, while the two negatives stay distinct. -/
def Displaces (ps : List Pair) : Prop :=
  ∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative ≠ q.negative ∧
    IsSymmetric { p with affirmative := q.affirmative }

/-- A paradigm is asymmetric when it neutralizes or displaces: symmetric paradigms are those in
which no asymmetry is found. -/
def ParadigmAsymmetric (ps : List Pair) : Prop := Neutralizes ps ∨ Displaces ps

instance (ps : List Pair) : Decidable (Neutralizes ps) :=
  inferInstanceAs (Decidable
    (∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative = q.negative))

instance (ps : List Pair) : Decidable (Displaces ps) :=
  inferInstanceAs (Decidable (∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧
    p.negative ≠ q.negative ∧ IsSymmetric { p with affirmative := q.affirmative }))

instance (ps : List Pair) : Decidable (ParadigmAsymmetric ps) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ### Language types -/

/-- The three types of language, from the symmetry of each construction and whether some
paradigm is asymmetric: symmetric negation when no asymmetry is found, asymmetric when every
construction is asymmetric, and both otherwise. -/
def languageType (cs : List α) (sym : α → Prop) [DecidablePred sym] (paradigmAsymmetric : Prop)
    [Decidable paradigmAsymmetric] : Data.WALS.F113A.NegationSymmetry :=
  if (∀ c ∈ cs, sym c) ∧ ¬ paradigmAsymmetric then .symmetric
  else if ∀ c ∈ cs, ¬ sym c then .asymmetric
  else .both

/-- The type of a language whose constructions form the paradigm `ps`. -/
abbrev pairsType (ps : List Pair) : Data.WALS.F113A.NegationSymmetry :=
  languageType ps (IsSymmetricIn ps) (ParadigmAsymmetric ps)

section LanguageType

variable (cs : List α) (sym : α → Prop) [DecidablePred sym] (P : Prop) [Decidable P]

theorem languageType_eq_symmetric_iff :
    languageType cs sym P = .symmetric ↔ (∀ c ∈ cs, sym c) ∧ ¬ P := by
  unfold languageType
  split_ifs <;> simp_all

theorem languageType_eq_asymmetric_iff (hne : cs ≠ []) :
    languageType cs sym P = .asymmetric ↔ ∀ c ∈ cs, ¬ sym c := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold languageType
  split_ifs with h₁ h₂
  · exact iff_of_false (by simp) fun h ↦ h c List.mem_cons_self (h₁.1 c List.mem_cons_self)
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by simp) h₂

theorem languageType_eq_both_iff :
    languageType cs sym P = .both ↔ (∃ c ∈ cs, sym c) ∧ ((∃ c ∈ cs, ¬ sym c) ∨ P) := by
  unfold languageType
  split_ifs with h₁ h₂
  · exact iff_of_false (by simp) fun ⟨_, h⟩ ↦
      h.elim (fun ⟨c, hc, hn⟩ ↦ hn (h₁.1 c hc)) h₁.2
  · exact iff_of_false (by simp) fun ⟨⟨c, hc, hs⟩, _⟩ ↦ h₂ c hc hs
  · refine iff_of_true rfl ⟨by simpa using h₂, ?_⟩
    by_contra h
    push Not at h
    exact h₁ ⟨h.1, h.2⟩

end LanguageType

/-! ### Paradigmatic displacement: Tunica -/

-- (5)
theorem tunica_displaces :
    Formed "tuni1252" ∧ (∀ p ∈ pairs "tuni1252", IsSymmetricIn (pairs "tuni1252") p) ∧
      Displaces (pairs "tuni1252") ∧ ¬ Neutralizes (pairs "tuni1252") := by
  decide +kernel

theorem exists_paradigmAsymmetric_not_neutralizes :
    ∃ ps, ParadigmAsymmetric ps ∧ ¬ Neutralizes ps :=
  ⟨_, .inr tunica_displaces.2.2.1, tunica_displaces.2.2.2⟩

/-! ### Symmetric negation: Spanish, German, Italian, French, Russian -/

theorem spanish_symmetric : Formed "stan1288" ∧ pairsType (pairs "stan1288") = .symmetric := by
  decide +kernel

theorem german_symmetric : Formed "stan1295" ∧ pairsType (pairs "stan1295") = .symmetric := by
  decide +kernel

theorem italian_symmetric : Formed "ital1282" ∧ pairsType (pairs "ital1282") = .symmetric := by
  decide +kernel

theorem french_symmetric : Formed "stan1290" ∧ pairsType (pairs "stan1290") = .symmetric := by
  decide +kernel

theorem russian_symmetric : Formed "russ1263" ∧ pairsType (pairs "russ1263") = .symmetric := by
  decide +kernel

/-! ### Finiteness asymmetry: Finnish, Japanese, Maori, Hixkaryana -/

theorem finnish_negVerb :
    Finnish.Negation.ending.cells = Agreement.Bundle.personNumberCells ∧ Formed "finn1318" ∧
    (∀ p ∈ pairs "finn1318", p.negative = p.markerForms ++ p.affirmative.reverse) ∧
    pairsType (pairs "finn1318") = .asymmetric := by
  decide +kernel

theorem japanese_negative_adjectival :
    Formed "nucl1643" ∧ ∀ p ∈ pairs "nucl1643", p.marker = Japanese.Negation.na →
      ∃ e ∈ Japanese.Negation.adjectivalEndings.map (toForm ·.form),
        p.negative = p.affirmative.take 1 ++ p.markerForms ++ [e] ∧
          ∀ m ∈ p.affirmative.drop 1,
            m ∉ Japanese.Negation.adjectivalEndings.map (toForm ·.form) := by
  decide +kernel

theorem japanese_asymmetric :
    (∃ p ∈ pairs "nucl1643", p.marker = Japanese.Negation.en ∧ Adds p) ∧
    ¬ ParadigmAsymmetric (pairs "nucl1643") ∧ pairsType (pairs "nucl1643") = .asymmetric := by
  decide +kernel

theorem maori_asymmetric : Formed "maor1246" ∧ pairsType (pairs "maor1246") = .asymmetric := by
  decide +kernel

theorem hixkaryana_asymmetric :
    Formed "hixk1239" ∧ (∀ p ∈ pairs "hixk1239", Adds p) ∧
      pairsType (pairs "hixk1239") = .asymmetric := by
  decide +kernel

/-! ### Mixed languages: Mandarin and Turkish -/

/-- A Mandarin negator's construction is symmetric when it adds nothing but the negator, so that
no verb comes with it and no aspect particle of the affirmative is excluded. -/
def IsSymmetricNegator (n : Mandarin.Negation.Negator) : Prop := n.verb = none ∧ n.excludes = []

instance : DecidablePred IsSymmetricNegator := fun n ↦
  inferInstanceAs (Decidable (n.verb = none ∧ n.excludes = []))

theorem mandarin_both :
    IsSymmetricNegator Mandarin.Negation.bu ∧ ¬ IsSymmetricNegator Mandarin.Negation.mei ∧
      languageType Mandarin.Negation.negators IsSymmetricNegator False = .both := by
  decide +kernel

theorem turkish_both :
    Formed "nucl1301" ∧ (∀ p ∈ pairs "nucl1301", IsSymmetric p ↔ toForm "ir" ∉ p.affirmative) ∧
    ¬ ParadigmAsymmetric (pairs "nucl1301") ∧ pairsType (pairs "nucl1301") = .both := by
  decide +kernel

/-! ### Paradigmatic neutralization: Burmese and English -/

theorem burmese_neutralizes :
    Formed "nucl1310" ∧ Neutralizes (pairs "nucl1310") ∧
      pairsType (pairs "nucl1310") = .asymmetric := by
  decide +kernel

theorem english_both :
    Formed "stan1293" ∧ (∀ p ∈ pairs "stan1293", ¬ IsSymmetric p → Adds p) ∧
    Neutralizes (pairs "stan1293") ∧
    pairsType (pairs "stan1293") = .both := by
  have h : Formed "stan1293" ∧ (∀ p ∈ pairs "stan1293", ¬ IsSymmetric p → Adds p) ∧
      Neutralizes (pairs "stan1293") ∧
      ∃ c ∈ pairs "stan1293", IsSymmetricIn (pairs "stan1293") c := by
    decide +kernel
  exact ⟨h.1, h.2.1, h.2.2.1, (languageType_eq_both_iff ..).2 ⟨h.2.2.2, .inr (.inl h.2.2.1)⟩⟩

/-! ### Non-realized marking: Imbabura Quechua -/

-- (63c, d), (332), (333), (89b), (90)
theorem quechua_negative_of_interrogative :
    IsSymmetric ⟨Quechua.Negation.mana, (forms Cole1982.Examples.ex_333).drop 2,
      (forms Cole1982.Examples.ex_332).drop 1⟩ ∧
    IsSymmetric ⟨Quechua.Negation.mana, ((forms Cole1982.Examples.ex_89b).drop 1).map
      (fun m ↦ if m = toForm "mi" then toForm Quechua.Negation.chu.form else m),
      forms Cole1982.Examples.ex_90⟩ ∧
    toForm "mi" ∈ forms Cole1982.Examples.ex_89b ∧ toForm "mi" ∉ forms Cole1982.Examples.ex_90 := by
  decide +kernel

end Miestamo2005
