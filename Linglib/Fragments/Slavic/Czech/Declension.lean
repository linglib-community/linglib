module

public import Linglib.Fragments.Slavic.Czech.Case
public import Linglib.Fragments.Slavic.Czech.Gender
public import Linglib.Fragments.Slavic.Czech.Phonology
public import Linglib.Syntax.Number.Basic
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Prod

/-!
# Czech declension

This file defines the declension classes of Czech nouns after Short's grammar, with the
conditions on velar stems that the Academy grammar *Mluvnice češtiny* states as rules.

A Czech noun inflects for seven cases and two numbers (p. 465). Short's Tables 9.2 to 9.7
(pp. 465–470) decline one model noun for each declension: *chlap* 'fellow' and *hrad* 'castle'
for the hard masculines, "one class, subdivided according to animacy" (p. 465), *muž* 'man' and
*stroj* 'machine' for the soft masculines, *město* 'town', *srdce* 'heart' and *učení* 'study'
for the neuter o-stems, *žena* 'woman', *hrdina* 'hero', *duše* 'soul' and *paní* 'lady' for the
a-stems, *kost* 'bone' for the i-stems and *jehně* 'lamb' for the neuter t-stems. A class here is
the declension of one model noun, and its endings are the table's, every alternant the table
prints in the order it prints them. Short states two conditions on stems besides: a velar
stem of the hard masculines takes the vocative singular *-u* (pp. 465–466), and the second
palatalization of velars replaces *k*, *h*, *g* and *ch* by *c*, *z*, *z* and *š* (p. 462).

*Mluvnice češtiny* states the vocative condition as a rule (pp. 292, 305), and a second one on
velar stems that Short gives by example alone (Short, pp. 462, 467): a velar stem of the hard
masculines and of the masculine a-stems takes the locative plural *-ích*, where the others take
*-ech* (pp. 292, 295, 300, 305). It makes the alternation of the velar obligatory before *-ích*
in the locative plural of the masculines and before *-i* in the nominative plural of the
masculine animates (p. 279), and a stem is inflected with the second palatalization there.

## Main definitions

* `Czech.Declension.Cell`: a case of the seven and a number
* `Czech.Declension.Class`: the declensions of Short's tables, by model noun
* `Czech.Declension.Class.gender`: the gender each table is for
* `Czech.Declension.Class.endings`: the endings of a class at each cell
* `Czech.Declension.finalPhoneme`: the final phoneme of a stem
* `Czech.Declension.IsVelar`, `Czech.Declension.Class.endingsOn`: the velar vocative singular
  and locative plural
* `Czech.Declension.palatalize`: the second palatalization of velars on a stem
* `Czech.Declension.Class.Palatalizes`, `Czech.Declension.Class.inflect`,
  `Czech.Declension.Class.formsOn`: where a stem palatalizes, and the forms of a class on a stem

## Main results

* `voc_eq_nom_plural`: the vocative plural is the nominative plural in every class
* `animacy_plural`: the masculine animates and inanimates differ in the plural only in the
  nominative and the vocative
* `acc_eq_gen_singular_iff`: the animate accusative singular is the genitive, except in the
  masculine a-stems
* `dat_loc_singular_iff`: the dative and locative singular fall together in every class but the
  hard masculine inanimates and the neuter o-stems
* `dat_singular_u_ovi`: the masculine dative singular *-u* is that of the hard masculines, and
  *-ovi* alone that of the masculine a-stems
* `isVelar_singleton_iff`: the velar letters are *k*, *g*, *h* and *ch*, and they palatalize to
  *c*, *z*, *z* and *š*
* `endingsOn_voc_velar`, `formsOn_locPl_velar`, `palatalize_examples`: the grammars' examples
  of the stem conditions

## Implementation notes

An ending is a list of orthographic segments, *ch* being one letter of the Czech alphabet
(p. 459), as the forms data segment words, and the null ending is the empty list. The
orthography spells a palatal *ď*, *ť* or *ň* on the following *ě* or *i* and on the consonant
before *a*, *o*, *u* or finally (p. 459), so the stem of *jehně* is written *jehn-* before the
*ě* of the singular endings and *jehň-* before the *a* of the plural ones. The endings are those
of the tables, save on a velar stem, where the vocative singular *-u* and the locative plural
*-ích* of *Mluvnice češtiny*'s rules replace the table's *-e* and *-ech*. The variation Short
describes in prose without a table alternant is left out: the locative singular *-ě* or *-u* of
the hard inanimates (p. 466) and the neuters (p. 467), the genitive singular *-a* or *-u* of the
inanimates (p. 466), the nominative plurals in *-é* and *-ové* of "subclasses not recorded in the
tables" (p. 466), and the locative plural *-ách* of suffixed velar neuters (pp. 466–467). So are
the locative plural *-ách* after a velar that *Mluvnice češtiny* allows in everyday speech
(pp. 292, 295, 300), the *-ích* it gives the masculine a-stems in a soft consonant, as *rikších*
(p. 292), since it lists no soft consonants, and its vocative *-e* of *člověče* and *bože* (p. 294).
`palatalize` is the second palatalization of velars alone, and a stem is palatalized only before
the plural *-i* and *-ích*: not where the alternation is of *r*, as *bratr–bratři* (*Mluvnice
češtiny*, p. 294), nor before the singular *-ě*, whose spelling it changes too, as the
dative-locative singular *ruce* of *ruka* (Short, p. 462). The palatal dentals are written as the
plain ones before *i* (Short, p. 459). The types Short describes without a table, the animates in
*-ce* (p. 466) and the *píseň* type (p. 468), have no class.

The stem conditions are stated over the phonemes that the stem's letters write
(`Czech.Phonology.ofChars`): a stem is velar when its final phoneme is one of
`Czech.Phonology.palatalizing`, and `palatalize` replaces that phoneme by its reflex under
`Czech.Phonology.secondPalatalization` and writes the reflex with its letter. The endings stay
lists of letters. The alternation of *d*, *t* and *n* with *ď*, *ť* and *ň* before a front vowel
and the /j/ after a labial before *ě* (Short, pp. 459, 462) are not rules here: the spelling
writes them on the *ě* or *i* of the ending, so a form's phonemes are read from its letters and
not composed from the stem's and the ending's. Stating these alternations as rules is the step
that would make the endings lists of phonemes.

## References

* [short-1993-czech]
* [komarek-etal-1986]
-/

@[expose] public section

namespace Czech.Declension

/-! ### Cells and segments -/

/-- The segments of a list of letters, *c* followed by *h* being the one segment *ch*. -/
def segmentsAux : List Char → List String
  | 'c' :: 'h' :: rest => "ch" :: segmentsAux rest
  | x :: rest => x.toString :: segmentsAux rest
  | [] => []

/-- The segments of a written form are its letters, *ch* being one letter of the alphabet
(p. 459). -/
def segments (w : String) : List String := segmentsAux w.toList

/-- The numbers are the singular and the plural (p. 465). -/
abbrev numbers : Finset Number := {.singular, .plural}

/-- A cell pairs one of the seven cases with a number. -/
abbrev Cell : Type := Case × numbers

/-- `Cell.of c n` is the cell of the case `c` and the number `n`. -/
def Cell.of (c : Case) (n : Number) (hn : n ∈ numbers := by decide) : Cell :=
  (c, ⟨n, hn⟩)

instance : Nonempty Cell := ⟨.of .nom .singular⟩

/-- The case of a cell. -/
def Cell.case (σ : Cell) : Case := σ.1

/-- The number of a cell. -/
def Cell.number (σ : Cell) : Number := σ.2.1

/-! ### The declensions of Short's tables -/

/-- The declensions of Short's tables, each named for its model noun. The hard masculines are
"one class, subdivided according to animacy" (p. 465), and in the soft masculines "the areas
where animates differ from inanimates replicate those under the hard declension" (p. 466); each
has a model noun for each animacy. -/
inductive Class where
  /-- The hard masculine animates, as *chlap* 'fellow' (Table 9.2, p. 465). -/
  | chlap
  /-- The hard masculine inanimates, as *hrad* 'castle' (Table 9.2, p. 465). -/
  | hrad
  /-- The soft masculine animates, as *muž* 'man' (Table 9.3, p. 466). -/
  | muz
  /-- The soft masculine inanimates, as *stroj* 'machine' (Table 9.3, p. 466). -/
  | stroj
  /-- The neuter o-stems, as *město* 'town' (Table 9.4, p. 467). -/
  | mesto
  /-- The neuter jo-stems, as *srdce* 'heart' (Table 9.4, p. 467). -/
  | srdce
  /-- The neuter ьjo-stems, as *učení* 'study' (Table 9.4, p. 467). -/
  | uceni
  /-- The hard feminine a-stems, as *žena* 'woman' (Table 9.5, p. 468). -/
  | zena
  /-- The hard masculine a-stems, as *hrdina* 'hero' (Table 9.5, p. 468), "the masculine
  a-declension" (p. 467). -/
  | hrdina
  /-- The soft feminine ja-stems, as *duše* 'soul' (Table 9.5, p. 468). -/
  | duse
  /-- The ьja-stem, "one word only", *paní* 'lady' (Table 9.5, p. 468). -/
  | pani
  /-- The i-stems, as *kost* 'bone' (Table 9.6, p. 469). -/
  | kost
  /-- The neuter t-stems, as *jehně* 'lamb' (Table 9.7, p. 470). -/
  | jehne
  deriving DecidableEq, Repr, Fintype

/-- The gender of a class is the gender its table is for, the masculine animate for *chlap*,
*muž* and *hrdina*, the masculine inanimate for *hrad* and *stroj*, the feminine for *žena*,
*duše*, *paní* and the i-stems, "mostly of feminine abstract nouns in -ost" (p. 468),
and the neuter for the neuter o-stems and t-stems. -/
def Class.gender : Class → Gender.Value
  | .chlap | .muz | .hrdina => .mascAnimate
  | .hrad | .stroj => .mascInanimate
  | .zena | .duse | .pani | .kost => .feminine
  | .mesto | .srdce | .uceni | .jehne => .neuter

/-- `row nom voc acc gen dat inst loc` gives each of the seven cases the endings named for it,
in the order of Short's tables. -/
def row (nom voc acc gen dat inst loc : List (List String)) : Case → List (List String)
  | .nom => nom
  | .voc => voc
  | .acc => acc
  | .gen => gen
  | .dat => dat
  | .inst => inst
  | .loc => loc

/-- The endings of a class in the singular, as Short's tables print them after the stem, the
alternants in the table's order. -/
def Class.singularEndings : Class → Case → List (List String)
  | .chlap =>
    row [[]] [["e"]] [["a"]] [["a"]] [["o", "v", "i"], ["u"]] [["e", "m"]] [["o", "v", "i"], ["u"]]
  | .hrad => row [[]] [["e"]] [[]] [["u"]] [["u"]] [["e", "m"]] [["ě"]]
  | .muz => row [[]] [["i"]] [["e"]] [["e"]] [["i"], ["o", "v", "i"]] [["e", "m"]]
    [["i"], ["o", "v", "i"]]
  | .stroj => row [[]] [["i"]] [[]] [["e"]] [["i"]] [["e", "m"]] [["i"]]
  | .mesto => row [["o"]] [["o"]] [["o"]] [["a"]] [["u"]] [["e", "m"]] [["ě"]]
  | .srdce => row [["e"]] [["e"]] [["e"]] [["e"]] [["i"]] [["e", "m"]] [["i"]]
  | .uceni => row [["í"]] [["í"]] [["í"]] [["í"]] [["í"]] [["í", "m"]] [["í"]]
  | .zena => row [["a"]] [["o"]] [["u"]] [["y"]] [["ě"]] [["o", "u"]] [["ě"]]
  | .hrdina => row [["a"]] [["o"]] [["u"]] [["y"]] [["o", "v", "i"]] [["o", "u"]] [["o", "v", "i"]]
  | .duse => row [["e"]] [["e"]] [["i"]] [["e"]] [["i"]] [["í"]] [["i"]]
  | .pani => row [[]] [[]] [[]] [[]] [[]] [[]] [[]]
  | .kost => row [[]] [["i"]] [[]] [["i"]] [["i"]] [["í"]] [["i"]]
  | .jehne => row [["ě"]] [["ě"]] [["ě"]] [["ě", "t", "e"]] [["ě", "t", "i"]] [["ě", "t", "e", "m"]]
    [["ě", "t", "i"]]

/-- The endings of a class in the plural, as Short's tables print them after the stem. -/
def Class.pluralEndings : Class → Case → List (List String)
  | .chlap => row [["i"]] [["i"]] [["y"]] [["ů"]] [["ů", "m"]] [["y"]] [["e", "ch"]]
  | .hrad => row [["y"]] [["y"]] [["y"]] [["ů"]] [["ů", "m"]] [["y"]] [["e", "ch"]]
  | .muz => row [["i"]] [["i"]] [["e"]] [["ů"]] [["ů", "m"]] [["i"]] [["í", "ch"]]
  | .stroj => row [["e"]] [["e"]] [["e"]] [["ů"]] [["ů", "m"]] [["i"]] [["í", "ch"]]
  | .mesto => row [["a"]] [["a"]] [["a"]] [[]] [["ů", "m"]] [["y"]] [["e", "ch"]]
  | .srdce => row [["e"]] [["e"]] [["e"]] [["í"]] [["í", "m"]] [["i"]] [["í", "ch"]]
  | .uceni => row [["í"]] [["í"]] [["í"]] [["í"]] [["í", "m"]] [["í", "m", "i"]] [["í", "ch"]]
  | .zena => row [["y"]] [["y"]] [["y"]] [[]] [["á", "m"]] [["a", "m", "i"]] [["á", "ch"]]
  | .hrdina =>
    row [["o", "v", "é"]] [["o", "v", "é"]] [["y"]] [["ů"]] [["ů", "m"]] [["y"]] [["e", "ch"]]
  | .duse => row [["e"]] [["e"]] [["e"]] [["í"]] [["í", "m"]] [["e", "m", "i"]] [["í", "ch"]]
  | .pani => row [[]] [[]] [[]] [[]] [["m"]] [["m", "i"]] [["ch"]]
  | .kost => row [["i"]] [["i"]] [["i"]] [["í"]] [["e", "m"]] [["m", "i"]] [["e", "ch"]]
  | .jehne => row [["a", "t", "a"]] [["a", "t", "a"]] [["a", "t", "a"]] [["a", "t"]]
    [["a", "t", "ů", "m"]] [["a", "t", "y"]] [["a", "t", "e", "ch"]]

/-- The endings of a class at a cell, as Short's tables print them. -/
def Class.endings (k : Class) (σ : Cell) : List (List String) :=
  if σ.number = .singular then k.singularEndings σ.1 else k.pluralEndings σ.1

/-- The nominative singular ending of a class, the one its table prints. -/
def Class.nomSg (k : Class) : List String := (k.endings (.of .nom .singular)).headD []

/-! ### Stem conditions -/

/-- The final phoneme of a stem, the last of the phonemes its letters write, if they are all
Czech. -/
def finalPhoneme (s : List String) : Option Phonology.Segment :=
  (Phonology.ofChars (s.flatMap String.toList)).bind List.getLast?

/-- A stem is velar when its final phoneme is one that the second palatalization changes, *k*,
*g*, *ch* or *h*. Short counts /h/ among the laryngeals (p. 457), but it alternates with *z* as
*g* does in the second palatalization (p. 462) and takes the velar vocative, as *vrahu*
'murderer' (p. 465). -/
def IsVelar (s : List String) : Prop := ∃ x ∈ finalPhoneme s, x ∈ Phonology.palatalizing

instance : DecidablePred IsVelar := fun s ↦ inferInstanceAs (Decidable (∃ x ∈ finalPhoneme s, _))

/-- The endings of a class on a stem are those of its table, except on a velar stem.

A velar stem of the hard masculines takes *-u* in the vocative singular: "The u-stem vocative
ending also survives, chiefly as a means to avoid palatalization of velar stems, for example,
*kluku* 'boy', *vrahu* 'murderer'" (p. 465), the forms in *-e* with palatalization, *člověče*
'man' and *bože* 'God', being "used chiefly as interjections" (pp. 465–466). *Mluvnice češtiny*
states it as a rule: the hard masculine animates take *-e* after a non-velar and *-u* after a
velar, *pane*, *dělníku* (p. 292), *-e* after a velar being confined to *člověče*, *bože* and
expressive use (p. 294), and the inanimates *-u* after a velar, *jazyku*, *prachu*, *prahu*
(p. 305).

A velar stem of the hard masculines and of the masculine a-stems takes *-ích* in the locative
plural, which Short gives by example, *geolozích* (p. 462) and *sluzích* (p. 467), and *Mluvnice
češtiny* as the rule: the non-velar stems of these classes take *-ech*, *pánech*, *předsedech*,
and the velar ones *-ích*, *dělnících*, *sluzích* (p. 292), *filolozích* (p. 295), *kolezích*
(p. 300), *rybnících*, *dialozích* (p. 305). -/
def Class.endingsOn (k : Class) (s : List String) (σ : Cell) : List (List String) :=
  if (k = .chlap ∨ k = .hrad) ∧ σ.case = .voc ∧ σ.number = .singular ∧ IsVelar s then [["u"]]
  else if (k = .chlap ∨ k = .hrad ∨ k = .hrdina) ∧ σ.case = .loc ∧ σ.number = .plural ∧
      IsVelar s then [["í", "ch"]]
  else k.endings σ

/-- The second palatalization of velars replaces the final phoneme of a velar stem by its reflex,
as Short states it, "*k* › *c*; *h* › *z*; *ch* › *š* (NB not *s*). Here too the reflex of *g* has
de-affricated from *dz* to *z*" (p. 462), and writes the reflex with its letter. Short's examples
of it in declension are the dative-locative singular of the a-stems, *ruka/ruce* 'hand' (p. 462)
and *matka/matce* 'mother' (p. 467), and the locative plural in *-ích* of velar stems,
*geolog–geolozích* 'geologist' (p. 462) and *sluha/sluzích* 'servant' (p. 467). -/
def palatalize (s : List String) : List String :=
  match finalPhoneme s with
  | some x =>
    if x ∈ Phonology.palatalizing then
      s.dropLast ++ (Phonology.letter (Phonology.secondPalatalization x)).toList
    else s
  | none => s

theorem palatalize_of_not_isVelar {s : List String} (h : ¬ IsVelar s) : palatalize s = s := by
  unfold palatalize
  split <;> simp_all [IsVelar]

theorem isVelar_singleton_iff :
    (∀ l ∈ Phonology.alphabet, IsVelar [l] ↔ l ∈ ["k", "g", "h", "ch"]) ∧
      palatalize ["k"] = ["c"] ∧ palatalize ["g"] = ["z"] ∧ palatalize ["h"] = ["z"] ∧
      palatalize ["ch"] = ["š"] := by
  decide +kernel

/-- A stem of a class palatalizes before an ending at a cell when the class is masculine and the
ending is the locative plural *-ích*, or the class is masculine animate and the ending the
nominative or vocative plural *-i*. *Mluvnice češtiny* makes the alternation obligatory there,
"závazné před -i v Npl mužských jmen životných, -ích v Lpl jmen mužských" 'obligatory before
*-i* in the nominative plural of the masculine animates, *-ích* in the locative plural of the
masculines' (p. 279), and the vocative plural is "s ním identický" 'identical with it'
(p. 292). -/
def Class.Palatalizes (k : Class) (σ : Cell) (e : List String) : Prop :=
  k.gender.toLabel = .masculine ∧ σ.number = .plural ∧
    (σ.case = .loc ∧ e = ["í", "ch"] ∨
      k.gender = .mascAnimate ∧ (σ.case = .nom ∨ σ.case = .voc) ∧ e = ["i"])

instance (k : Class) (σ : Cell) (e : List String) : Decidable (k.Palatalizes σ e) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `k.inflect s σ e` is the stem `s` followed by the ending `e` at the cell `σ` in the class
`k`, the stem undergoing the second palatalization where it palatalizes. -/
def Class.inflect (k : Class) (s : List String) (σ : Cell) (e : List String) : List String :=
  (if k.Palatalizes σ e then palatalize s else s) ++ e

/-- The forms of a class on a stem at a cell are the stem inflected with each of the class's
endings on it. -/
def Class.formsOn (k : Class) (s : List String) (σ : Cell) : List (List String) :=
  (k.endingsOn s σ).map (k.inflect s σ)

/-! ### Generalizations over the tables -/

/-- In every class the vocative plural is the nominative plural, as "no adjectival, pronominal,
numeral or plural noun paradigms have distinct vocative forms (vocative = nominative)"
(p. 465). -/
theorem voc_eq_nom_plural (k : Class) :
    k.endings (.of .voc .plural) = k.endings (.of .nom .plural) := by
  cases k <;> decide

/-- "In the plural, the animacy opposition is expressed only in the existence of a distinctive
nominative plural for animates" (p. 465): the hard and the soft masculine animates and
inanimates share their plural endings in every case but the nominative and, the vocative
plural being the nominative, the vocative. -/
theorem animacy_plural (c : Case) :
    (Class.chlap.pluralEndings c = Class.hrad.pluralEndings c ↔ c ≠ .nom ∧ c ≠ .voc) ∧
      (Class.muz.pluralEndings c = Class.stroj.pluralEndings c ↔ c ≠ .nom ∧ c ≠ .voc) := by
  revert c
  decide

/-- "In the singular, animate accusative equals genitive, which itself, in the core (hard)
masculine paradigm, differs from the inanimate genitive", the exception being "the masculine
singular a-declension, which, like the feminine, has inherited unambiguous forms for
nominative, genitive and accusative" (p. 465). -/
theorem acc_eq_gen_singular_iff :
    (∀ k : Class, k.gender.IsAnimate →
      (k.singularEndings .acc = k.singularEndings .gen ↔
        k ≠ .hrdina)) ∧
      Class.chlap.singularEndings .gen ≠
        Class.hrad.singularEndings .gen := by
  decide

/-- The dative and locative singular fall together in every class but the hard masculine
inanimates and the neuter o-stems, whose dative is *-u* and locative *-ě*, "A noteworthy
development within the case system" being "the spread of dative–locative syncretism in singular
noun classes" (p. 465). -/
theorem dat_loc_singular_iff (k : Class) :
    k.singularEndings .dat = k.singularEndings .loc ↔
      k ≠ .hrad ∧ k ≠ .mesto := by
  cases k <;> decide

/-- Among the masculines, the dative singular *-u* is that of the hard masculines alone, and of
all the classes only the masculine a-stems have *-ovi* alone. *Mluvnice češtiny* states both:
"-u mají pouze jména podtypu I.A s tzv. skloňováním tvrdým" '*-u* is had only by the nouns of
subtype I.A, with the so-called hard declension', *-i* belonging to the soft ones, and "V III.
typu má D a L sg podobu jedinou, nevariantní, a to -ovi" 'in type III the dative and locative
singular have a single, non-variant form, *-ovi*' (p. 292), as the inanimate *hrad* has *-u*
(p. 307) and *stroj* *-i* (p. 309). Short's tables agree: *chlapovi* or *chlapu*, *hradu*,
*muži* or *mužovi*, *stroji* and *hrdinovi* (Tables 9.2, 9.3, 9.5), the neuter *městu* not being
masculine. -/
theorem dat_singular_u_ovi (k : Class) :
    (k.gender.toLabel = .masculine →
      (["u"] ∈ k.singularEndings .dat ↔ k = .chlap ∨ k = .hrad)) ∧
      (k.singularEndings .dat = [["o", "v", "i"]] ↔ k = .hrdina) := by
  cases k <;> decide

/-- A velar stem of the hard masculines takes *-u* in the vocative singular, as *kluku* 'boy'
and *vrahu* 'murderer' (p. 465), and any other stem the table's *-e*, as *chlape* (Table 9.2). -/
theorem endingsOn_voc_velar :
    (Class.chlap.endingsOn (segments "kluk") (.of .voc .singular)).map (segments "kluk" ++ ·) =
        [segments "kluku"] ∧
      (Class.chlap.endingsOn (segments "vrah") (.of .voc .singular)).map (segments "vrah" ++ ·) =
        [segments "vrahu"] ∧
      (Class.chlap.endingsOn (segments "chlap") (.of .voc .singular)).map
        (segments "chlap" ++ ·) = [segments "chlape"] := by
  decide +kernel

/-- A velar stem of the hard masculines and of the masculine a-stems takes the locative plural
*-ích* on the palatalized stem, as *filolozích* (*Mluvnice češtiny*, p. 295), *sluzích*
(Short, p. 467; *Mluvnice češtiny*, pp. 292, 300) and *dialozích* (*Mluvnice češtiny*, p. 305),
and any other stem the table's *-ech*, as *chlapech* (Table 9.2) and *předsedech* (*Mluvnice
češtiny*, p. 292). -/
theorem formsOn_locPl_velar :
    Class.chlap.formsOn (segments "filolog") (.of .loc .plural) = [segments "filolozích"] ∧
      Class.hrdina.formsOn (segments "sluh") (.of .loc .plural) = [segments "sluzích"] ∧
      Class.hrad.formsOn (segments "dialog") (.of .loc .plural) = [segments "dialozích"] ∧
      Class.chlap.formsOn (segments "chlap") (.of .loc .plural) = [segments "chlapech"] ∧
      Class.hrdina.formsOn (segments "předsed") (.of .loc .plural) =
        [segments "předsedech"] := by
  decide +kernel

/-- The second palatalization gives Short's examples *ruce* from *ruka* 'hand', *geolozích* from
*geolog* 'geologist' and the adverb *plaše* from *plachý* 'timid' (p. 462), and *matce* from
*matka* 'mother' and *sluzích* from *sluha* 'servant' (p. 467), and *Mluvnice češtiny*'s
*filolozích* from *filolog* 'philologist' (p. 295). -/
theorem palatalize_examples :
    palatalize (segments "ruk") ++ ["e"] = segments "ruce" ∧
      palatalize (segments "geolog") ++ ["í", "ch"] = segments "geolozích" ∧
      palatalize (segments "plach") ++ ["e"] = segments "plaše" ∧
      palatalize (segments "matk") ++ ["e"] = segments "matce" ∧
      palatalize (segments "sluh") ++ ["í", "ch"] = segments "sluzích" ∧
      palatalize (segments "filolog") ++ ["í", "ch"] = segments "filolozích" := by
  decide +kernel

end Czech.Declension
