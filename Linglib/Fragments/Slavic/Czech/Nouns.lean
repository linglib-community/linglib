module

public import Linglib.Fragments.Slavic.Czech.Declension
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Czech nouns

This file defines the Czech noun as a lexical entry with its controller gender, its declension
class and the nominative plural it takes lexically, and gives the model nouns of Short's
declension tables and *kluk* 'boy', the nouns the grammars name as changing class with number,
and the nouns of Stump's tables of Czech heteroclisis, whose classes follow from Short's grammar
and the Academy grammar *Mluvnice češtiny*.

A noun's class is that of its singular, and its plural follows the same class unless the noun
changes class with number: "Modern masculines like *den* 'day' and *kořen* 'root' generally
follow *stroj* in the singular and *hrady* in the plural" (Short, p. 469), and *Mluvnice
češtiny* gives the masculines with a stem in *-en-*, *kořen* and *pramen* among them, the soft
declension in the singular and the hard one in the plural (p. 310). The stem is the citation
form less the nominative singular ending of its class.

Where a class leaves the nominative plural of the masculine animates open, *Mluvnice češtiny*
assigns it noun by noun: its three endings *-i*, *-ové* and *-é* are taken "buď jen jednu, nebo
dvě" 'either only one or two' by a noun (pp. 292–293). An entry records the endings the grammar
assigns it, and its forms are those of its class with these endings in the nominative and
vocative plural.

## Main definitions

* `Czech.Noun`: a noun with its controller gender, its class in each number and its lexical
  nominative plural
* `Czech.Noun.clsAt`, `Czech.Noun.stem`: the class of a number, and the stem
* `Czech.Noun.endingsIn`, `Czech.Noun.endings`, `Czech.Noun.forms`: a noun's endings in a class,
  its endings and its forms
* `Czech.nouns`: the entries

## Main results

* `Czech.stem_append_nomSg`: every entry's citation form is its stem followed by the nominative
  singular ending of its class
* `Czech.gender_eq_cls_gender`: every entry has the gender of its class's table
* `Czech.isVelar_stem_iff`, `Czech.isSome_ofChars_forms`: the velar stems are those of *kluk*,
  *sluha* and *filolog*, and every form is written in Czech letters
* `Czech.forms_examples`: the forms the grammars give Stump's nouns in the cells where they
  depart from the model nouns' tables

## Implementation notes

The stem is that of the nominative singular. Short's e ~ ∅ alternation between the nominative
singular and the oblique cases, as *den/dne* (p. 463), gives *den* an oblique stem *dn-* that
`Noun.stem` does not record, and the stem of *jehně* is written *jehň-* before the plural endings
(p. 459). The hard forms that *Mluvnice češtiny* says enter the singular of the *-en-* stems
(p. 310) are not recorded, the grammar naming no cell they occupy. A lexical nominative plural is
recorded only where *Mluvnice češtiny* names the noun, Short placing none of the entries among
the subclasses with a nominative plural in *-é* or *-ové* (p. 466).

## References

* [short-1993-czech]
* [komarek-etal-1986]
* [stump-2006]
-/

@[expose] public section

namespace Czech

open Declension

/-- A Czech noun with its controller gender, its declension class in each number, and the
nominative plural it takes lexically. -/
structure Noun extends GenderedNoun Gender.Value where
  /-- The class of the singular. -/
  cls : Class
  /-- The class of the plural, that of the singular unless the noun changes class. -/
  clsPlural : Class := cls
  /-- The nominative and vocative plural endings the grammar assigns the noun lexically, where
  its class leaves a choice, or `none` where the noun takes its class's. -/
  nomPlural : Option (List (List String)) := none
  deriving DecidableEq, Repr

/-- The class a noun follows in a number. -/
def Noun.clsAt (n : Noun) (m : Number) : Class := if m = .plural then n.clsPlural else n.cls

/-- The stem of a noun is its citation form less the nominative singular ending of its class. -/
def Noun.stem (n : Noun) : List String :=
  (segments n.form).take ((segments n.form).length - n.cls.nomSg.length)

/-- The endings of a noun in a class at a cell are those of the class on the noun's stem, save
that the noun's lexical nominative plural replaces the class's in the nominative and the
vocative plural. -/
def Noun.endingsIn (n : Noun) (k : Class) (σ : Cell) : List (List String) :=
  if σ.number = .plural ∧ (σ.case = .nom ∨ σ.case = .voc) then
    n.nomPlural.getD (k.endingsOn n.stem σ)
  else k.endingsOn n.stem σ

/-- The endings of a noun at a cell are its endings in the class it follows in the cell's
number. -/
def Noun.endings (n : Noun) (σ : Cell) : List (List String) := n.endingsIn (n.clsAt σ.number) σ

/-- The forms of a noun at a cell are its stem inflected with each of its endings there. -/
def Noun.forms (n : Noun) (σ : Cell) : List (List String) :=
  (n.endings σ).map ((n.clsAt σ.number).inflect n.stem σ)

/-! ### The model nouns of Short's tables -/

/-- *chlap* 'fellow', the hard masculine animate model (Table 9.2, p. 465). -/
def chlap : Noun :=
  { form := "chlap", gloss := "fellow", gender := .mascAnimate, naturalGender := some .masculine,
    cls := .chlap }

/-- *hrad* 'castle', the hard masculine inanimate model (Table 9.2, p. 465). -/
def hrad : Noun := { form := "hrad", gloss := "castle", gender := .mascInanimate, cls := .hrad }

/-- *muž* 'man', the soft masculine animate model (Table 9.3, p. 466). Short's table gives the
nominative plural *muži* alone, and *Mluvnice češtiny* says that "jméno muž může mít podobu
obojí, -ové i -i" 'the noun *muž* can have both forms, *-ové* and *-i*' (p. 298). -/
def muz : Noun :=
  { form := "muž", gloss := "man", gender := .mascAnimate, naturalGender := some .masculine,
    cls := .muz, nomPlural := some [["i"], ["o", "v", "é"]] }

/-- *stroj* 'machine', the soft masculine inanimate model (Table 9.3, p. 466). -/
def stroj : Noun :=
  { form := "stroj", gloss := "machine", gender := .mascInanimate, cls := .stroj }

/-- *město* 'town', the neuter o-stem model (Table 9.4, p. 467). -/
def mesto : Noun := { form := "město", gloss := "town", gender := .neuter, cls := .mesto }

/-- *srdce* 'heart', the neuter jo-stem model (Table 9.4, p. 467). -/
def srdce : Noun := { form := "srdce", gloss := "heart", gender := .neuter, cls := .srdce }

/-- *učení* 'study', the neuter ьjo-stem model (Table 9.4, p. 467). -/
def uceni : Noun := { form := "učení", gloss := "study", gender := .neuter, cls := .uceni }

/-- *žena* 'woman', the hard feminine a-stem model (Table 9.5, p. 468). -/
def zena : Noun :=
  { form := "žena", gloss := "woman", gender := .feminine, naturalGender := some .feminine,
    cls := .zena }

/-- *hrdina* 'hero', the hard masculine a-stem model (Table 9.5, p. 468). -/
def hrdina : Noun :=
  { form := "hrdina", gloss := "hero", gender := .mascAnimate, cls := .hrdina }

/-- *duše* 'soul', the soft feminine ja-stem model (Table 9.5, p. 468). -/
def duse : Noun := { form := "duše", gloss := "soul", gender := .feminine, cls := .duse }

/-- *paní* 'lady', "a unique item" (p. 468), the one ьja-stem (Table 9.5, p. 468). -/
def pani : Noun :=
  { form := "paní", gloss := "lady", gender := .feminine, naturalGender := some .feminine,
    cls := .pani }

/-- *kost* 'bone', the i-stem model (Table 9.6, p. 469). -/
def kost : Noun := { form := "kost", gloss := "bone", gender := .feminine, cls := .kost }

/-- *jehně* 'lamb', the neuter t-stem model (Table 9.7, p. 470). -/
def jehne : Noun := { form := "jehně", gloss := "lamb", gender := .neuter, cls := .jehne }

/-- *kluk* 'boy', a hard masculine animate with a velar stem, whose vocative singular *kluku* Short
gives as a survival of the u-stem vocative, "chiefly as a means to avoid palatalization of velar
stems" (p. 465). -/
def kluk : Noun :=
  { form := "kluk", gloss := "boy", gender := .mascAnimate, naturalGender := some .masculine,
    cls := .chlap }

/-! ### Nouns that change class with number -/

/-- *den* 'day', which follows *stroj* in the singular and *hrady* in the plural (Short, p. 469),
and whose oblique stem is *dn-* (Short, p. 463). -/
def den : Noun :=
  { form := "den", gloss := "day", gender := .mascInanimate, cls := .stroj, clsPlural := .hrad }

/-- *kořen* 'root', which follows *stroj* in the singular and *hrady* in the plural (Short,
p. 469), and which *Mluvnice češtiny* lists among the masculines with a stem in *-en-* that
decline soft in the singular and hard in the plural (p. 310). -/
def koren : Noun :=
  { form := "kořen", gloss := "root", gender := .mascInanimate, cls := .stroj,
    clsPlural := .hrad }

/-- *pramen* 'spring', which follows *stroj* in the singular and *hrady* in the plural.
*Mluvnice češtiny* lists it with the masculines whose stem ends in *-en-*, the former n-stems,
"řemen, ječmen, kámen, kmen, hřeben, kořen, křemen, plamen, pramen ap.", and says that "Tato
jména mají dnes v sg tvary shodné se skloňováním měkkým, v pl se skloňováním tvrdým (tvary
„tvrdé“ pronikají i do sg)" 'these nouns today have the forms of the soft declension in the
singular and of the hard declension in the plural (the hard forms also entering the singular)'
(p. 310). Short does not mention it. -/
def pramen : Noun :=
  { form := "pramen", gloss := "spring", gender := .mascInanimate, cls := .stroj,
    clsPlural := .hrad }

/-! ### Stump's nouns -/

/-- *pokoj* 'room', a masculine inanimate declined as *stroj*. *Mluvnice češtiny* makes the soft
declension obligatory for a stem ending in a morphonologically soft consonant (p. 290, of the
animates) and the final consonant of the *stroj* type soft (p. 309), and the nouns it lists for
the type include *kraj*, *boj* and *orloj*, in *j* like *pokoj* (p. 309). It names no soft
consonants, nor *pokoj* itself. -/
def pokoj : Noun :=
  { form := "pokoj", gloss := "room", gender := .mascInanimate, cls := .stroj }

/-- *most* 'bridge', a masculine inanimate declined as *hrad*. -/
def most : Noun := { form := "most", gloss := "bridge", gender := .mascInanimate, cls := .hrad }

/-- *předseda* 'chairman', a masculine a-stem declined as *hrdina*, of "the masculine
a-declension" (Short, p. 467), and the model noun of *Mluvnice češtiny*'s third type of the
masculine animates (p. 290). -/
def predseda : Noun :=
  { form := "předseda", gloss := "chairman", gender := .mascAnimate, cls := .hrdina }

/-- *sluha* 'servant', a masculine a-stem declined as *hrdina*, whose locative plural both
grammars give as *sluzích* (Short, p. 467; *Mluvnice češtiny*, pp. 292, 300). -/
def sluha : Noun := { form := "sluha", gloss := "servant", gender := .mascAnimate, cls := .hrdina }

/-- *filosof* 'philosopher', a masculine animate declined as *chlap*, the hard subtype taking
every noun whose stem ends in *b*, *f*, *m*, *p* or *v* (*Mluvnice češtiny*, p. 294). Its
nominative plural is in neither grammar: Short does not place it among the subclasses in *-é*
or *-ové* (p. 466), and *Mluvnice češtiny* mentions the noun once, spelled *filozof*, among the
Latin borrowings that lost *-us* (p. 340). -/
def filosof : Noun :=
  { form := "filosof", gloss := "philosopher", gender := .mascAnimate, cls := .chlap }

/-- *filolog* 'philologist', a masculine animate declined as *chlap*, with a velar stem, which
takes the vocative singular *-u* (Short, p. 465; *Mluvnice češtiny*, p. 292) and the locative
plural *filolozích* (*Mluvnice češtiny*, p. 295). Its nominative plural is *-ové*, which
*Mluvnice češtiny* calls "výrazně jedinou podobou" 'clearly the only form' of the borrowed
masculines in *-log*, naming *filolog* (p. 296), although it gives *filolog – filolozi* as its
example of the alternation of *g* before the nominative plural *-i* (p. 294). -/
def filolog : Noun :=
  { form := "filolog", gloss := "philologist", gender := .mascAnimate, cls := .chlap,
    nomPlural := some [["o", "v", "é"]] }

/-- The entries are the model nouns of Short's tables, *kluk*, *den*, *kořen* and *pramen*, and
Stump's other nouns. -/
def nouns : List Noun :=
  [chlap, hrad, muz, stroj, mesto, srdce, uceni, zena, hrdina, duse, pani, kost, jehne, kluk, den,
    koren, pramen, pokoj, most, predseda, sluha, filosof, filolog]

/-- Every entry's citation form is its stem followed by the nominative singular ending of its
class, so each is declined in a class whose nominative singular it has. -/
theorem stem_append_nomSg : ∀ n ∈ nouns, n.stem ++ n.cls.nomSg = segments n.form := by
  decide +kernel

/-- The velar stems among the entries are those of *kluk*, *sluha* and *filolog*, ending in *k*,
*h* and *g*. -/
theorem isVelar_stem_iff :
    ∀ n ∈ nouns, IsVelar n.stem ↔ n = kluk ∨ n = sluha ∨ n = filolog := by
  decide +kernel

/-- Every form of every entry is written in Czech letters, and so has phonemes. -/
theorem isSome_ofChars_forms :
    ∀ n ∈ nouns, ∀ σ, ∀ w ∈ n.forms σ, (Phonology.ofChars (w.flatMap String.toList)).isSome := by
  decide +kernel

/-- Every entry has the gender of its class's table. -/
theorem gender_eq_cls_gender : ∀ n ∈ nouns, n.gender = n.cls.gender := by decide

/-- The entries give Stump's nouns the forms that *Mluvnice češtiny* states where these depart
from the model nouns' tables: *muži* and *mužové* (p. 298), *filologové* (p. 296), *filolozích*
(p. 295) and *sluzích* (pp. 292, 300); *filologu* by the velar vocative rule (p. 292); and the
soft genitive singular *pramene* beside the hard nominative plural *prameny* (p. 310). -/
theorem forms_examples :
    muz.forms (.of .nom .plural) = [segments "muži", segments "mužové"] ∧
      filolog.forms (.of .nom .plural) = [segments "filologové"] ∧
      filolog.forms (.of .voc .singular) = [segments "filologu"] ∧
      filolog.forms (.of .loc .plural) = [segments "filolozích"] ∧
      sluha.forms (.of .loc .plural) = [segments "sluzích"] ∧
      pramen.forms (.of .gen .singular) = [segments "pramene"] ∧
      pramen.forms (.of .nom .plural) = [segments "prameny"] := by
  decide +kernel

end Czech
