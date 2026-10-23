module

public import Linglib.Morphology.Exponence.Containment.Contiguity
public import Linglib.Fragments.Slavic.Czech.Nouns
public import Studies.Blake1994
public import Linglib.Data.Wordlist.Caha2009
public import Linglib.Morphology.Word.UD

/-!
# Caha (2009): The Nanosyntax of Case

This file formalizes Caha's Universal Contiguity (10): non-accidental case syncretism targets
contiguous regions of a sequence of cases that is the same in every language, nominative,
accusative, genitive, dative, instrumental, comitative. The evidence is the Slavic declensions of
chapter 8, read along the Slavic sequence with the prepositional between the genitive and the
dative (13). The paradigms of Caha's tables that are not contiguous are the ones whose syncretism
he treats as a phonological conflation or an accidental homophony, a Ukrainian variant he leaves
open, and a Slovene paradigm he passes over.

## Main definitions

* `sequence`: the Case sequence (10b)
* `slavicCase`, `form`: the Slavic sequence (13), nominative, accusative, genitive,
  prepositional, dative, instrumental, and a paradigm's forms along it; the paradigms are the
  columns of the Serbian, Slovene, Czech, Slovak and Ukrainian tables of chapter 8, read from
  `Data/Wordlist/Caha2009`
* `accounts`, `analyses`: Caha's treatment of the paradigms with an offending syncretism
* `czechCase`, `Declines`: the Czech case at each place of the sequence, and a noun of the Czech
  fragment declining a paradigm of the tables at a place

## Main results

* `exists_position_lt`: Blake's hierarchy orders the cases of the sequence as it does
* `not_isContiguous_iff`: the paradigms of the tables that are not contiguous
* `supersetSpellable_form`: Superset spellout generates the other paradigms
* `isContiguous_analysis`: the underlying forms Caha gives are contiguous
* `isNone_iff_adjacent`: the syncretisms (67) calls non-accidental are the adjacent ones
* `declines_czechNouns`, `declines_hrad_mesto_iff`, `declines_colloquial_iff`: Caha's literary
  Czech noun paradigms are the fragment's declensions after Short and *Mluvnice češtiny*

## Implementation notes

Two cells are syncretic when their forms are identical, which ignores Caha's shading. The data
records the segmentation each table prints and its departures: the column headings that are
wrong (Czech *kost* is 'bone', not 'castle'; the Czech *ta* of note 26 is feminine singular; the
Slovene *dva* of (16) is 'two', not 'both'), the nominatives printed with a weak form beside the
strong one, and the tables' indexing of endings. Where the tables decline a word in two ways
without naming the variety, as where two grammars decline a Ukrainian word differently, the
second paradigm's identifier ends in `_2`.

## TODO

* `not_isContiguous_iff` takes several seconds in the kernel, comparing forms as strings at
  every triple of cells; deciding it on the first occurrence of each form would compare each pair
  once.

## References

* [caha-2009]
* [blake-1994]
* [short-1993-czech]
* [komarek-etal-1986]
-/

@[expose] public section

namespace Caha2009

open CLDF.Wordlist (Paradigm)
open Wordlist
open Morphology.Containment (SupersetSpellable isContiguous_iff_spelloutGenerable)

/-! ### The Case sequence -/

/-- `sequence` is the Case sequence (10b): nominative, accusative, genitive, dative,
instrumental, comitative. -/
def sequence : Fin 6 → Case := ![.nom, .acc, .gen, .dat, .inst, .com]

/-- Blake's hierarchy orders the cases of the sequence (48) as the sequence does. -/
theorem exists_position_lt {i j : Fin 6} (h : i < j) :
    ∃ p q, Blake1994.position (sequence i) = some p ∧ Blake1994.position (sequence j) = some q ∧
      p < q := by
  revert i j; decide

/-! ### The Slavic tables

Caha's paradigms are the columns of the tables of chapter 8, read from `Data/Wordlist/Caha2009`
with the segmentation and the locator each table prints. A paradigm's form at a place of the
Slavic sequence (13) is its form in the cell of that case. -/

/-- `slavicCase i` is the case at the place `i` of the Slavic sequence (13): nominative,
accusative, genitive, prepositional, dative, instrumental, the prepositional as the locative. -/
def slavicCase : Fin 6 → Case := ![.nom, .acc, .gen, .loc, .dat, .inst]

/-- `form p i` is the form the paradigm `p` gives the case at the place `i` of the Slavic
sequence. -/
def form (p : Paradigm Wordlist.Cell) : Morphology.Paradigm 6 String := fun i ↦
  ((p.forms.find? (Morphology.Features.ofUD ·.cell .case = ↑(slavicCase i))).map (·.form)).getD ""

/-- `number p` is the number of the paradigm's cells. -/
def number (p : Paradigm Wordlist.Cell) : Option Number :=
  p.forms.head?.bind fun f ↦ Morphology.Features.ofUD f.cell .number

/-! ### Contiguity -/

/-- Caha accounts for an offending syncretism as a phonological conflation of distinct forms or as
an accidental homophony of distinct lexical entries. -/
inductive Account
  | conflation
  | accidental
  deriving DecidableEq, Repr

/-- `accounts` pairs each paradigm Caha accounts for with his account. -/
def accounts : List (Paradigm Wordlist.Cell × Account) :=
  [(slv_ta_n.paradigm, .conflation), (slv_potnik_pl.paradigm, .conflation),
    (slv_ta_f.paradigm, .accidental), (ukr_bezkrajij_msg_2.paradigm, .conflation),
    (ces_ulice_sg.paradigm, .accidental), (ces_muz_pl.paradigm, .conflation),
    (ces_dobry_fsg.paradigm, .conflation), (ces_vetsi_msg.paradigm, .conflation),
    (ces_vetsi_nsg.paradigm, .conflation), (ces_vul_pl.paradigm, .conflation),
    (ces_hoch_pl.paradigm, .conflation), (ces_kluk_pl.paradigm, .conflation)]

/-- `offenders` lists the paradigms Caha accounts for, the Ukrainian variant of 'region' he leaves
open (70), and the Slovene 'lady' (16), whose accusative–instrumental *gospó* he leaves unshaded
although he takes that syncretism to be confined to the declension of 'this'. -/
def offenders : List (Paradigm Wordlist.Cell) :=
  accounts.map Prod.fst ++ [ukr_kraj_sg_2.paradigm, slv_gospa_sg.paradigm]

/-- A paradigm of the tables is not contiguous exactly when it is an offender. -/
theorem not_isContiguous_iff :
    ∀ p ∈ Wordlist.paradigms, ¬ IsContiguous (form p) ↔ p ∈ offenders := by
  decide +kernel

/-- Superset spellout generates every paradigm of the tables but the offenders. -/
theorem supersetSpellable_form {p : Paradigm Wordlist.Cell} (hp : p ∈ Wordlist.paradigms)
    (h : p ∉ offenders) :
    SupersetSpellable (form p) :=
  (isContiguous_iff_spelloutGenerable _).1 <|
    not_not.1 fun hc ↦ h ((not_isContiguous_iff p hp).1 hc)

/-- `analyses` pairs a paradigm with the underlying ending or lexical index Caha gives each cell,
or `""`: the indexed endings of 'street' (40), the underlying endings of (19), (32), (52), (58)
and note 26, and the endings of p. 270. -/
def analyses : List (Paradigm Wordlist.Cell × Morphology.Paradigm 6 String) :=
  [(ces_ulice_sg.paradigm, !["e1", "i1", "e2", "i2", "i2", "í2"]),
    (ces_muz_pl.paradigm, !["i", "", "", "", "", "y"]),
    (ces_hoch_pl.paradigm, !["", "", "", "", "", "yø"]),
    (ces_vetsi_nsg.paradigm, !["e", "e", "eho", "em", "emu", "ím"]),
    (ces_dobry_fsg.paradigm, !["a", "u", "é", "é", "é", "ou"]),
    (slv_ta_n.paradigm, !["", "", "", "", "", "îm"]),
    (ukr_bezkrajij_msg_2.paradigm, !["", "", "", "im", "", "ım"])]

/-- Each analyzed paradigm is an offender, and its forms paired with their underlying endings
are contiguous. -/
theorem isContiguous_analysis :
    ∀ a ∈ analyses, a.1 ∈ offenders ∧ IsContiguous fun i ↦ (form a.1 i, a.2 i) := by
  decide +kernel

/-! ### The Czech syncretisms -/

/-- `czechCase i` is the Czech case at the place `i` of the Slavic sequence. -/
def czechCase : Fin 6 → _root_.Czech.Case := ![.nom, .acc, .gen, .loc, .dat, .inst]

/-- `Adjacent c d` holds when `d` follows `c` in the Slavic sequence. -/
def Adjacent (c d : _root_.Czech.Case) : Prop :=
  ∃ i : Fin 5, czechCase i.castSucc = c ∧ czechCase i.succ = d

instance (c d : _root_.Czech.Case) : Decidable (Adjacent c d) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- `table67` is Caha's summary of the Czech syncretisms (67), each with his account, `none` for
the non-accidental ones. -/
def table67 : List (_root_.Czech.Case × _root_.Czech.Case × Option Account) :=
  [(.nom, .acc, none), (.nom, .gen, some .accidental), (.nom, .inst, some .conflation),
    (.acc, .gen, none), (.acc, .loc, some .accidental), (.acc, .inst, some .conflation),
    (.gen, .loc, none), (.loc, .dat, none), (.loc, .inst, some .conflation), (.dat, .inst, none)]

/-- The syncretisms (67) calls non-accidental are the ones of adjacent cases. -/
theorem isNone_iff_adjacent : ∀ r ∈ table67, r.2.2 = none ↔ Adjacent r.1 r.2.1 := by
  decide

/-! ### Caha's Czech nouns and Short's declensions

Caha's Czech noun paradigms are those of the fragment's declension classes, the classes of
[short-1993-czech]'s tables with the stem conditions of [komarek-etal-1986]: each form of the
literary paradigms is one of the forms the fragment gives the noun. The plural of *kluk* 'boy'
depends on the stem conditions, since the tables alone would give *kluki* and *klukech* where Caha
has *kluci* and *klucích*. Caha's *hradu* and *městu* are the locative singular in *-u* that Short
describes beside the tables' *-ě* for the hard inanimates (p. 466) and the neuters (p. 467), and
his colloquial paradigms depart from the literary declension in the locative and the
instrumental. -/

/-- A noun of the fragment declines a paradigm of the tables at a place of the sequence when the
paradigm's form there is one of the noun's forms in that case and the paradigm's number. -/
def Declines (n : _root_.Czech.Noun) (p : Paradigm Wordlist.Cell) (i : Fin 6) : Prop :=
  ∃ m ∈ number p, ∃ h : m ∈ _root_.Czech.Declension.numbers,
    _root_.Czech.Declension.segments (form p i) ∈ n.forms (czechCase i, ⟨_, h⟩)

instance (n : _root_.Czech.Noun) (p : Paradigm Wordlist.Cell) (i : Fin 6) :
    Decidable (Declines n p i) :=
  inferInstanceAs (Decidable (∃ m ∈ number p, _))

/-- The literary paradigms of the tables that decline nouns of the fragment, with the nouns. -/
def czechNouns : List (Paradigm Wordlist.Cell × _root_.Czech.Noun) :=
  [(ces_muz_sg.paradigm, _root_.Czech.muz), (ces_muz_pl.paradigm, _root_.Czech.muz),
    (ces_stroj_sg.paradigm, _root_.Czech.stroj), (ces_stroj_pl.paradigm, _root_.Czech.stroj),
    (ces_kost_sg.paradigm, _root_.Czech.kost), (ces_kost_pl.paradigm, _root_.Czech.kost),
    (ces_zena_sg.paradigm, _root_.Czech.zena), (ces_zena_pl.paradigm, _root_.Czech.zena),
    (ces_kluk_pl.paradigm, _root_.Czech.kluk)]

/-- The fragment declines each literary paradigm of the tables at every place. -/
theorem declines_czechNouns : ∀ x ∈ czechNouns, ∀ i, Declines x.2 x.1 i := by
  decide +kernel

/-- The endings of Short's table on the bare stem do not give Caha's nominative *kluci* and
locative *klucích*. -/
theorem kluk_pl_not_mem_table :
    _root_.Czech.Declension.segments (form ces_kluk_pl.paradigm 0) ∉
        (_root_.Czech.Declension.Class.chlap.endings (.of .nom .plural)).map
          (_root_.Czech.kluk.stem ++ ·) ∧
      _root_.Czech.Declension.segments (form ces_kluk_pl.paradigm 3) ∉
        (_root_.Czech.Declension.Class.chlap.endings (.of .loc .plural)).map
          (_root_.Czech.kluk.stem ++ ·) := by
  decide +kernel

/-- The fragment declines Caha's *hrad* and *město* at every place but the locative, where Caha
has *hradu* and *městu* and the fragment the tables' *hradě* and *městě*. -/
theorem declines_hrad_mesto_iff (i : Fin 6) :
    (Declines _root_.Czech.hrad ces_hrad_sg.paradigm i ↔ czechCase i ≠ .loc) ∧
      (Declines _root_.Czech.mesto ces_mesto_sg.paradigm i ↔ czechCase i ≠ .loc) := by
  revert i; decide +kernel

/-- The colloquial *klukách* and *klukama* and *mužema* are not the literary declension, which
the colloquial paradigms follow at the other places. -/
theorem declines_colloquial_iff (i : Fin 6) :
    (Declines _root_.Czech.kluk ces_kluk_pl_colloquial.paradigm i ↔
        czechCase i ≠ .loc ∧ czechCase i ≠ .inst) ∧
      (Declines _root_.Czech.muz ces_muz_pl_colloquial.paradigm i ↔ czechCase i ≠ .inst) := by
  revert i; decide +kernel

end Caha2009
