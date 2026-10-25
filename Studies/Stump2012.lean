module

public import Linglib.Data.Wordlist.Stump2012
public import Linglib.Morphology.Paradigm.Linkage
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

/-!
# Stump (2012): The Formal and Functional Architecture of Inflectional Morphology

This file formalizes [stump-2012-mmm8]'s architecture of inflection, in which a lexeme's
content paradigm is linked to the form paradigms of its stems, and its account of
noncanonical inflection as deviation from canonical paradigm linkage. Canonical linkage is
total, univalent, stem-invariant, injective and property-preserving, the five axes of the
substrate's `Morphology.Linkage.IsCanonical`, and the Breton inflecting preposition HERVEZ is the
paper's canonical witness (`hervez_isCanonical`). Each noncanonical phenomenon deviates on
one axis: Latin COEPISSE lacks present-system stems and is defective without being
suppletive (`coepisse_defective_not_suppletive`), Latin BELLUM shares form correspondents
between the nominative and the accusative and between the dative and the ablative, the
directional and nondirectional syncretisms of the paper's rules (24) and (25)
(`bellum_nom_acc_syncretic`, `bellum_nom_acc_realize_eq`), deponent HORTĀRĪ has passive
form correspondents for its active content cells and none for its passive ones
(`hortari_unfaithful`, `hortari_defective`, `hortari_active_form_virtual`), the Hungarian
pronoun ÉN takes its oblique-case forms from case stems inflected for the pronoun's own
person and number, the functor-argument reversal of rule (37)
(`en_functor_argument_reversal`, `en_pm_lexeme_sensitive`), and Latin FERRE has two stems
in complementary distribution under the default rule alone, suppletive yet
property-preserving (`ferre_suppletive_yet_faithful`). The deviations compound: Old
Icelandic ÞURFA forms its present as a strong verb forms its past and its past on a weak
stem, deponent and suppletive at once (`thurfa_suppletive_and_unfaithful`).

The forms of the paper's examples are read from the forms data (`attested`). Where the
paper's realization follows from a stem and an ending, the ending is read off an exemplar:
COEPISSE's perfect endings are FERRE's (`coepisse_perfect_realized`), and HORTĀRĪ's
passive endings are LAUDĀRE's, which realize the deponent's active content cells
(`hortari_realizes_hortor`, `depon_vs_regular`).

## Implementation notes

The Breton, Latin and Old Icelandic linkages give content and form cells one type of property
sets, identified by `id`; the Hungarian pronouns' content cells carry cases and their form cells
person-number sets, a case being identified with the form property set `HuProp.case`. The
merged dative/ablative form cell of rule (25) is represented by the dative, with both
content cells mapped there. Deponent HORTĀRĪ's stem is taken as the segments before the
personal ending, as is LAUDĀRE's, so that the endings are shared. The Hungarian pronoun's
direct-case forms and the full Old Icelandic paradigm of (44) are not represented; the
paper's discussion of the later Latin active *hortābat* as an exploratory expression is
described only in the docstring of the virtual form cell.

## References

* [stump-2012-mmm8]
* [hippisley-2010]
-/

@[expose] public section

namespace Stump2012

open Morphology CLDF.Wordlist

/-- `attested pid c` is the segmentation of the first attested form with parameter `pid` in the
cell `c`, or the empty list when there is none. -/
def attested (pid : String) (c : Wordlist.Cell) : List String :=
  ((Wordlist.all.find? fun f ↦ f.parameterId == pid && f.cell == c).map (·.segments)).getD []

/-- `Agr` lists the six person-number agreement values that the Latin verb paradigms share. -/
inductive Agr
  | s1
  | s2
  | s3
  | p1
  | p2
  | p3
  deriving DecidableEq, Fintype, Repr

/-- The person of an agreement value. -/
def Agr.person : Agr → UD.Person
  | .s1 | .p1 => .first
  | .s2 | .p2 => .second
  | .s3 | .p3 => .third

/-- The number of an agreement value. -/
def Agr.number : Agr → UD.Number
  | .s1 | .s2 | .s3 => .Sing
  | .p1 | .p2 | .p3 => .Plur

/-- `a.cell c` is the cell `c` with the person and number of the agreement value `a`. -/
def Agr.cell (a : Agr) (c : Wordlist.Cell := {}) : Wordlist.Cell :=
  { c with person := ↑a.person, number := ↑a.number }

/-- `System` splits the Latin verb cells into present-system and perfect-system cells. -/
inductive System
  | pres
  | perf
  deriving DecidableEq, Fintype, Repr


/-! ### Breton HERVEZ: the canonical baseline -/

section Breton

/-- `HervezLex` has the single lexeme HERVEZ 'according to', an inflecting preposition. -/
inductive HervezLex
  | hervez
  deriving DecidableEq, Fintype, Repr

/-- HERVEZ has a single stem. -/
inductive HervezStem
  | hervez
  deriving DecidableEq, Fintype, Repr

/-- HERVEZ's linkage has one stem and the identity property mapping, the canonical pattern of
the paper's (14). -/
def hervezLinkage : Linkage HervezLex HervezStem Agr Agr := Linkage.canonical id fun _ ↦ .hervez

/-- HERVEZ is canonical on all five axes. -/
theorem hervez_isCanonical : hervezLinkage.IsCanonical id :=
  Linkage.canonical_isCanonical Function.injective_id _

end Breton

/-! ### Latin COEPISSE: defectiveness -/

section Coepisse

inductive CoepLex
  | coepisse
  deriving DecidableEq, Fintype, Repr

inductive CoepStem
  | coep
  deriving DecidableEq, Fintype, Repr

/-- A Latin verb content cell pairs a tense system with an agreement feature. -/
structure SysCell where
  sys : System
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype SysCell :=
  Fintype.ofEquiv (System × Agr)
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun c ↦ (c.sys, c.agr), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- COEPISSE's linkage follows the stem specification (18), which gives the perfect-system
cells the stem `coep` and the present-system cells no stem. -/
def coepisseLinkage : Linkage CoepLex CoepStem SysCell SysCell where
  realize _ σ := match σ.sys with | .perf => {.coep} | .pres => ∅
  pm _ σ := σ

/-- `perfEnding a` is the perfect ending for the agreement `a`, read off FERRE's perfect form
of (41) after its stem `tul`. -/
def perfEnding (a : Agr) : List String :=
  (attested "carry" (a.cell { system := ↑Wordlist.System.perf })).drop 3

/-- A form cell of `coep` realizes as the stem followed by the perfect ending. -/
def coepRealize : CoepStem → SysCell → List String
  | _, σ => ["c", "o", "e", "p"] ++ perfEnding σ.agr

/-- COEPISSE is defective because its present-system cells lack a stem. -/
theorem coepisse_defective : coepisseLinkage.IsDefective := ⟨.coepisse, ⟨.pres, .s1⟩, rfl⟩

/-- The third singular present-system content cell has no realization. -/
theorem coepisse_present_no_realization :
    coepisseLinkage.realized coepRealize .coepisse ⟨.pres, .s3⟩ = ∅ := by decide

/-- Every perfect-system content cell realizes through its `coep` correspondent as the
paper's (17) lists, with FERRE's perfect endings. -/
theorem coepisse_perfect_realized (a : Agr) :
    coepisseLinkage.realized coepRealize .coepisse ⟨.perf, a⟩ =
      {(attested "begin" (a.cell { system := ↑Wordlist.System.perf }), ⟨.perf, a⟩)} := by
  revert a; decide

/-- COEPISSE keeps a single stem, so it is stem-invariant. -/
theorem coepisse_stemInvariant : coepisseLinkage.IsStemInvariant := by decide

/-- COEPISSE is defective without being suppletive, deviating on totality but not on stem
invariance. -/
theorem coepisse_defective_not_suppletive :
    coepisseLinkage.IsDefective ∧ ¬ coepisseLinkage.IsSuppletive .coepisse :=
  ⟨coepisse_defective, fun h ↦
    coepisseLinkage.not_isInvariant_of_isSuppletive h (coepisse_stemInvariant _)⟩

end Coepisse

/-! ### Latin BELLUM: syncretism -/

section Bellum

inductive BellumLex
  | bellum
  deriving DecidableEq, Fintype, Repr

inductive BellumStem
  | bell
  deriving DecidableEq, Fintype, Repr

inductive Case
  | nom
  | gen
  | dat
  | acc
  | abl
  deriving DecidableEq, Fintype, Repr

/-- `c.ud` is the case `c` in the forms data. -/
def Case.ud : Case → UD.Case
  | .nom => .Nom | .gen => .Gen | .dat => .Dat | .acc => .Acc | .abl => .Abl

inductive Num
  | sg
  | pl
  deriving DecidableEq, Fintype, Repr

/-- `n.ud` is the number `n` in the forms data. -/
def Num.ud : Num → UD.Number
  | .sg => .Sing
  | .pl => .Plur

/-- A BELLUM content cell pairs a case with a number. -/
structure BellumCell where
  case : Case
  num : Num
  deriving DecidableEq, Repr

instance : Fintype BellumCell :=
  Fintype.ofEquiv (Case × Num)
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun c ↦ (c.case, c.num), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The property mapping sends the nominative to the accusative, the directional neuter
syncretism of rule (24), and the ablative to the dative, which represents the merged
dative/ablative cell of rule (25). -/
def bellumPm (σ : BellumCell) : BellumCell :=
  match σ.case with
  | .nom => { σ with case := .acc }
  | .abl => { σ with case := .dat }
  | _ => σ

/-- BELLUM's linkage has one stem and the syncretizing property mapping. -/
def bellumLinkage : Linkage BellumLex BellumStem BellumCell BellumCell where
  realize _ _ := {.bell}
  pm _ σ := bellumPm σ

/-- `bellRealize` reads the realization of each form cell of `bell` off the attested forms,
the paper's (22). -/
def bellRealize : BellumStem → BellumCell → List String
  | _, σ => attested "war" { case := ↑σ.case.ud, number := ↑σ.num.ud }

/-- The nominative and accusative singular share a form correspondent, a directional
syncretism. -/
theorem bellum_nom_acc_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.nom, .sg⟩, ⟨.acc, .sg⟩, by decide, by decide⟩

/-- The dative and ablative singular share a form correspondent, a nondirectional
syncretism. -/
theorem bellum_dat_abl_syncretic : bellumLinkage.IsSyncretic :=
  ⟨.bellum, ⟨.dat, .sg⟩, ⟨.abl, .sg⟩, by decide, by decide⟩

/-- The nominative and accusative singular have the same realization because they share a
form correspondent, the paper's (26). -/
theorem bellum_nom_acc_realize_eq :
    bellumLinkage.realized bellRealize .bellum ⟨.nom, .sg⟩ =
      bellumLinkage.realized bellRealize .bellum ⟨.acc, .sg⟩ :=
  bellumLinkage.realized_eq_of_corr_eq bellRealize (by decide)

/-- The nominative singular realizes through the accusative form cell. -/
theorem bellum_nom_realizes_acc :
    bellumLinkage.realized bellRealize .bellum ⟨.nom, .sg⟩ =
      {(attested "war" { case := ↑UD.Case.Acc, number := ↑UD.Number.Sing }, ⟨.acc, .sg⟩)} := by
  decide

/-- BELLUM's linkage is not injective, since syncretism is a failure of injectivity. -/
theorem bellum_not_injective : ¬ bellumLinkage.IsInjective :=
  bellumLinkage.not_isInjective_iff.mpr bellum_nom_acc_syncretic

end Bellum

/-! ### Latin HORTĀRĪ: deponency, defectiveness and virtual cells -/

section Hortari

inductive LatinVerb
  | hortari
  | laudare
  deriving DecidableEq, Fintype, Repr

inductive VerbStem
  | hort
  | laud
  deriving DecidableEq, Fintype, Repr

inductive Voice
  | active
  | passive
  deriving DecidableEq, Fintype, Repr

/-- `v.ud` is the voice `v` in the forms data. -/
def Voice.ud : Voice → UD.Voice
  | .active => .Act
  | .passive => .Pass

/-- A finite content cell pairs a voice with an agreement feature. -/
structure VCell where
  voice : Voice
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype VCell :=
  Fintype.ofEquiv (Voice × Agr)
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun c ↦ (c.voice, c.agr), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- In the linkage of the two verbs, deponent HORTĀRĪ has a stem on its active cells only and
the voice-flipping property mapping of rule (29), the stem specification (30a), while regular
LAUDĀRE is canonical, (30b). -/
def latinLinkage : Linkage LatinVerb VerbStem VCell VCell where
  realize l σ := match l, σ.voice with
    | .hortari, .active => {.hort}
    | .hortari, .passive => ∅
    | .laudare, _ => {.laud}
  pm l σ := match l with
    | .hortari => { σ with voice := .passive }
    | .laudare => σ

/-- `personalEnding v a` is the personal ending for the voice `v` and the agreement `a`, read
off LAUDĀRE's forms of (28) after its stem. -/
def personalEnding (v : Voice) (a : Agr) : List String :=
  (attested "praise" (a.cell { voice := ↑v.ud })).drop 4

/-- A form cell realizes as its stem followed by the ending of the form cell's voice. -/
def verbRealize : VerbStem → VCell → List String
  | .hort, τ => ["h", "o", "r", "t"] ++ personalEnding τ.voice τ.agr
  | .laud, τ => ["l", "a", "u", "d"] ++ personalEnding τ.voice τ.agr

/-- HORTĀRĪ's deponency makes the linkage unfaithful, since the property mapping flips its
active content cells to passive. -/
theorem hortari_unfaithful : latinLinkage.IsUnfaithful id :=
  ⟨.hortari, ⟨.active, .s1⟩, by decide⟩

/-- Every active content cell of HORTĀRĪ has a passive form correspondent. -/
theorem hortari_active_realized_by_passive (a : Agr) :
    (latinLinkage.corr .hortari ⟨.active, a⟩).image (·.2.voice) = {.passive} := by
  revert a; decide

/-- The active content cells of HORTĀRĪ realize with LAUDĀRE's passive endings, as the
paper's (28) lists. -/
theorem hortari_realizes_hortor (a : Agr) :
    latinLinkage.realized verbRealize .hortari ⟨.active, a⟩ =
      {(attested "urge" (a.cell { voice := ↑UD.Voice.Pass }), ⟨.passive, a⟩)} := by
  revert a; decide

/-- On the same active content cell, LAUDĀRE realizes through an active form cell and HORTĀRĪ
through a passive one. -/
theorem depon_vs_regular (a : Agr) :
    latinLinkage.realized verbRealize .laudare ⟨.active, a⟩ =
        {(attested "praise" (a.cell { voice := ↑UD.Voice.Act }), ⟨.active, a⟩)} ∧
      latinLinkage.realized verbRealize .hortari ⟨.active, a⟩ =
        {(attested "urge" (a.cell { voice := ↑UD.Voice.Pass }), ⟨.passive, a⟩)} := by
  revert a; decide

/-- Deponency compounds with defectiveness, since the passive content cells of HORTĀRĪ lack a
stem. -/
theorem hortari_defective : latinLinkage.IsDefective := ⟨.hortari, ⟨.passive, .s1⟩, rfl⟩

/-- The first singular active form cell of `hort` is virtual. No content cell corresponds to
it, since active content maps to passive form and passive content has no correspondent. The
later Latin active *hortābat*, as [hippisley-2010] describes, releases it. -/
theorem hortari_active_form_virtual : latinLinkage.IsVirtual (.hort, ⟨.active, .s1⟩) := by
  decide

end Hortari

/-! ### Hungarian ÉN: functor-argument reversal -/

section Hungarian

/-- `Pron` has the personal pronouns ÉN '1sg' and TE '2sg'. -/
inductive Pron
  | en
  | te
  deriving DecidableEq, Fintype, Repr

/-- `HuCase` lists the oblique cases of (38) represented here. -/
inductive HuCase
  | dative
  | inessive
  | superessive
  deriving DecidableEq, Fintype, Repr

/-- `PersNum` lists the pronominal person-number properties that a form cell carries. -/
inductive PersNum
  | p1sg
  | p2sg
  deriving DecidableEq, Fintype, Repr

/-- `pn.cell` is the cell of the person-number property `pn` in the forms data. -/
def PersNum.cell : PersNum → Wordlist.Cell
  | .p1sg => { person := ↑UD.Person.first, number := ↑UD.Number.Sing }
  | .p2sg => { person := ↑UD.Person.second, number := ↑UD.Number.Sing }

/-- A form property set of a Hungarian case stem is a case, the property set that a faithful
correspondent of a case content cell would carry, or a person-number set. -/
inductive HuProp
  | case (c : HuCase)
  | agr (pn : PersNum)
  deriving DecidableEq, Fintype, Repr

/-- `CaseStem` lists the case postposition stems *nek*, *benn* and *rajt*. -/
inductive CaseStem
  | nek
  | benn
  | rajt
  deriving DecidableEq, Fintype, Repr

def CaseStem.pid : CaseStem → String
  | .nek => "nek"
  | .benn => "benn"
  | .rajt => "rajt"

/-- In the stem selection of rule (37), the case picks the postpositional stem. -/
def enStems : Pron → HuCase → Finset CaseStem
  | _, .dative => {.nek}
  | _, .inessive => {.benn}
  | _, .superessive => {.rajt}

/-- The property mapping computes the form property set from the lexeme, the
functor-argument reversal of (32) and (37). -/
def enPm : Pron → HuCase → HuProp
  | .en, _ => .agr .p1sg
  | .te, _ => .agr .p2sg

/-- The pronouns' linkage selects the stem by case and the form property set by lexeme; its
content cells carry cases and its form cells person-number sets. -/
def enLinkage : Linkage Pron CaseStem HuCase HuProp where
  realize := enStems
  pm := enPm

/-- A person-number form cell of a case stem realizes as the inflected postposition of
(36). -/
def enRealize : CaseStem → HuProp → List String
  | z, .agr pn => attested z.pid pn.cell
  | _, _ => []

/-- The inessive of ÉN corresponds to the 1sg form cell of *benn*, the paper's (38). -/
theorem en_inessive_corr : enLinkage.corr .en .inessive = {(.benn, .agr .p1sg)} := by
  decide

/-- Every oblique case content cell has the case's postpositional stem, so the pronouns'
linkage is total. -/
theorem en_isTotal : enLinkage.IsTotal := by decide

/-- The reversal is unfaithful, since the correspondent's property set is the pronoun's, not
the case's. -/
theorem en_functor_argument_reversal : enLinkage.IsUnfaithful HuProp.case :=
  ⟨.en, .inessive, by decide⟩

/-- ÉN and TE send the same inessive content cell to different form property sets, so the
property mapping consults the lexeme. -/
theorem en_pm_lexeme_sensitive :
    enLinkage.pm .en .inessive ≠ enLinkage.pm .te .inessive := by
  decide

/-- The inessive of ÉN and of TE realize as the first and second person forms of *benn*. -/
theorem inessive_realizes :
    enLinkage.realized enRealize .en .inessive =
        {(attested "benn" PersNum.p1sg.cell, .agr .p1sg)} ∧
      enLinkage.realized enRealize .te .inessive =
        {(attested "benn" PersNum.p2sg.cell, .agr .p2sg)} := by
  decide

end Hungarian

/-! ### Latin FERRE: suppletion under the default rule -/

section Ferre

inductive FerreLex
  | ferre
  deriving DecidableEq, Fintype, Repr

inductive FerreStem
  | fer
  | tul
  deriving DecidableEq, Fintype, Repr

/-- In FERRE's linkage, the stem specification (42) gives two suppletive stems in
complementary distribution, and the default rule supplies the identity property mapping. -/
def ferreLinkage : Linkage FerreLex FerreStem SysCell SysCell where
  realize _ σ := match σ.sys with | .pres => {.fer} | .perf => {.tul}
  pm _ σ := σ

/-- FERRE is suppletive because its present- and perfect-system cells draw on different
stems. -/
theorem ferre_suppletive : ferreLinkage.IsSuppletive .ferre := by decide

/-- FERRE is property-preserving, since with no override the default rule preserves the
content cell's property set. -/
theorem ferre_propertyPreserving : ferreLinkage.IsPropertyPreserving id := fun _ _ ↦ rfl

/-- FERRE is suppletive yet property-preserving, so the two axes are independent. -/
theorem ferre_suppletive_yet_faithful :
    ferreLinkage.IsSuppletive .ferre ∧ ferreLinkage.IsPropertyPreserving id :=
  ⟨ferre_suppletive, ferre_propertyPreserving⟩

end Ferre

/-! ### Old Icelandic ÞURFA: a compound deviation -/

section Thurfa

inductive ThurfaLex
  | thurfa
  deriving DecidableEq, Fintype, Repr

/-- ÞURFA has the strong stem *þarf* and the weak stem *þurf*. -/
inductive ThurfaStem
  | strong
  | weak
  deriving DecidableEq, Fintype, Repr

inductive Tense
  | pres
  | past
  deriving DecidableEq, Fintype, Repr

/-- A ÞURFA content cell pairs a tense with an agreement feature. -/
structure TCell where
  tense : Tense
  agr : Agr
  deriving DecidableEq, Repr

instance : Fintype TCell :=
  Fintype.ofEquiv (Tense × Agr)
    ⟨fun p ↦ ⟨p.1, p.2⟩, fun c ↦ (c.tense, c.agr), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- ÞURFA's linkage, the paper's (45) and (46), gives the present the strong stem and the past
the weak stem, a suppletion, and its property mapping sends every cell to the past, the
deponent tense. -/
def thurfaLinkage : Linkage ThurfaLex ThurfaStem TCell TCell where
  realize _ σ := match σ.tense with | .pres => {.strong} | .past => {.weak}
  pm _ σ := { σ with tense := .past }

/-- In the realizations of (46), the strong stem at a past form cell gives the present forms
and the weak stem the past forms. -/
def thurfaRealize : ThurfaStem → TCell → List String
  | .strong, τ => attested "need" (τ.agr.cell { tense := ↑UD.Tense.Pres })
  | .weak, τ => attested "need" (τ.agr.cell { tense := ↑UD.Tense.Past })

/-- ÞURFA is suppletive because its present and past draw on different stems. -/
theorem thurfa_suppletive : thurfaLinkage.IsSuppletive .thurfa := by decide

/-- ÞURFA is unfaithful because a present content cell maps to a past form cell. -/
theorem thurfa_unfaithful : thurfaLinkage.IsUnfaithful id := ⟨.thurfa, ⟨.pres, .s1⟩, by decide⟩

/-- ÞURFA's linkage compounds suppletion with a deponent tense mapping. -/
theorem thurfa_suppletive_and_unfaithful :
    thurfaLinkage.IsSuppletive .thurfa ∧ thurfaLinkage.IsUnfaithful id :=
  ⟨thurfa_suppletive, thurfa_unfaithful⟩

/-- The present content cell realizes as *þarf* through the strong stem at the past form
cell, and the past content cell as *þurfta* through the weak stem. -/
theorem thurfa_realizes :
    thurfaLinkage.realized thurfaRealize .thurfa ⟨.pres, .s1⟩ =
        {(attested "need" (Agr.s1.cell { tense := ↑UD.Tense.Pres }), ⟨.past, .s1⟩)} ∧
      thurfaLinkage.realized thurfaRealize .thurfa ⟨.past, .s1⟩ =
        {(attested "need" (Agr.s1.cell { tense := ↑UD.Tense.Past }), ⟨.past, .s1⟩)} := by
  decide

end Thurfa

end Stump2012
