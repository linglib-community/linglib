module

public import Linglib.Data.Wordlist.Stump2006
public import Linglib.Morphology.Paradigm.Linkage
public import Linglib.Morphology.Exponence.Domain
public import Linglib.Morphology.Word.UD
public import Linglib.Fragments.Slavic.Czech.Nouns
public import Linglib.Fragments.Slavic.Russian.Case
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Syntax.Number.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.DeriveFintype

/-!
# Stump (2006): Heteroclisis and paradigm linkage

This file formalizes Stump's account of heteroclisis, the property of a lexeme whose paradigm
contains forms built on stems of two or more inflection classes. A rule of paradigm linkage gives a
content cell of a lexeme a form correspondent built on one of the lexeme's stems: the universal
default assigns the root, and narrower language-specific rules override it by Pāṇini's principle,
assigning a coradical, a stem that differs from the root in form or in inflection class. The paper's
rules (5), (14), (15), (17) and (18), with the endings of the Czech declension fragment, after
Short's tables and the rules of *Mluvnice češtiny*, realize every form of the Czech nouns in its
Tables 1, 6 and 8, read from the forms data, once the masculine a-stems' nominative plural in -ové
is read from their own class and FILOSOF's, which neither grammar gives, is supplied. The
heteroclisis of Czech PRAMEN is morphosyntactically conditioned, its inflection class fixed by the
property sets its cells express, whereas that of Sanskrit AHAN is morphologically conditioned,
following a pattern of alternation among Strong, Middle and Weakest stems. Stump's Sanskrit rules of
paradigm linkage (20a,b) "are independently motivated by the need to account for the pattern of stem
alternation in nonheteroclite paradigms such as the masculine and neuter paradigms of PRATYAÑC"
(p. 295): one list of rules gives the grades of PRATYAÑC's stems, which share a declension, and the
stems of AHAN, which do not. The paper measures how closely a heteroclite paradigm's class boundary
follows an inflectional category, and claims that the categories serving as absolute correlates are
privileged: every rule of paradigm linkage sensitive to some category is sensitive to a privileged
one.

## Main definitions

* `attested`: the forms of a Czech cell, every matching row of the forms data.
* `Decl.toClass`, `CzNoun.noun`: the paper's declensions as classes of Short's tables, and the
  nouns as entries of the Czech noun fragment.
* `Stem`, `Entry`, `inferSoftMasc`: stems individuated by lexeme and declension, lexical
  entries read off the nouns, and the rule of stem inference (18).
* `CellRule`, `rulesFor`, `stemFor`: the rules of paradigm linkage (14), (15) and (17) as
  domain rules, resolved by the Elsewhere engine with the root of rule (5) as the fallback.
* `classNomPl`, `nomPlOverride`, `suppliedNomPl`: the masculine a-stems' nominative plural read
  from their class, FILOSOF's, which neither grammar gives, and the two together.
* `czRealize`, `czLinkage`: the realization of form cells and the Czech paradigm linkage.
* `degreeNum`, `degree`: the degree of correlation of a category with a class split.
* `IsAbsoluteCorrelate`, `IsMaximalCorrelate`, `IsCloven`, `IsFractured`,
  `IsIntersectiveCorrelate`: the paper's classification of heteroclite paradigms, over any
  cells pairing a case with a number.
* `SensitiveTo`, `Privileged`, `SatisfiesPCR`: the privileged category restriction.
* `SktForm`, `f₁`: Sanskrit form property sets and the property mapping (10).
* `strength`, `rule20a`, `rule20b`, `sktLinkage`: the strong and weak property sets of (19),
  the rules (20a,b), and the linkage of PRATYAÑC and AHAN.
* `hrdLinkage`, `matLinkage`: Sanskrit HṚD(AYA) and Russian MAT'.

## Main results

* `realize_matches_tables`: the rules realize every attested form of the nine Czech nouns.
* `czRealizeTable_stemFor_iff`: the fragment's endings alone miss exactly the six nominative and
  vocative plurals of PŘEDSEDA, SLUHA and FILOSOF.
* `predseda_eq_hrdina`, `sluha_eq_hrdina_iff`: rules (14) and (15) rebuild Short's paradigm of
  the masculine a-stems, from which SLUHA's departs only in the locative plural.
* `sluha_locPl`, `filolog_locPl`, `filologu_voc`: the grammars' velar forms, derived, the
  locative plurals alike through the soft-masculine coradical and the hard-masculine stem.
* `pramen_eq_koren_pattern`: rule (14) gives PRAMEN the classes the grammars give *kořen*.
* `heteroclite_iff`, `segments_invariant`, `pramen_suppletive`: PRAMEN, PŘEDSEDA, SLUHA and
  FILOLOG are heteroclite on form-identical stems, and heteroclisis is suppletion.
* `degreeNum_eq_card_iff`: a category is an absolute correlate exactly when the class split
  factors through it.
* `pramen_degrees`, `predseda_degrees`, `sluha_degrees`, `filolog_degrees`: the paper's figures.
* `isAbsoluteCorrelate_of_rules`: rules seeing only a category make it an absolute correlate.
* `pcr`, `not_satisfiesPCR_hypothetical`: the Czech rules satisfy (40), and a case-only rule
  would violate it.
* `fractured_minimal_intersective_privileged`: claim (39) for the Czech nouns.
* `rules_match_table9`, `rules_match_table10`: (19) and (20a,b) give PRATYAÑC's grades and
  AHAN's stems at every cell of Tables 9 and 10.
* `pratyanc_not_heteroclite`, `ahan_heteroclite`, `ahan_grade_eq_pratyancN`: one list of rules
  makes AHAN heteroclite and PRATYAÑC not, with the same grades.
* `ahan_degrees`, `ahan_fractured`: AHAN's paradigm is fractured, its case correlation .71.
* `hrd_cloven`, `privileged_case`, `pcr_skt`: case, the absolute correlate of HṚD(AYA)'s cloven
  paradigm, is privileged, and (20a,b) satisfy (40).
* `hrd_form_suppletive`, `mat_suppletive_not_heteroclite`: suppletion with and without
  heteroclisis.

## Implementation notes

A Czech noun's segments are the stem of its entry in the Czech noun fragment, the citation form less
the nominative singular ending of its class, so PŘEDSEDA's root and coradical share the segments
*předsed*. A stem's endings are the fragment's endings of its noun in the class that the stem's
declension is for the noun's animacy, with the velar vocative singular -u and locative plural -ích
and the noun's lexical nominative plural, MUŽ's -i or -ové and FILOLOG's -ové, and the stem is
inflected as the fragment inflects it, palatalized before the masculine locative plural -ích and the
animate nominative plural -i. Where the paper and the grammars differ the paper's forms stand and
the difference is stated: the nominative and vocative plurals in -ové of PŘEDSEDA and SLUHA,
realized on the hard-masculine coradical, whose class gives -i, are read from their own class, and
FILOSOF's, which neither grammar gives, is an override; Stump's hard-feminine roots for the
masculine a-stems rebuild Short's separate *hrdina* declension; and his soft-masculine coradical of
velar stems gives the locative plurals in -ích that *Mluvnice češtiny*'s rule gives the
hard-masculine stem.
Sanskrit endings are read off exemplars, chosen by declension among PRATYAÑC, NĀMAN and MANAS. Rules
compete by domain inclusion, the rendering of Pāṇini's principle, and selection falls back on the
root, by (5) and (12). Gender is taken as lexical: PRATYAÑC's masculine and neuter are two lexemes,
clause (ii) of `f₁` is vacuous, and the feminine, whose ī-stem *pratīcī* (n. 18) would make PRATYAÑC
heteroclite, is left out, as are n. 21's stem indexing and n. 22's alternants. Sanskrit sandhi
(*aho-bhis*, *pratyag-*) is unstated, so no forms are built. Rows are filtered by language.

## References

* [stump-2006]
* [stump-2001]
* [short-1993-czech]
* [komarek-etal-1986]
-/

@[expose] public section

namespace Stump2006

open Morphology CLDF.Wordlist Finset

/-! ### Cells and the attested forms -/

/-- A content cell of a Czech noun is a cell of Short's declension tables, pairing a case of the
Czech inventory with a number, gender being constant within a paradigm. -/
abbrev CzCell : Type := Czech.Declension.Cell

/-- The case of a form's cell. -/
def caseOfForm (f : Form Wordlist.Cell) : Option Case :=
  (f.cell.case : Option UD.Case).bind Case.fromUD

/-- The number of a form's cell. -/
def numberOfForm (f : Form Wordlist.Cell) : Option Number :=
  (f.cell.number : Option UD.Number).bind Number.fromUD

/-- `czForms` are the Czech rows of the forms data, those of Tables 1, 6 and 8. -/
def czForms : List (Form Wordlist.Cell) := Wordlist.all.filter (·.languageId == "czec1258")

/-- The Czech nouns of Tables 1, 6 and 8 are POKOJ 'room', PRAMEN 'spring', MOST 'bridge',
ŽENA 'woman', PŘEDSEDA 'president', FILOSOF 'philosopher', SLUHA 'servant', FILOLOG
'philologist' and MUŽ 'man'. -/
inductive CzNoun
  | pokoj
  | pramen
  | most
  | zena
  | predseda
  | filosof
  | sluha
  | filolog
  | muz
  deriving DecidableEq, Fintype, Repr

/-- `l.paramId` is the concept that the forms of `l` express in the forms data. -/
def CzNoun.paramId : CzNoun → String
  | .pokoj => "room" | .pramen => "spring" | .most => "bridge" | .zena => "woman"
  | .predseda => "president" | .filosof => "philosopher" | .sluha => "servant"
  | .filolog => "philologist" | .muz => "man"

/-- The attested forms of a cell are the segments of every row of the forms data for the noun
whose case code decodes to the comparative value of the cell's case and whose number code to its
number, so a cell with two alternants has two. -/
def attested (l : CzNoun) (σ : CzCell) : Finset (List String) :=
  ((czForms.filter fun f ↦ f.parameterId == l.paramId && caseOfForm f == some σ.case.label &&
      numberOfForm f == some σ.number).map (·.segments)).toFinset

theorem attested_nonempty : ∀ l σ, (attested l σ).Nonempty := by decide +kernel

theorem filosof_cellMates : 2 ≤ (attested .filosof (.of .dat .singular)).card := by decide

/-! ### Stems and lexical entries -/

/-- The three declensions the tables juxtapose are the soft masculine, the hard masculine and
the hard feminine. -/
inductive Decl
  | softMasc
  | hardMasc
  | hardFem
  deriving DecidableEq, Fintype, Repr

/-- A declension is, for animate and for inanimate stems, a declension of Short's tables, the
soft masculine being that of *muž* or *stroj*, the hard masculine that of *chlap* or *hrad*, and
the hard feminine that of *žena*. -/
def Decl.toClass : Decl → Bool → Czech.Declension.Class
  | .softMasc, true => .muz
  | .softMasc, false => .stroj
  | .hardMasc, true => .chlap
  | .hardMasc, false => .hrad
  | .hardFem, _ => .zena

theorem Decl.toClass_injective (a : Bool) : Function.Injective (Decl.toClass · a) := by
  cases a <;> decide

/-- `Decl.ofClass k` is the declension of the root of a noun of Short's class `k`, where the
nouns of the tables include one: the soft masculine for *muž* and *stroj*, the hard masculine
for *chlap* and *hrad*, and the hard feminine for *žena* and for the masculine a-stems of
*hrdina*, whose roots the paper takes to be hard-feminine. -/
def Decl.ofClass : Czech.Declension.Class → Option Decl
  | .muz | .stroj => some .softMasc
  | .chlap | .hrad => some .hardMasc
  | .zena | .hrdina => some .hardFem
  | _ => none

theorem Decl.ofClass_toClass (d : Decl) (a : Bool) : Decl.ofClass (d.toClass a) = some d := by
  cases d <;> cases a <;> rfl

/-- `l.noun` is the entry of `l` in the Czech noun fragment. -/
def CzNoun.noun : CzNoun → Czech.Noun
  | .pokoj => Czech.pokoj | .pramen => Czech.pramen | .most => Czech.most | .zena => Czech.zena
  | .predseda => Czech.predseda | .filosof => Czech.filosof | .sluha => Czech.sluha
  | .filolog => Czech.filolog | .muz => Czech.muz

/-- A stem is individuated, as in the paper, by its lexeme and its inflection class; its form
is the lexeme's, so two stems of one lexeme are class-distinct and form-identical. -/
structure Stem where
  /-- `lexeme` is the noun whose stem this is. -/
  lexeme : CzNoun
  /-- `decl` is the declension the stem inflects in. -/
  decl : Decl
  deriving DecidableEq, Repr

/-- A lexical entry records a noun's stem segments, the declension of its root, whether it
inflects as animate, and whether it belongs to the PRAMEN class of rule (14). -/
structure Entry where
  /-- `lexeme` is the noun the entry describes. -/
  lexeme : CzNoun
  /-- `segments` are the segments of the noun's stems. -/
  segments : List String
  /-- `rootDecl` is the declension of the noun's root. -/
  rootDecl : Decl
  /-- `animate` records whether the noun inflects as animate. -/
  animate : Bool
  /-- `pramenClass` records membership in the PRAMEN class, a lexical stipulation. -/
  pramenClass : Bool
  deriving DecidableEq, Repr

/-- `entry l` is the lexical entry of `l`, read off its noun. The segments are the noun's stem,
the root declension is that of the noun's singular class, so that PRAMEN's root is
soft-masculine (p. 289) and PŘEDSEDA's and SLUHA's are hard-feminine, and the noun inflects as
animate when its gender is the masculine animate. Membership in the PRAMEN class, which PRAMEN,
PŘEDSEDA and SLUHA have, is the lexical stipulation of rule (14). -/
def entry (l : CzNoun) : Entry where
  lexeme := l
  segments := l.noun.stem
  rootDecl := (Decl.ofClass l.noun.cls).get (by cases l <;> rfl)
  animate := decide l.noun.gender.IsAnimate
  pramenClass := l matches .pramen | .predseda | .sluha

/-- The segments of a stem are those of its lexeme's entry. -/
def Stem.segments (z : Stem) : List String := (entry z.lexeme).segments

/-- The root of a noun, its default stem (n. 8), inflects in the root declension. -/
def Entry.root (e : Entry) : Stem := ⟨e.lexeme, e.rootDecl⟩

/-- A stem is a root when it inflects in its lexeme's root declension. -/
def Stem.IsRoot (z : Stem) : Prop := z.decl = (entry z.lexeme).rootDecl

instance : DecidablePred Stem.IsRoot := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The hard-masculine coradical of a noun of the PRAMEN class is its stem in the
hard-masculine declension. -/
def Entry.hardMascCoradical (e : Entry) : Option Stem :=
  if e.pramenClass then some ⟨e.lexeme, .hardMasc⟩ else none

/-- A noun belongs to the PŘEDSEDA subclass, "a subclass of masculine animate members of the
PRAMEN class" (p. 290), when it is an animate member of the PRAMEN class. -/
def Entry.InPredsedaSubclass (e : Entry) : Prop := e.pramenClass = true ∧ e.animate = true

instance : DecidablePred Entry.InPredsedaSubclass :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- `inferSoftMasc` is the Czech rule of stem inference (18) (p. 292), which reads "If lexeme L
has a stem s belonging to the hard-masculine declension and s ends in a back obstruent, then L
has s′ as its soft-masculine coradical, where s′ is like s except that it belongs to the
soft-masculine declension." The back obstruents are Short's velars. -/
def inferSoftMasc (z : Stem) : Option Stem :=
  if z.decl = .hardMasc ∧ Czech.Declension.IsVelar z.segments then
    some { z with decl := .softMasc }
  else none

/-- The hard-masculine stem of a noun is its root if that is hard-masculine, and otherwise its
hard-masculine coradical. -/
def Entry.hardMascStem (e : Entry) : Option Stem :=
  if e.rootDecl = .hardMasc then some e.root else e.hardMascCoradical

/-- The soft-masculine coradical of a noun is the stem that rule (18) infers from its
hard-masculine stem. -/
def Entry.softMascCoradical (e : Entry) : Option Stem := e.hardMascStem.bind inferSoftMasc

-- (18)
theorem softMascCoradical_isSome_iff :
    ∀ l, (entry l).softMascCoradical.isSome ↔ l = .sluha ∨ l = .filolog := by
  decide

theorem Entry.lexeme_of_mem_hardMascCoradical {e : Entry} {z : Stem}
    (hz : z ∈ e.hardMascCoradical) : z.lexeme = e.lexeme := by
  unfold Entry.hardMascCoradical at hz
  split at hz
  · cases hz; rfl
  · cases hz

theorem Entry.lexeme_of_mem_softMascCoradical {e : Entry} {z : Stem}
    (hz : z ∈ e.softMascCoradical) : z.lexeme = e.lexeme := by
  obtain ⟨y, hy, hz⟩ := Option.mem_bind_iff.mp hz
  have hy : y.lexeme = e.lexeme := by
    unfold Entry.hardMascStem at hy
    split at hy
    · cases hy; rfl
    · exact e.lexeme_of_mem_hardMascCoradical hy
  unfold inferSoftMasc at hz
  split at hz
  · cases hz; exact hy
  · cases hz

/-! ### Rules of paradigm linkage -/

/-- A rule of paradigm linkage, instantiated for one noun, gives the cells of its domain form
correspondents built on its exponent, a stem. Rules are ordered by Pāṇini's principle, by which
"competition between two or more morphological markings is resolved in favor of the marking
having the narrowest 'meaning'" (n. 5): a rule whose domain is included in another's is the
more specific. -/
abbrev CellRule : Type := Exponence.DomainRule CzCell Stem

/-- `plural` is the set of plural cells, `{plural X}` in the paper's notation. -/
def plural : Finset CzCell := {σ | σ.number = .plural}

/-- `datLocSg` is the set of dative and locative singular cells. -/
def datLocSg : Finset CzCell := {σ | σ.number = .singular ∧ (σ.case = .dat ∨ σ.case = .loc)}

/-- `locPl` is the locative plural cell, `{locative plural X}` in the paper's notation. -/
def locPl : Finset CzCell := {σ | σ.case = .loc ∧ σ.number = .plural}

/-- Rule (14) (p. 289) reads "Where L is a nominal lexeme that belongs to the PRAMEN class and
has s as its hard-masculine coradical, if σ = {plural X}, then the content-cell ⟨L, σ⟩ has
⟨s, σ⟩ as its form-correspondent." -/
def rule14 (e : Entry) : Option CellRule := e.hardMascCoradical.map (⟨plural, ·⟩)

/-- Rule (15) (p. 290) reads "Where L is a nominal lexeme that belongs to the PŘEDSEDA subclass
and has s as its hard-masculine coradical, if σ = {α singular X} and α = dative or locative,
then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its form-correspondent." -/
def rule15 (e : Entry) : Option CellRule :=
  if e.InPredsedaSubclass then e.hardMascCoradical.map (⟨datLocSg, ·⟩) else none

/-- Rule (17) (p. 292) reads "Where L is a nominal lexeme having s as its soft-masculine
coradical, if σ = {locative plural X}, then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its
form-correspondent." -/
def rule17 (e : Entry) : Option CellRule := e.softMascCoradical.map (⟨locPl, ·⟩)

/-- The language-specific rules of paradigm linkage applying to a noun are those of (14), (15)
and (17) whose coradicals and classes the noun has. The universal default (5) is not among
them: it is the root that `Linkage.ofRules` falls back on. -/
def rulesFor (e : Entry) : List CellRule :=
  (rule14 e).toList ++ (rule15 e).toList ++ (rule17 e).toList

/-- `czRules l` are the rules of paradigm linkage of the noun `l`. -/
def czRules (l : CzNoun) : List CellRule := rulesFor (entry l)

/-- `czRoot l` is the root of `l`, the stem that rule (5), the universal default rule of
paradigm linkage (p. 286), gives every cell that none of the rules of `l` reaches. -/
def czRoot (l : CzNoun) : Stem := (entry l).root

/-- The stem of a cell's form correspondent is the one Pāṇini's principle selects, that of an
applicable rule no applicable rule is narrower than, or the root where no rule applies. -/
def stemFor (l : CzNoun) (σ : CzCell) : Stem :=
  Exponence.RuleSet.realizeMinimalD (czRules l) (·.dom) (fun _ ↦ czRoot l) σ

@[simp] theorem entry_lexeme (l : CzNoun) : (entry l).lexeme = l := by cases l <;> rfl

theorem lexeme_stem_of_mem_rulesFor {e : Entry} {r : CellRule} (hr : r ∈ rulesFor e) :
    r.exponent.lexeme = e.lexeme := by
  simp only [rulesFor, List.mem_append, Option.mem_toList] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact e.lexeme_of_mem_hardMascCoradical hz
  · unfold rule15 at hr
    split at hr
    · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
      exact e.lexeme_of_mem_hardMascCoradical hz
    · cases hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact e.lexeme_of_mem_softMascCoradical hz

theorem stemFor_lexeme (l : CzNoun) (σ : CzCell) : (stemFor l σ).lexeme = l :=
  Exponence.RuleSet.realizeMinimalD_induction (fun z ↦ z.lexeme = l) (entry_lexeme l)
    fun _ hr ↦ (lexeme_stem_of_mem_rulesFor hr).trans (entry_lexeme l)

/-! ### Realization -/

/-- The endings of a stem at a cell are the fragment's endings of its noun in the class its
declension is for the noun's animacy: the class's endings on the noun's stem, a velar stem of the
hard masculines taking the vocative singular -u (Short, p. 465; *Mluvnice češtiny*, p. 292) and a
velar stem of the hard masculines or the masculine a-stems the locative plural -ích (*Mluvnice
češtiny*, p. 292), with the noun's lexical nominative plural. -/
def Stem.classEndings (z : Stem) (σ : CzCell) : List (List String) :=
  z.lexeme.noun.endingsIn (z.decl.toClass (entry z.lexeme).animate) σ

/-- The endings of a stem at a cell in the fragment are its class endings, less the -u
alternating with -ovi, which is "restricted to roots belonging to the hard-masculine
declension" (n. 14). The restriction is Stump's, and the fact it derives is *Mluvnice
češtiny*'s: "-u mají pouze jména podtypu I.A s tzv. skloňováním tvrdým" '-u is had only by the
nouns of subtype I.A, with the so-called hard declension', and "V III. typu má D a L sg podobu
jedinou, nevariantní, a to -ovi: předsedovi, husitovi, sluhovi, rikšovi" 'in type III the dative
and locative singular have a single, non-variant form, -ovi' (p. 292). -/
def Stem.tableEndings (z : Stem) (σ : CzCell) : Finset (List String) :=
  let ends := (z.classEndings σ).toFinset
  if ¬ z.IsRoot ∧ ["o", "v", "i"] ∈ ends then ends.erase ["u"] else ends

/-- `nomVocPl` is the set of nominative and vocative plural cells. -/
def nomVocPl : Finset CzCell := {σ | σ.number = .plural ∧ (σ.case = .nom ∨ σ.case = .voc)}

/-- The nominative and vocative plural endings of a noun of the masculine a-declension, read from
its own class. PŘEDSEDA and SLUHA take their plural on the hard-masculine coradical, whose class
gives *chlapi*'s -i (Short, Table 9.2), but their class gives *hrdinové* (Short, Table 9.5), and
*Mluvnice češtiny* names the nouns in -a among those with one form, *předsed-ové* (p. 293). -/
def classNomPl (l : CzNoun) : Option (List (List String)) :=
  if l.noun.cls = .hrdina then some (l.noun.cls.endings (.of .nom .plural)) else none

/-- The nominative and vocative plural endings of Tables 6 and 8 that neither grammar gives:
FILOSOF's -ové. Short's tables leave out the "many formally and semantically distinctive groups
with nominative plural in -é or -ové" without placing *filosof* in one (Short, p. 466), and
*Mluvnice češtiny* gives no plural of *filozof*, its borrowed compounds in -ové being those in
-graf, -fil, -fob and -nom (p. 296). -/
def nomPlOverride : CzNoun → Option (List (List String))
  | .filosof => some [["o", "v", "é"]]
  | _ => none

/-- The nominative and vocative plural endings the study supplies beyond the fragment's endings
of the stem: those of the noun's own class, and otherwise the override. -/
def suppliedNomPl (l : CzNoun) : Option (List (List String)) := (classNomPl l).or (nomPlOverride l)

/-- The endings of a stem at a cell are those of the fragment, save at the nominative and
vocative plural of a noun whose endings there the study supplies, the vocative plural being the
nominative (Short, p. 465). -/
def Stem.endings (z : Stem) (σ : CzCell) : Finset (List String) :=
  if σ ∈ nomVocPl then ((suppliedNomPl z.lexeme).map List.toFinset).getD (z.tableEndings σ)
  else z.tableEndings σ

/-- A stem is inflected with an ending as the fragment inflects the noun's stem in the stem's
class, palatalized before the masculine locative plural -ích and the animate nominative plural
-i (*Mluvnice češtiny*, p. 279). So the soft-masculine coradical of a velar stem palatalizes
before -ích, as Short's *geolozích* (Short, p. 462) and *sluzích* (Short, p. 467) show. -/
def Stem.inflect (z : Stem) (σ : CzCell) (e : List String) : List String :=
  (z.decl.toClass (entry z.lexeme).animate).inflect z.segments σ e

/-- The form cell `⟨z, σ⟩` is realized as `z` inflected with each of its endings. -/
def czRealize (z : Stem) (σ : CzCell) : Finset (List String) := (z.endings σ).image (z.inflect σ)

/-- The realization by the fragment's endings alone, without the endings the study supplies. -/
def czRealizeTable (z : Stem) (σ : CzCell) : Finset (List String) :=
  (z.tableEndings σ).image (z.inflect σ)

/-- The Czech paradigm linkage gives each content cell the stem its rules select, and
preserves its property set. -/
def czLinkage : Linkage CzNoun Stem CzCell CzCell := Linkage.ofRules id (·.dom) czRules czRoot

theorem czRealize_stemFor : ∀ l σ, czRealize (stemFor l σ) σ = attested l σ := by
  decide +kernel

/-- The rules of paradigm linkage, with the endings of the fragment and those the study supplies,
realize every form of Tables 1, 6 and 8. -/
theorem realize_matches_tables (l : CzNoun) (σ : CzCell) :
    czLinkage.realized czRealize l σ = {(attested l σ, σ)} :=
  (Linkage.ofFun_realized _ _ czRealize l σ).trans <|
    congrArg (fun w ↦ {(w, σ)}) (czRealize_stemFor l σ)

theorem czRealizeTable_eq_czRealize {z : Stem} {σ : CzCell}
    (h : σ ∉ nomVocPl ∨ suppliedNomPl z.lexeme = none) : czRealizeTable z σ = czRealize z σ := by
  rcases h with h | h <;> simp [czRealizeTable, czRealize, Stem.endings, h]

theorem suppliedNomPl_eq_none_iff (l : CzNoun) :
    suppliedNomPl l = none ↔ l ≠ .predseda ∧ l ≠ .sluha ∧ l ≠ .filosof := by
  cases l <;> decide

/-- The fragment's endings realize every attested form except the nominative and vocative plural
-ové of PŘEDSEDA, SLUHA and FILOSOF (Tables 6 and 8). -/
theorem czRealizeTable_stemFor_iff (l : CzNoun) (σ : CzCell) :
    czRealizeTable (stemFor l σ) σ = attested l σ ↔
      σ ∉ nomVocPl ∨ l ≠ .predseda ∧ l ≠ .sluha ∧ l ≠ .filosof := by
  rw [← suppliedNomPl_eq_none_iff]
  have miss : ∀ l σ, σ ∈ nomVocPl → suppliedNomPl l ≠ none →
      czRealizeTable (stemFor l σ) σ ≠ attested l σ := by
    decide +kernel
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hc
    simp only [not_or, not_not] at hc
    exact miss l σ hc.1 hc.2 h
  · rw [czRealizeTable_eq_czRealize (by rwa [stemFor_lexeme]), czRealize_stemFor]

-- n. 14, Table 9.5, p. 467, p. 292
theorem coradical_no_u : ∀ l, (entry l).InPredsedaSubclass → ∀ σ ∈ datLocSg,
    czRealize ⟨l, .hardMasc⟩ σ = {(entry l).segments ++ ["o", "v", "i"]} := by
  decide

/-- PŘEDSEDA's paradigm, derived by rules (14) and (15), is Short's paradigm of *hrdina* on its stem
(Table 9.5). -/
theorem predseda_eq_hrdina : ∀ σ, czRealize (stemFor .predseda σ) σ =
    ((Czech.predseda.cls.endings σ).map (Czech.predseda.stem ++ ·)).toFinset := by
  decide +kernel

-- Table 9.2
theorem predseda_table_eq_hrdina_iff (σ : CzCell) : czRealizeTable (stemFor .predseda σ) σ =
    ((Czech.predseda.cls.endings σ).map (Czech.predseda.stem ++ ·)).toFinset ↔ σ ∉ nomVocPl := by
  rw [← predseda_eq_hrdina, czRealize_stemFor, czRealizeTable_stemFor_iff]
  simp

/-- SLUHA's paradigm is *hrdina*'s on its stem but in the locative plural, where rules (17) and
(18) give the palatalized *sluzích* for the table's -ech. -/
theorem sluha_eq_hrdina_iff : ∀ σ, czRealize (stemFor .sluha σ) σ =
    ((Czech.sluha.cls.endings σ).map (Czech.sluha.stem ++ ·)).toFinset ↔
      σ ≠ .of .loc .plural := by
  decide +kernel

/-- Rules (17) and (18) give SLUHA's locative plural *sluzích*, as does the hard-masculine velar
rule (Short, p. 467; *Mluvnice češtiny*, pp. 292, 300). -/
theorem sluha_locPl : czRealize (stemFor .sluha (.of .loc .plural)) (.of .loc .plural) =
      {Czech.Declension.segments "sluzích"} ∧
    czRealize ⟨.sluha, .hardMasc⟩ (.of .loc .plural) = {Czech.Declension.segments "sluzích"} := by
  decide +kernel

/-- Rules (17) and (18) give FILOLOG's locative plural *filolozích*, as does the hard-masculine
velar rule (Short, p. 462; *Mluvnice češtiny*, p. 295). -/
theorem filolog_locPl : czRealize (stemFor .filolog (.of .loc .plural)) (.of .loc .plural) =
      {Czech.Declension.segments "filolozích"} ∧
    czRealize ⟨.filolog, .hardMasc⟩ (.of .loc .plural) =
      {Czech.Declension.segments "filolozích"} := by
  decide +kernel

/-- FILOLOG's vocative singular is *filologu*, though the hard-masculine table's ending is -e
(Short, p. 465; *Mluvnice češtiny*, p. 292). -/
theorem filologu_voc :
    czRealize (stemFor .filolog (.of .voc .singular)) (.of .voc .singular) =
        {Czech.Declension.segments "filologu"} ∧
      Czech.Declension.Class.chlap.endings (.of .voc .singular) = [["e"]] := by
  decide +kernel

/-! ### Heteroclisis -/

/-- `cellClass l σ` is the declension that the cell `σ` of `l` inflects in. -/
def cellClass (l : CzNoun) (σ : CzCell) : Decl := (stemFor l σ).decl

theorem pramen_heteroclite : czLinkage.IsHeteroclite Stem.decl .pramen := by decide

/-- Exactly PRAMEN, PŘEDSEDA, SLUHA and FILOLOG are heteroclite. -/
theorem heteroclite_iff : ∀ l, czLinkage.IsHeteroclite Stem.decl l ↔
    l = .pramen ∨ l = .predseda ∨ l = .sluha ∨ l = .filolog := by
  decide +kernel

/-- Every noun's stems share their segments, so the heteroclite nouns alternate between stems
that differ in declension alone. -/
theorem segments_invariant (l : CzNoun) : czLinkage.IsInvariantAlong Stem.segments l :=
  Linkage.ofFun_isInvariantAlong_iff.mpr fun σ σ' ↦
    show (stemFor l σ).segments = (stemFor l σ').segments by
      simp only [Stem.segments, stemFor_lexeme]

/-- PRAMEN's paradigm "exhibits a kind of stem suppletion" (pp. 282–283), since its two stems,
though phonologically identical, are two stems. -/
theorem pramen_suppletive : czLinkage.IsSuppletive .pramen := pramen_heteroclite.isSuppletive

/-- Rule (14) assigns PRAMEN in each cell the class the fragment gives *kořen* in that number
(Short, p. 469; *Mluvnice češtiny*, p. 310). -/
theorem pramen_eq_koren_pattern :
    ∀ σ, (cellClass .pramen σ).toClass (entry .pramen).animate = Czech.koren.clsAt σ.number := by
  decide

/-! ### The degree of correlation -/

section Correlation

variable {C V K : Type*} [Fintype C] [Fintype V] [Fintype K] [DecidableEq V] [DecidableEq K]

/-- `degreeNum A cls` is the numerator of the degree of `A`-correlation (p. 309), the sum over
the values `v` of `A` of "the largest number of cells in P that carry the specification v and
inflect as members of the same inflection class". -/
def degreeNum (A : C → V) (cls : C → K) : ℕ :=
  ∑ v, univ.sup fun k ↦ #{σ | A σ = v ∧ cls σ = k}

omit [Fintype V] in
private theorem sup_card_le_card_fiber (A : C → V) (cls : C → K) (v : V) :
    univ.sup (fun k ↦ #{σ | A σ = v ∧ cls σ = k}) ≤ #{σ | A σ = v} :=
  Finset.sup_le fun _ _ ↦ card_le_card fun σ ↦ by simp +contextual

theorem degreeNum_le_card (A : C → V) (cls : C → K) : degreeNum A cls ≤ Fintype.card C := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := A) (t := univ) (by simp)]
  exact sum_le_sum fun v _ ↦ sup_card_le_card_fiber A cls v

/-- The count is the number of cells exactly when the class split factors through the
category. -/
theorem degreeNum_eq_card_iff (A : C → V) (cls : C → K) :
    degreeNum A cls = Fintype.card C ↔ cls.FactorsThrough A := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := A) (t := univ) (by simp), degreeNum,
    sum_eq_sum_iff_of_le fun v _ ↦ sup_card_le_card_fiber A cls v]
  constructor
  · intro h σ τ hστ
    obtain ⟨k, -, hk⟩ := exists_mem_eq_sup univ ⟨cls σ, mem_univ _⟩
      fun k ↦ #{σ' | A σ' = A σ ∧ cls σ' = k}
    have hcard := h (A σ) (mem_univ _)
    rw [hk] at hcard
    have hsub := eq_of_subset_of_card_le (s := {σ' | A σ' = A σ ∧ cls σ' = k})
      (t := {σ' | A σ' = A σ}) (fun x ↦ by simp +contextual) hcard.ge
    have h₁ : σ ∈ ({σ' | A σ' = A σ ∧ cls σ' = k} : Finset C) := hsub ▸ by simp
    have h₂ : τ ∈ ({σ' | A σ' = A σ ∧ cls σ' = k} : Finset C) := hsub ▸ by simp [hστ]
    rw [(by simpa using h₁ : cls σ = k), (by simpa [hστ] using h₂ : cls τ = k)]
  · intro h v _
    refine le_antisymm (sup_card_le_card_fiber A cls v) ?_
    rcases ({σ | A σ = v} : Finset C).eq_empty_or_nonempty with he | ⟨σ, hσ⟩
    · simp [he]
    · refine le_trans (le_of_eq ?_) (le_sup (mem_univ (cls σ)))
      congr 1
      ext τ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      exact ⟨fun hτ ↦ ⟨hτ, h (hτ.trans hσ.symm)⟩, And.left⟩

/-- The degree of `A`-correlation (p. 309) is the count over the number of cells. -/
def degree (A : C → V) (cls : C → K) : ℚ := degreeNum A cls / Fintype.card C

theorem degree_eq_one_iff [Nonempty C] {A : C → V} {cls : C → K} :
    degree A cls = 1 ↔ cls.FactorsThrough A := by
  rw [degree, div_eq_one_iff_eq (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_inj,
    degreeNum_eq_card_iff]

end Correlation

/-! ### Correlates of heteroclisis

The paper's classification of heteroclite paradigms applies to any cells pairing a case in `A`
with a number in `B`, and to any class map `cls` giving the inflection class of each cell. -/

section Correlates

variable {A B K L E : Type*}

/-- The inflectional categories of a noun are number and case. -/
inductive Category
  | number
  | case
  deriving DecidableEq, Fintype, Repr

/-- `c.proj σ` is the value of the category `c` at the cell `σ`. -/
def Category.proj : Category → A × B → A ⊕ B
  | .number, σ => .inr σ.2
  | .case, σ => .inl σ.1

/-- `c.other` is the category other than `c`. -/
def Category.other : Category → Category
  | .number => .case
  | .case => .number

@[simp] theorem Category.other_other (c : Category) : c.other.other = c := by cases c <;> rfl

/-- A category is an absolute correlate of a paradigm's heteroclisis "if and only if the degree
of A-correlation in that paradigm is 1.0" (p. 309), that is, when the paradigm's class split
factors through the category. -/
def IsAbsoluteCorrelate (c : Category) (cls : A × B → K) : Prop := cls.FactorsThrough c.proj

/-- A paradigm is cloven when it is heteroclite, two of its cells inflecting in distinct
classes, and has an absolute correlate (p. 309). -/
def IsCloven (cls : A × B → K) : Prop :=
  (∃ σ τ, cls σ ≠ cls τ) ∧ ∃ c, IsAbsoluteCorrelate c cls

/-- A paradigm is fractured when it is heteroclite, two of its cells inflecting in distinct
classes, and lacks any absolute correlate (p. 309). -/
def IsFractured (cls : A × B → K) : Prop :=
  (∃ σ τ, cls σ ≠ cls τ) ∧ ∀ c, ¬ IsAbsoluteCorrelate c cls

theorem cellClass_eq_of_isAbsoluteCorrelate {cls : A × B → K}
    (hn : IsAbsoluteCorrelate .number cls) (hc : IsAbsoluteCorrelate .case cls) (σ τ : A × B) :
    cls σ = cls τ :=
  (hc (a := σ) (b := (σ.1, τ.2)) rfl).trans (hn rfl)

/-- `projOn S σ` records the values at `σ` of the categories in `S`. -/
def projOn (S : Finset Category) (σ : A × B) : Option A × Option B :=
  (if .case ∈ S then some σ.1 else none, if .number ∈ S then some σ.2 else none)

/-- Categories are intersective correlates of a paradigm's heteroclisis when "for each
well-formed property set τ specified for exactly the categories A₁, . . . , A_n there is a
single inflection class C such that every cell in P realizing τ inflects as a member of C"
(p. 313). -/
def IsIntersectiveCorrelate (cls : A × B → K) (S : Finset Category) : Prop :=
  cls.FactorsThrough (projOn S)

theorem projOn_eq_of_subset {S T : Finset Category} (hST : S ⊆ T) {σ τ : A × B}
    (h : projOn T σ = projOn T τ) : projOn S σ = projOn S τ := by
  simp only [projOn, Prod.mk.injEq] at h ⊢
  refine ⟨?_, ?_⟩
  · by_cases hc : Category.case ∈ S
    · simpa [hc, hST hc] using h.1
    · simp [hc]
  · by_cases hn : Category.number ∈ S
    · simpa [hn, hST hn] using h.2
    · simp [hn]

theorem IsIntersectiveCorrelate.mono {cls : A × B → K} {S T : Finset Category}
    (h : IsIntersectiveCorrelate cls S) (hST : S ⊆ T) : IsIntersectiveCorrelate cls T :=
  fun _ _ hστ ↦ h (projOn_eq_of_subset hST hστ)

theorem isIntersectiveCorrelate_singleton_iff {cls : A × B → K} {c : Category} :
    IsIntersectiveCorrelate cls {c} ↔ IsAbsoluteCorrelate c cls := by
  have key : ∀ σ τ : A × B, projOn {c} σ = projOn {c} τ ↔ c.proj σ = c.proj τ := by
    intro σ τ; cases c <;> simp [projOn, Category.proj]
  exact ⟨fun h _ _ hστ ↦ h ((key _ _).mpr hστ), fun h _ _ hστ ↦ h ((key _ _).mp hστ)⟩

theorem isIntersectiveCorrelate_univ (cls : A × B → K) : IsIntersectiveCorrelate cls univ :=
  fun σ τ h ↦ by
    simp only [projOn, mem_univ, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at h
    rw [Prod.ext h.1 h.2]

theorem minimal_univ_of_isFractured {cls : A × B → K} (h : IsFractured cls) :
    Minimal (IsIntersectiveCorrelate cls) univ := by
  refine ⟨isIntersectiveCorrelate_univ cls, fun S hS _ ↦ ?_⟩
  by_contra hne
  obtain ⟨c, -, hc⟩ := not_subset.mp hne
  refine h.2 c.other (isIntersectiveCorrelate_singleton_iff.mp (hS.mono fun x hx ↦ ?_))
  exact mem_singleton.mpr (by cases x <;> cases c <;> first | rfl | exact absurd hx hc)

/-- A rule is sensitive to the value of a category when its applicability does not factor
through the other category. -/
def SensitiveTo (r : Exponence.DomainRule (A × B) E) (c : Category) : Prop :=
  ¬ (Exponence.Applies r).FactorsThrough c.other.proj

/-- A category is privileged for a family `cls` of class maps, one for each lexeme, when it
serves as an absolute correlate of a cloven paradigm: "the inflectional categories serving as
absolute correlates of heteroclisis in a given language are PRIVILEGED" (p. 315). -/
def Privileged (cls : L → A × B → K) (c : Category) : Prop :=
  ∃ l, IsCloven (cls l) ∧ IsAbsoluteCorrelate c (cls l)

/-- A system of rules satisfies the privileged category restriction (40) (p. 316), which reads
"If a rule of paradigm linkage applies to lexemes belonging to a privileged syntactic category C
and this rule is sensitive to the value of any inflectional category, then it is sensitive to
the value of a privileged inflectional category for members of C." The lexemes `L` are taken to
form one privileged syntactic category, so the antecedent on the syntactic category is left
implicit. -/
def SatisfiesPCR (cls : L → A × B → K)
    (rules : L → Exponence.RuleSet (Exponence.DomainRule (A × B) E)) : Prop :=
  ∀ l, ∀ r ∈ rules l, (∃ c, SensitiveTo r c) → ∃ c, Privileged cls c ∧ SensitiveTo r c

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A category is a maximal correlate when its degree "is higher than any other inflectional
category's degree of correlation in that paradigm" (p. 309). -/
def IsMaximalCorrelate [Fintype K] [DecidableEq K] (c : Category) (cls : A × B → K) : Prop :=
  ∀ c' ≠ c, degreeNum c'.proj cls < degreeNum c.proj cls

theorem isAbsoluteCorrelate_iff_degree [Fintype K] [DecidableEq K] [Nonempty (A × B)]
    {c : Category} {cls : A × B → K} : IsAbsoluteCorrelate c cls ↔ degree c.proj cls = 1 :=
  degree_eq_one_iff.symm

theorem IsAbsoluteCorrelate.isMaximalCorrelate [Fintype K] [DecidableEq K] {c : Category}
    {cls : A × B → K} (hl : ∃ σ τ, cls σ ≠ cls τ) (h : IsAbsoluteCorrelate c cls) :
    IsMaximalCorrelate c cls := by
  intro c' hc'
  rw [(degreeNum_eq_card_iff _ _).mpr h]
  refine (degreeNum_le_card _ _).lt_of_ne fun hEq ↦ ?_
  have h' : IsAbsoluteCorrelate c' cls := (degreeNum_eq_card_iff _ _).mp hEq
  obtain ⟨σ, τ, hne⟩ := hl
  apply hne
  cases c <;> cases c'
  · exact absurd rfl hc'
  · exact cellClass_eq_of_isAbsoluteCorrelate h h' σ τ
  · exact cellClass_eq_of_isAbsoluteCorrelate h' h σ τ
  · exact absurd rfl hc'

variable [DecidableEq K]

instance (c : Category) (cls : A × B → K) : Decidable (IsAbsoluteCorrelate c cls) :=
  inferInstanceAs (Decidable (∀ σ τ, c.proj σ = c.proj τ → cls σ = cls τ))

instance [Fintype K] (c : Category) (cls : A × B → K) : Decidable (IsMaximalCorrelate c cls) :=
  inferInstanceAs (Decidable (∀ _, _ → _))

instance (cls : A × B → K) : Decidable (IsCloven cls) := inferInstanceAs (Decidable (_ ∧ _))

instance (cls : A × B → K) : Decidable (IsFractured cls) := inferInstanceAs (Decidable (_ ∧ _))

instance (r : Exponence.DomainRule (A × B) E) (c : Category) : Decidable (SensitiveTo r c) :=
  inferInstanceAs (Decidable (¬ _))

instance [Fintype L] (cls : L → A × B → K) (c : Category) : Decidable (Privileged cls c) :=
  inferInstanceAs (Decidable (∃ _, _))

instance [Fintype L] (cls : L → A × B → K)
    (rules : L → Exponence.RuleSet (Exponence.DomainRule (A × B) E)) :
    Decidable (SatisfiesPCR cls rules) :=
  have (r : Exponence.DomainRule (A × B) E) :
      Decidable ((∃ c, SensitiveTo r c) → ∃ c, Privileged cls c ∧ SensitiveTo r c) :=
    inferInstance
  inferInstanceAs (Decidable (∀ _, _))

end Correlates

/-! ### Correlates of Czech heteroclisis -/

/-- PRAMEN's degree of number correlation is 14/14 and its degree of case correlation .50. -/
theorem pramen_degrees : degree Category.number.proj (cellClass .pramen) = 1 ∧
    degree Category.case.proj (cellClass .pramen) = 1 / 2 := by
  decide +kernel

/-- PŘEDSEDA's degree of number correlation is .86 (= 12/14) and its degree of case
correlation .64. -/
theorem predseda_degrees : degree Category.number.proj (cellClass .predseda) = 6 / 7 ∧
    degree Category.case.proj (cellClass .predseda) = 9 / 14 := by
  decide +kernel

/-- SLUHA's degree of number correlation is .79 (= 11/14) and its degree of case correlation
.57. -/
theorem sluha_degrees : degree Category.number.proj (cellClass .sluha) = 11 / 14 ∧
    degree Category.case.proj (cellClass .sluha) = 4 / 7 := by
  decide +kernel

/-- FILOLOG's degrees of number and of case correlation are both .93 (= 13/14) (p. 313). -/
theorem filolog_degrees : degree Category.number.proj (cellClass .filolog) = 13 / 14 ∧
    degree Category.case.proj (cellClass .filolog) = 13 / 14 := by
  decide +kernel

theorem pramen_cloven : IsCloven (cellClass .pramen) := by decide

theorem predseda_fractured : IsFractured (cellClass .predseda) := by decide

theorem sluha_fractured : IsFractured (cellClass .sluha) := by decide

theorem filolog_fractured : IsFractured (cellClass .filolog) := by decide

-- (38), p. 312
theorem number_maximal_predseda_sluha :
    IsMaximalCorrelate .number (cellClass .predseda) ∧
      IsMaximalCorrelate .number (cellClass .sluha) := by
  decide

-- (38), p. 313
theorem filolog_no_maximal : ∀ c, ¬ IsMaximalCorrelate c (cellClass .filolog) := by decide

/-! ### Rules sensitive to a category -/

/-- If every rule's applicability factors through `A`, so does the noun's class split ((41a), p.
317). -/
theorem isAbsoluteCorrelate_of_rules {V : Type*} (l : CzNoun) (A : CzCell → V)
    (h : ∀ r ∈ czRules l, (Exponence.Applies r).FactorsThrough A) :
    (fun σ ↦ (stemFor l σ).decl).FactorsThrough A :=
  (Exponence.RuleSet.realizeMinimalD_factorsThrough (fun _ _ _ ↦ rfl) fun r hr _ _ hA ↦
    Iff.of_eq (h r hr hA)).comp_left Stem.decl

theorem isAbsoluteCorrelate_of_forall_not_sensitiveTo {c : Category} {l : CzNoun}
    (h : ∀ r ∈ czRules l, ¬ SensitiveTo r c.other) : IsAbsoluteCorrelate c (cellClass l) :=
  isAbsoluteCorrelate_of_rules _ _ fun r hr ↦ by simpa [SensitiveTo] using h r hr

-- (14), (5)
theorem pramen_number_absolute : IsAbsoluteCorrelate .number (cellClass .pramen) :=
  isAbsoluteCorrelate_of_forall_not_sensitiveTo (by decide)

theorem number_maximal_pramen : IsMaximalCorrelate .number (cellClass .pramen) :=
  pramen_number_absolute.isMaximalCorrelate pramen_cloven.1

/-! ### The privileged category restriction -/

theorem privileged_number : Privileged cellClass .number :=
  ⟨.pramen, pramen_cloven, pramen_number_absolute⟩

-- p. 316
theorem not_privileged_case : ¬ Privileged cellClass .case := by decide +kernel

/-- The Czech rules (14), (15) and (17) satisfy (40) (p. 316). -/
theorem pcr : SatisfiesPCR cellClass czRules := by decide +kernel

/-- `genitive` is the set of genitive cells. -/
def genitive : Finset CzCell := {σ | σ.case = .gen}

/-- A hypothetical system adds to the Czech rules one giving the genitive cells of the
PŘEDSEDA subclass the hard-masculine coradical, a rule sensitive to case alone. It is modelled
on the paper's hypothetical (41) and Table 26, whose type-II rule is sensitive to tense and
person but not number; it leaves PRAMEN, and so the privilege of number, untouched. -/
def hypothetical (e : Entry) : List CellRule :=
  rulesFor e ++
    (if e.InPredsedaSubclass then (e.hardMascCoradical.map (⟨genitive, ·⟩)).toList else [])

/-- The hypothetical system violates (40), so the restriction is not vacuous. -/
theorem not_satisfiesPCR_hypothetical : ¬ SatisfiesPCR cellClass (hypothetical ∘ entry) := by
  decide +kernel

/-- Every fractured Czech paradigm has a privileged category among its minimal intersective
correlates, as Claim (39) states (p. 313). -/
theorem fractured_minimal_intersective_privileged {l : CzNoun}
    (h : IsFractured (cellClass l)) :
    ∃ S, Minimal (IsIntersectiveCorrelate (cellClass l)) S ∧ ∃ c ∈ S, Privileged cellClass c :=
  ⟨univ, minimal_univ_of_isFractured h, .number, mem_univ _, privileged_number⟩

/-! ### Sanskrit cells, stems and form property sets -/

/-- The Sanskrit cases are the nominative, vocative, accusative, instrumental, dative, ablative,
genitive and locative. -/
abbrev SktCase : Finset Case := {.nom, .voc, .acc, .inst, .dat, .abl, .gen, .loc}

/-- The Sanskrit numbers are the singular, the dual and the plural. -/
abbrev SktNumber : Finset Number := {.singular, .dual, .plural}

/-- A Sanskrit content cell pairs a case with a number, gender being constant within a
paradigm. -/
abbrev SktCell : Type := SktCase × SktNumber

/-- `SktCell.of c n` is the cell of case `c` and number `n`. -/
def SktCell.of (c : Case) (n : Number) (hc : c ∈ SktCase := by decide)
    (hn : n ∈ SktNumber := by decide) : SktCell :=
  (⟨c, hc⟩, ⟨n, hn⟩)

instance : Nonempty SktCell := ⟨.of .nom .singular⟩

/-- The genders of the Sanskrit paradigms considered are the masculine and the neuter. -/
inductive SktGender
  | masc
  | neut
  deriving DecidableEq, Fintype, Repr

/-- `g.ud` is the gender `g` in the forms data. -/
def SktGender.ud : SktGender → UD.Gender
  | .masc => .Masc
  | .neut => .Neut

/-- The Sanskrit declensions considered are the neuter a-stem declension of HṚD(AYA)'s *hṛdaya*
(Table 4), the general consonant-stem declension, followed by HṚD(AYA)'s *hṛd* and by every stem
of PRATYAÑC (Table 9), and the neuter an-stem and neuter as-stem declensions (Table 10). -/
inductive SktDecl
  | aStem
  | consStem
  | anStem
  | asStem
  deriving DecidableEq, Fintype, Repr

/-- A stem is individuated, as in the paper, by its form and the declension it inflects in. -/
structure SktStem where
  /-- `form` is the form of the stem. -/
  form : String
  /-- `decl` is the declension the stem inflects in. -/
  decl : SktDecl
  deriving DecidableEq, Repr

/-- A form case is a case or the property [nominative ∨ accusative] that the operator ∨ joins,
"such that any rule realizing p or p′ also realizes [p ∨ p′]" (p. 286). -/
inductive SktFormCase
  | plain (c : SktCase)
  | nomAcc
  deriving DecidableEq

/-- A form property set pairs a form case with a number. It omits gender, which is lexical for
the lexemes considered. -/
abbrev SktForm : Type := SktFormCase × SktNumber

/-- `ι σ` is the form property set specified exactly as the content property set `σ`. -/
def ι (σ : SktCell) : SktForm := (.plain σ.1, σ.2)

theorem ι_injective : Function.Injective ι := fun σ τ h ↦ by
  simp only [ι, Prod.mk.injEq, SktFormCase.plain.injEq] at h
  exact Prod.ext h.1 h.2

/-- The property mapping `f₁ g` of a lexeme of gender `g` is (10) (p. 288), which reads "Where α
is any gender and β is any oblique case: (i) if σ = {neut nom X} or {neut acc X}, then
f₁(σ) = {neut [nom ∨ acc] X}; (ii) if σ = {α β X}, then f₁(σ) = {β X}; (iii) otherwise
f₁(σ) = σ." Gender being lexical here and absent from form property sets, clause (ii) is
vacuous. -/
def f₁ : SktGender → SktCell → SktForm
  | .masc, σ => ι σ
  | .neut, σ => if σ.1.1 = .nom ∨ σ.1.1 = .acc then (.nomAcc, σ.2) else ι σ

/-! ### Sanskrit HṚD(AYA) (Table 4) -/

/-- HṚD(AYA) 'heart' is the Sanskrit noun of Table 4. -/
inductive SktNoun
  | hrdaya
  deriving DecidableEq, Fintype, Repr

/-- The direct cases are the nominative, vocative and accusative. -/
abbrev direct : Finset Case := {.nom, .voc, .acc}

/-- `hrdStem σ` is the stem of the cell `σ`, since "the direct ... case forms of HṚD(AYA) are
built on the stem hṛdaya, while its remaining, oblique case forms are built on the stem hṛd"
(p. 282). Its stems' declensions follow their final segments, for "because hṛdaya is a neuter
stem ending in a, it follows the neuter a-stem declension ..., but because hṛd is a neuter stem
ending in a consonant, it instead follows the neuter consonant-stem declension" (p. 282). -/
def hrdStem (σ : SktCell) : SktStem :=
  if σ.1.1 ∈ direct then ⟨"hṛdaya", .aStem⟩ else ⟨"hṛd", .consStem⟩

/-- `hrdLinkage` is the paradigm linkage of HṚD(AYA), whose stem alternation "is not the effect
of any regular rule of inflectional exponence, but is instead simply stipulated in HṚD(AYA)'s
lexical entry" (p. 282). HṚD(AYA) is neuter, and its property sets map by `f₁`. -/
def hrdLinkage : Linkage SktNoun SktStem SktCell SktForm where
  realize _ σ := {hrdStem σ}
  pm _ := f₁ .neut

/-- `hrdClass σ` is the declension that the cell `σ` of HṚD(AYA) inflects in. -/
def hrdClass (σ : SktCell) : SktDecl := (hrdStem σ).decl

theorem hrd_heteroclite : hrdLinkage.IsHeteroclite SktStem.decl .hrdaya := by decide

/-- HṚD(AYA)'s stems also differ in form, its heteroclisis being an effect of stem suppletion,
unlike PRAMEN's (`segments_invariant`). -/
theorem hrd_form_suppletive : hrdLinkage.IsHeteroclite SktStem.form .hrdaya := by decide

/-- HṚD(AYA)'s paradigm is cloven (p. 313), with case as its absolute correlate (p. 310). -/
theorem hrd_cloven : IsCloven hrdClass ∧ IsAbsoluteCorrelate .case hrdClass := by decide

/-! ### Sanskrit stem grades (§3.2)

"In instances of morphosyntactically conditioned heteroclisis, the choice of inflection class in
the realization of a paradigm's individual cells is directly determined by the morphosyntactic
property sets expressed by those cells; in instances of morphologically conditioned
heteroclisis, the choice of inflection class in the realization of a paradigm's individual cells
is instead determined by an independently observable pattern of stem alternation" (p. 293).
PRAMEN's is of the first sort. In Sanskrit, rules (20a,b) give each cell of an alternating
nominal its Strong, Middle or Weakest stem by the strength (19) of its property set and by the
ending that follows; they make PRATYAÑC 'westerly' alternate among stems of one declension and
AHAN 'day' among stems of two. -/

/-- The grades of an alternating Sanskrit stem are the Strong, the Middle and the Weakest. -/
inductive Grade
  | strong
  | middle
  | weakest
  deriving DecidableEq, Fintype, Repr

/-- A property set is strong or weak, as (19) defines. -/
inductive Strength
  | strong
  | weak
  deriving DecidableEq, Repr

/-- Clause (19a) makes strong the direct-case property sets of a masculine and the direct-case
plural ones of a neuter. -/
def rule19a (g : SktGender) : Exponence.DomainRule SktCell Strength :=
  ⟨{σ | σ.1.1 ∈ direct ∧ (g = .masc ∨ σ.2.1 = .plural)}, .strong⟩

/-- Clause (19b) makes weak the accusative plural property set of a masculine. -/
def rule19b (g : SktGender) : Exponence.DomainRule SktCell Strength :=
  ⟨{σ | g = .masc ∧ σ.1.1 = .acc ∧ σ.2.1 = .plural}, .weak⟩

-- (19b), (19a), n. 19
theorem rule19b_lt_rule19a : (rule19b .masc).dom ⊂ (rule19a .masc).dom := by decide

/-- The strength of a property set is given by (19) (p. 294), which reads "Where α is masculine
or feminine, β is any direct case (nominative, vocative, or accusative), and γ is any number
(singular, dual, or plural), a. instances of {α β γ} and {neuter β plural} are strong by
default; b. but instances of {α accusative plural} are weak; in addition, c. any
gender/case/number combination that is not strong according to (a) is weak." Clause (19b)
overrides (19a) by Pāṇini's principle, and (19c) is the default. -/
def strength (g : SktGender) (σ : SktCell) : Strength :=
  Exponence.RuleSet.realizeMinimalD [rule19a g, rule19b g] (·.dom) (fun _ ↦ .weak) σ

/-- `weak g` is the set of weak property sets of a lexeme of gender `g`. -/
def weak (g : SktGender) : Finset SktCell := {σ | strength g σ = .weak}

/-- A Sanskrit row expresses the concept `pid` in the gender `g` at the cell `σ`. -/
def SktRow (pid : String) (g : SktGender) (σ : SktCell) (f : Form Wordlist.Cell) : Bool :=
  f.languageId == "sans1269" && f.parameterId == pid && f.cell.gender = ↑g.ud &&
    caseOfForm f == some σ.1.1 && numberOfForm f == some σ.2.1

/-- `sktRows pid g σ` are the Sanskrit rows expressing the concept `pid` in the gender `g` at the
cell `σ`, those of Tables 9 and 10. -/
def sktRows (pid : String) (g : SktGender) (σ : SktCell) : List (Form Wordlist.Cell) :=
  Wordlist.all.filter (SktRow pid g σ)

/-- The ending of a row is what follows its stem alternant, nothing for a bare stem. -/
def endingOf (f : Form Wordlist.Cell) : List String := f.segments.drop 1

/-- `d.exemplar` is the concept whose rows exemplify the declension `d`, PRATYAÑC 'westerly' for
the general consonant-stem declension and, for the neuter an-stem and as-stem declensions, NĀMAN
'name' and MANAS 'mind', which Table 10 sets beside AHAN. The tables print no a-stem paradigm. -/
def SktDecl.exemplar : SktDecl → Option String
  | .aStem => none
  | .consStem => some "westerly"
  | .anStem => some "name"
  | .asStem => some "mind"

/-- The row realizing a form case is that of the case itself, or of the nominative for the join
[nominative ∨ accusative], the accusative row agreeing with it (`sktEndings_nomAcc`). -/
def SktFormCase.rowCase : SktFormCase → SktCase
  | .plain c => c
  | .nomAcc => ⟨.nom, by decide⟩

/-- `sktEndings d g τ` are the endings of the declension `d` for the gender `g` at the form property
set `τ`, those of its exemplar's row. -/
def sktEndings (d : SktDecl) (g : SktGender) (τ : SktForm) : List (List String) :=
  match d.exemplar with
  | some pid => (sktRows pid g (τ.1.rowCase, τ.2)).map endingOf
  | none => []

theorem sktEndings_nomAcc : ∀ d (n : SktNumber),
    sktEndings d .neut (.nomAcc, n) = sktEndings d .neut (.plain ⟨.acc, by decide⟩, n) := by decide

/-- `sktVowels` are the vowels of Sanskrit. -/
def sktVowels : List String := ["a", "ā", "i", "ī", "u", "ū", "ṛ", "ṝ", "ḷ", "e", "ai", "o", "au"]

/-- An ending is vowel-initial when its first segment begins with a vowel. -/
def VowelInitial (e : List String) : Prop :=
  ∃ s ∈ e.head?, ∃ v ∈ sktVowels, v.toList <+: s.toList

instance : DecidablePred VowelInitial := fun _ ↦ inferInstanceAs (Decidable (∃ s ∈ _, _))

/-- The lexemes of §3.2 are the adjective PRATYAÑC 'westerly' and the noun AHAN 'day'.
PRATYAÑC's masculine and neuter paradigms (Table 9) are indexed separately, gender being lexical
for the nouns that share their cells. -/
inductive SktLex
  | pratyancM
  | pratyancN
  | ahan
  deriving DecidableEq, Fintype, Repr

/-- A lexical entry records a lexeme's gender, its root, the Strong stem, and whichever of a
Middle and a Weakest coradical it has, for "some alternating nominals possess only two stems: a
Strong stem and a single Weak stem. Others have a Strong stem and two Weak stems" (p. 293). -/
structure SktEntry where
  /-- `gender` is the lexeme's gender. -/
  gender : SktGender
  /-- `root` is the lexeme's Strong stem. -/
  root : SktStem
  /-- `middle` is the lexeme's Middle coradical, if it has one. -/
  middle : Option SktStem
  /-- `weakest` is the lexeme's Weakest coradical, if it has one. -/
  weakest : Option SktStem
  deriving DecidableEq, Repr

/-- `sktEntry l` is the lexical entry of `l`. PRATYAÑC's root is its Strong stem *pratyañc*, and
*pratyac* and *pratīc* are its Middle and Weakest coradicals, all three following "the general
consonant-stem declension" (p. 294). For AHAN, "ahan is identified as AHAN's root (= its Strong
stem), ahas as its Middle coradical, and ahn as its Weakest coradical", where "ahan and its
zero-grade counterpart ahn inflect according to the neuter an-stem declension, while ahas
inflects according to the neuter as-stem declension" (p. 295). -/
def sktEntry : SktLex → SktEntry
  | .pratyancM => ⟨.masc, ⟨"pratyañc", .consStem⟩, some ⟨"pratyac", .consStem⟩,
      some ⟨"pratīc", .consStem⟩⟩
  | .pratyancN => ⟨.neut, ⟨"pratyañc", .consStem⟩, some ⟨"pratyac", .consStem⟩,
      some ⟨"pratīc", .consStem⟩⟩
  | .ahan => ⟨.neut, ⟨"ahan", .anStem⟩, some ⟨"ahas", .asStem⟩, some ⟨"ahn", .anStem⟩⟩

/-- The stems of an entry are its root and its coradicals. -/
def SktEntry.stems (e : SktEntry) : List SktStem := e.root :: (e.middle.toList ++ e.weakest.toList)

/-- A Sanskrit rule of paradigm linkage gives the cells of its domain form correspondents built on
its exponent, a stem. -/
abbrev SktRule : Type := Exponence.DomainRule SktCell SktStem

/-- Rule (20a) (p. 294) reads "Where L is a nominal lexeme having s_w as its Weakest coradical and
σ is a weak property set, if the realization of the form-cell ⟨s_w, f₁(σ)⟩ is s_w[vowel]X, then
the content-cell ⟨L, σ⟩ has ⟨s_w, f₁(σ)⟩ as its form-correspondent." Its domain is read off the
endings of s_w's declension rather than listed. -/
def rule20a (e : SktEntry) : Option SktRule :=
  e.weakest.map fun z : SktStem ↦
    ⟨{σ ∈ weak e.gender | ∃ w ∈ sktEndings z.decl e.gender (f₁ e.gender σ), VowelInitial w}, z⟩

/-- Rule (20b) (p. 294) reads "If L is a nominal lexeme having s_m as its Middle coradical and σ
is a weak property set, then the content-cell ⟨L, σ⟩ has ⟨s_m, f₁(σ)⟩ as its
form-correspondent." -/
def rule20b (e : SktEntry) : Option SktRule := e.middle.map (⟨weak e.gender, ·⟩)

/-- The rules (20a,b) that apply to a lexeme are those whose coradicals it has. The Sanskrit
default (12) is not among them: it is the root that `Exponence.RuleSet.realizeMinimalD` falls
back on. -/
def sktRulesFor (e : SktEntry) : List SktRule := (rule20a e).toList ++ (rule20b e).toList

/-- `sktRules l` are the rules of paradigm linkage of the lexeme `l`. -/
def sktRules (l : SktLex) : List SktRule := sktRulesFor (sktEntry l)

/-- `sktRoot l` is the root of `l`, the stem that the Sanskrit rule of paradigm linkage (12)
(p. 289) gives every cell that no rule of `l` reaches: "Where L is a nominal lexeme having r as
its root, the content-cell ⟨L, σ⟩ has ⟨r, f₁(σ)⟩ as its form-correspondent." -/
def sktRoot (l : SktLex) : SktStem := (sktEntry l).root

/-- The stem of a cell is the one Pāṇini's principle selects, by which "20a will, as the
narrower of the two rules, override 20b in any instance in which the former rule is applicable"
(p. 295). -/
def sktStem (l : SktLex) (σ : SktCell) : SktStem :=
  Exponence.RuleSet.realizeMinimalD (sktRules l) (·.dom) (fun _ ↦ sktRoot l) σ

/-- The Sanskrit paradigm linkage gives each content cell the stem its rules select, with the
form property set that `f₁` maps its property set to. -/
def sktLinkage : Linkage SktLex SktStem SktCell SktForm where
  realize l σ := {sktStem l σ}
  pm l := f₁ (sktEntry l).gender

/-- The grade of a stem in an entry is weakest for its Weakest coradical, middle for its Middle
coradical, and strong for its root. -/
def SktEntry.gradeOf (e : SktEntry) (z : SktStem) : Grade :=
  if e.weakest = some z then .weakest else if e.middle = some z then .middle else .strong

/-- `grade l σ` is the grade of the stem that the rules select at the cell `σ` of `l`. -/
def grade (l : SktLex) (σ : SktCell) : Grade := (sktEntry l).gradeOf (sktStem l σ)

/-- `sktClass l σ` is the declension that the cell `σ` of `l` inflects in. -/
def sktClass (l : SktLex) (σ : SktCell) : SktDecl := (sktStem l σ).decl

/-! ### The rules against Tables 9 and 10 -/

/-- `l.paramId` is the concept that the forms of `l` express in the forms data. -/
def SktLex.paramId : SktLex → String
  | .pratyancM | .pratyancN => "westerly"
  | .ahan => "day"

/-- `l.analyses σ` are the paper's analyses of the rows of the forms data for the cell `σ` of
`l`. -/
def SktLex.analyses (l : SktLex) (σ : SktCell) : List Wordlist.Analysis :=
  Wordlist.analyses.filter (SktRow l.paramId (sktEntry l).gender σ ·.form)

/-- `gradeOf g` reads a grade of the paper's analysis as a grade. -/
def gradeOf : Wordlist.Grade → Grade
  | .strong => .strong
  | .middle => .middle
  | .weakest => .weakest

-- (20a)
theorem sktEndings_length : ∀ l σ, ∀ z ∈ (sktEntry l).weakest,
    (sktEndings z.decl (sktEntry l).gender (f₁ (sktEntry l).gender σ)).length = 1 := by decide

-- (20a), (20b), p. 295
theorem rule20a_lt_rule20b : ∀ l, ∀ a ∈ rule20a (sktEntry l), ∀ b ∈ rule20b (sktEntry l),
    a.dom ⊂ b.dom := by decide

/-- Rules (19) and (20a,b) give each cell of PRATYAÑC's masculine and neuter paradigms the grade
shaded in Table 9 (p. 294). -/
theorem rules_match_table9 : ∀ l ∈ [SktLex.pratyancM, .pratyancN], ∀ σ,
    (l.analyses σ).map (·.grade.map gradeOf) = [some (grade l σ)] := by decide

/-- The rules give every cell of AHAN the stem that Table 10 (p. 296) and p. 295 build it on,
each cell having one row. -/
theorem rules_match_table10 : ∀ σ,
    (SktLex.ahan.analyses σ).map (·.stem) = [some (sktStem .ahan σ).form] := by decide

/-! ### Heteroclisis from stem alternation -/

theorem SktEntry.exponent_mem_stems {e : SktEntry} {r : SktRule} (hr : r ∈ sktRulesFor e) :
    r.exponent ∈ e.stems := by
  rcases List.mem_append.mp hr with hr | hr <;>
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hr) <;>
    simp [SktEntry.stems, hz]

theorem sktStem_mem_stems (l : SktLex) (σ : SktCell) : sktStem l σ ∈ (sktEntry l).stems :=
  Exponence.RuleSet.realizeMinimalD_induction (· ∈ (sktEntry l).stems) List.mem_cons_self
    fun _ hr ↦ SktEntry.exponent_mem_stems hr

-- §3.2
theorem sktLinkage_isHeteroclite_iff {l : SktLex} :
    sktLinkage.IsHeteroclite SktStem.decl l ↔ ∃ σ τ, sktClass l σ ≠ sktClass l τ := by
  simp [Linkage.IsHeteroclite, sktLinkage, sktClass]

theorem not_isHeteroclite_of_stems {l : SktLex} {d : SktDecl}
    (h : ∀ z ∈ (sktEntry l).stems, z.decl = d) : ¬ sktLinkage.IsHeteroclite SktStem.decl l := by
  rintro ⟨σ, σ', z, hz, z', hz', hne⟩
  rw [Finset.mem_singleton.mp hz, Finset.mem_singleton.mp hz'] at hne
  exact hne ((h _ (sktStem_mem_stems l σ)).trans (h _ (sktStem_mem_stems l σ')).symm)

/-- Neither of PRATYAÑC's paradigms is heteroclite (p. 294; p. 318). -/
theorem pratyanc_not_heteroclite :
    ∀ l ∈ [SktLex.pratyancM, .pratyancN], ¬ sktLinkage.IsHeteroclite SktStem.decl l := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> exact not_isHeteroclite_of_stems (d := .consStem) (by decide)

/-- AHAN's paradigm, built on two an-stems and an as-stem, is heteroclite (p. 295). -/
theorem ahan_heteroclite : sktLinkage.IsHeteroclite SktStem.decl .ahan := by decide

/-- AHAN's cells have the grades of neuter PRATYAÑC's, though (20a) tests different endings for each
(p. 295). -/
theorem ahan_grade_eq_pratyancN : ∀ σ, grade .ahan σ = grade .pratyancN σ := by decide

theorem ahan_class_counts : #{σ | sktClass .ahan σ = .anStem} = 14 ∧
    #{σ | sktClass .ahan σ = .asStem} = 10 := by decide

/-- AHAN's degree of case correlation is .71 (= 17/24), as Table 21 (p. 312) prints it, and its
degree of number correlation, which the paper does not print, is 7/12. -/
theorem ahan_degrees : degree Category.case.proj (sktClass .ahan) = 17 / 24 ∧
    degree Category.number.proj (sktClass .ahan) = 7 / 12 := by
  decide +kernel

/-- AHAN's paradigm is fractured, as Table 25 (p. 317) classes it. -/
theorem ahan_fractured : IsFractured (sktClass .ahan) := by decide

-- Table 21, p. 312
theorem ahan_case_maximal : IsMaximalCorrelate .case (sktClass .ahan) := by decide

/-! ### The property mapping `f₁` -/

theorem pratyancM_pm (σ : SktCell) : sktLinkage.pm .pratyancM σ = ι σ := rfl

theorem neut_corr_nom_eq_acc : ∀ l, (sktEntry l).gender = .neut → ∀ n : SktNumber,
    sktLinkage.corr l (⟨.nom, by decide⟩, n) = sktLinkage.corr l (⟨.acc, by decide⟩, n) := by decide

theorem sktLinkage_isSyncretic : sktLinkage.IsSyncretic := by
  refine ⟨.ahan, .of .nom .singular, .of .acc .singular, by decide, ?_⟩
  rw [SktCell.of, SktCell.of, neut_corr_nom_eq_acc .ahan rfl, disjoint_self_iff_empty,
    ← not_nonempty_iff_eq_empty, not_not, Linkage.corr_nonempty]
  exact singleton_nonempty _

theorem sktLinkage_isUnfaithful : sktLinkage.IsUnfaithful ι :=
  ⟨.ahan, .of .nom .singular, by decide⟩

/-! ### The privileged category restriction in Sanskrit -/

/-- The Sanskrit nominals considered are HṚD(AYA) and the lexemes of §3.2. -/
abbrev SktNominal : Type := SktNoun ⊕ SktLex

/-- `sktClasses n σ` is the declension that the cell `σ` of the nominal `n` inflects in. -/
def sktClasses : SktNominal → SktCell → SktDecl := Sum.elim (fun _ ↦ hrdClass) sktClass

/-- The rules of paradigm linkage of a nominal are those of (20a,b) it instantiates, and none for
HṚD(AYA), whose stem alternation is "simply stipulated in HṚD(AYA)'s lexical entry" (p. 282). -/
def sktNominalRules : SktNominal → List SktRule := Sum.elim (fun _ ↦ []) sktRules

/-- Case is privileged for Sanskrit nominals, "a privileged inflectional category for Sanskrit
nouns" (p. 318), as the absolute correlate of HṚD(AYA)'s cloven paradigm. -/
theorem privileged_case : Privileged sktClasses .case := ⟨.inl .hrdaya, hrd_cloven⟩

theorem not_privileged_number : ¬ Privileged sktClasses .number := by
  rintro ⟨_ | l, hcl, hn⟩
  · obtain ⟨σ, τ, hne⟩ := hcl.1
    exact hne (cellClass_eq_of_isAbsoluteCorrelate hn hrd_cloven.2 σ τ)
  · cases l
    case ahan => exact ahan_fractured.2 .number hn
    all_goals exact pratyanc_not_heteroclite _ (by simp) (sktLinkage_isHeteroclite_iff.mpr hcl.1)

-- (20a,b), p. 318
theorem sktRules_sensitiveTo_case : ∀ l, ∀ r ∈ sktRules l, SensitiveTo r .case := by decide

-- (20a,b)
theorem sktRules_sensitiveTo_number : ∀ l, ∀ r ∈ sktRules l, SensitiveTo r .number := by decide

/-- The Sanskrit rules satisfy (40), since each, though sensitive to number as well, is
sensitive to case, which is privileged. -/
theorem pcr_skt : SatisfiesPCR sktClasses sktNominalRules := by
  rintro (_ | l) r hr -
  · simp [sktNominalRules] at hr
  · exact ⟨.case, privileged_case, sktRules_sensitiveTo_case l r hr⟩

/-! ### Russian MAT' (Table 5) -/

/-- The Russian numbers are the singular and the plural. -/
abbrev RuNumber : Finset Number := {.singular, .plural}

/-- A Russian content cell pairs one of the six cases with a number; the prepositional is the
locative. -/
abbrev RuCell : Type := Russian.Case × RuNumber

/-- MAT' is the one Russian lexeme considered. -/
inductive RuNoun
  | mat
  deriving DecidableEq, Fintype, Repr

/-- MAT' has "a radical stem mat' in the singular direct-case forms and an extended stem
mater' elsewhere" (p. 283). -/
inductive RuStem
  | mat
  | mater
  deriving DecidableEq, Fintype, Repr

/-- Both stems of MAT' follow the third declension (p. 283). -/
def RuStem.decl : RuStem → Russian.Gender.DeclClass
  | .mat => .III
  | .mater => .III

/-- `matLinkage` builds MAT' on *mat'* in the nominative and accusative singular and on
*mater'* elsewhere. -/
def matLinkage : Linkage RuNoun RuStem RuCell RuCell :=
  Linkage.ofFun id fun _ σ ↦
    if σ.2.1 = .singular ∧ (σ.1 = .nom ∨ σ.1 = .acc) then .mat else .mater

/-- MAT' is suppletive but not heteroclite, for "suppletion in itself does not necessitate
heteroclisis" (p. 283). -/
theorem mat_suppletive_not_heteroclite :
    matLinkage.IsSuppletive .mat ∧ ¬ matLinkage.IsHeteroclite RuStem.decl .mat := by
  decide

end Stump2006
