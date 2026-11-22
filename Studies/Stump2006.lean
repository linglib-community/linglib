module

public import Linglib.Data.Wordlist.Stump2006
public import Linglib.Morphology.Paradigm.Linkage
public import Linglib.Morphology.Exponence.DomainRule
public import Linglib.Morphology.Word.UD
public import Linglib.Fragments.Slavic.Czech.Nouns
public import Linglib.Fragments.Slavic.Russian.Case
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Syntax.Feature.Number.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.Minimal
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Languages

/-!
# Stump (2006): Heteroclisis and paradigm linkage

A lexeme is heteroclite when the cells of its paradigm are built on stems of two or more
inflection classes. A rule of paradigm linkage gives a content cell `⟨L, σ⟩` of a lexeme a form
correspondent `⟨s, τ⟩` built on one of the lexeme's stems: the universal default assigns the
root, and a language-specific rule assigns to the cells of its domain a coradical, a stem that
differs from the root in form or in inflection class. Rules compete by Pāṇini's principle, the
rule with the narrower domain prevailing.

For Czech, we define three rules as domain rules over the cells of the declension fragment. One
gives the nouns of the PRAMEN class their hard-masculine coradical in the plural, one gives the
animate nouns of that class the same coradical in the dative and locative singular, and one
gives a noun its soft-masculine coradical in the locative plural, where `inferSoftMasc` infers
that coradical from a hard-masculine stem ending in a velar. `stemFor` is the stem the rules
select and `czLinkage` the linkage they define. With the fragment's endings they realize every
form of the nine nouns of the forms data (`realize_matches_tables`), and exactly PRAMEN,
PŘEDSEDA, SLUHA and FILOLOG are heteroclite (`heteroclite_iff`).

For Sanskrit, a property set is strong or weak (`strength`), and two rules give a weak cell the
Weakest coradical where the ending that follows begins with a vowel and the Middle coradical
otherwise. One list of rules gives the grades of PRATYAÑC's stems, which share a declension
(`rules_match_table9`), and the stems of AHAN, which do not (`rules_match_table10`).

For a paradigm with cells `C`, a value `props σ c` of each inflectional category `c` at each
cell `σ`, and a map `cls` giving each cell's inflection class, the degree of correlation of a
category with values $v_1, \dots, v_m$ is $\sum_i n_i / |C|$, where $n_i$ is the largest number
of cells with value $v_i$ that inflect in one class (`degree`). A category is an absolute
correlate when `cls` factors through it, equivalently when its degree is 1
(`isAbsoluteCorrelate_iff_degree`), and a heteroclite paradigm is cloven when it has an absolute
correlate and fractured when it has none. A set `S` of categories are intersective correlates
when cells that agree in every category of `S` inflect in one class, which for `props = id` is
`DependsOn cls S` (`isIntersectiveCorrelate_id_iff`). A category is privileged when it is the
absolute correlate of a cloven paradigm, and a system of rules satisfies the privileged
category restriction when each of its rules that is sensitive to some category is sensitive to
a privileged one. The Czech and the Sanskrit rules satisfy it (`pcr`, `pcr_skt`). A language
with one rule for the plural and another for the third person of the past does not
(`not_satisfiesPCR_hRules`), and in it no minimal set of intersective correlates of the
fractured paradigm contains the privileged category
(`not_fracturedHavePrivilegedCorrelate_hClass`).

## Implementation notes

The inflectional categories of a paradigm are an index type with a family of value types, not
the pair of case and number, so that the three-category language is stated on the definitions
used for Czech and Sanskrit. A rule is taken to be sensitive to a category when two cells that
differ in that category alone differ in whether it applies. The claim that fractured paradigms
have a privileged category among their minimal intersective correlates is stated for the set of
all privileged categories, and holds of any paradigm with two categories
(`fracturedHavePrivilegedCorrelate_of_card_eq_two`).

A Czech noun's segments are the stem of its entry in the Czech noun fragment, the citation form less
the nominative singular ending of its class, so PŘEDSEDA's root and coradical share the segments
*předsed*. A stem's endings are the fragment's endings of its noun in the class that the stem's
declension is for the noun's animacy, with the velar vocative singular -u and locative plural -ích
and the noun's lexical nominative plural, MUŽ's -i or -ové and FILOLOG's -ové, and the stem is
inflected as the fragment inflects it, palatalized before the masculine locative plural -ích and the
animate nominative plural -i. Where the paper and the grammars differ the paper's forms stand and
the difference is stated: the nominative and vocative plurals in -ové of PŘEDSEDA and SLUHA,
realized on the hard-masculine coradical, whose class gives -i, are their lexical nominative
plural in the fragment, and FILOSOF's, which neither grammar gives, is an override; Stump's
hard-feminine roots for the
masculine a-stems rebuild Short's separate *hrdina* declension; and his soft-masculine coradical of
velar stems gives the locative plurals in -ích that *Mluvnice češtiny*'s rule gives the
hard-masculine stem.

Sanskrit endings are read off exemplars, chosen by declension among PRATYAÑC, NĀMAN and MANAS. Rules
compete by domain inclusion, the rendering of Pāṇini's principle, and selection falls back on the
root. Gender is taken as lexical: PRATYAÑC's masculine and neuter are two lexemes, the clause of
`f₁` that drops gender from oblique property sets is vacuous, and the feminine, built on the
ī-stem *pratīcī*, is left out, as are the default rule of stem indexing and the optional Strong
alternants of the an-stems. Sanskrit sandhi (*aho-bhis*, *pratyag-*) is unstated, so no forms
are built.

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
def czForms : List (Form Wordlist.Cell) := Wordlist.all.filter (·.languageId == .czech)

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
def Decl.toClass (d : Decl) (animate : Prop) [Decidable animate] : Czech.Declension.Class :=
  match d with
  | .softMasc => if animate then .muz else .stroj
  | .hardMasc => if animate then .chlap else .hrad
  | .hardFem => .zena

/-- `Decl.ofClass k` is the declension of the root of a noun of Short's class `k`, where the
nouns of the tables include one: the soft masculine for *muž* and *stroj*, the hard masculine
for *chlap* and *hrad*, and the hard feminine for *žena* and for the masculine a-stems of
*hrdina*, whose roots the paper takes to be hard-feminine. -/
def Decl.ofClass : Czech.Declension.Class → Option Decl
  | .muz | .stroj => some .softMasc
  | .chlap | .hrad => some .hardMasc
  | .zena | .hrdina => some .hardFem
  | _ => none

theorem Decl.ofClass_toClass (d : Decl) (p : Prop) [Decidable p] :
    Decl.ofClass (d.toClass p) = some d := by
  cases d <;> by_cases h : p <;> simp [Decl.toClass, Decl.ofClass, h]

/-- `l.noun` is the entry of `l` in the Czech noun fragment. -/
def CzNoun.noun : CzNoun → Czech.Noun
  | .pokoj => Czech.pokoj | .pramen => Czech.pramen | .most => Czech.most | .zena => Czech.zena
  | .predseda => Czech.predseda | .filosof => Czech.filosof | .sluha => Czech.sluha
  | .filolog => Czech.filolog | .muz => Czech.muz

/-- The declension of a noun's root is that of its singular class, so that PRAMEN's root is
soft-masculine (p. 289) and PŘEDSEDA's and SLUHA's are hard-feminine. -/
def CzNoun.rootDecl (l : CzNoun) : Decl := (Decl.ofClass l.noun.cls).get (by cases l <;> rfl)

/-- A noun inflects as animate when its gender is the masculine animate. -/
def CzNoun.IsAnimate (l : CzNoun) : Prop := l.noun.gender.IsAnimate

instance : DecidablePred CzNoun.IsAnimate :=
  fun l ↦ inferInstanceAs (Decidable l.noun.gender.IsAnimate)

/-- The PRAMEN class of rule (14), to which PRAMEN, PŘEDSEDA and SLUHA belong, is a lexical
stipulation. -/
def CzNoun.InPramenClass (l : CzNoun) : Prop := l = .pramen ∨ l = .predseda ∨ l = .sluha

instance : DecidablePred CzNoun.InPramenClass := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A noun belongs to the PŘEDSEDA subclass, "a subclass of masculine animate members of the
PRAMEN class" (p. 290), when it is an animate member of the PRAMEN class. -/
def CzNoun.InPredsedaSubclass (l : CzNoun) : Prop := l.InPramenClass ∧ l.IsAnimate

instance : DecidablePred CzNoun.InPredsedaSubclass :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A stem is individuated, as in the paper, by its lexeme and its inflection class; its form
is the lexeme's, so two stems of one lexeme are class-distinct and form-identical. -/
structure Stem where
  /-- `lexeme` is the noun whose stem this is. -/
  lexeme : CzNoun
  /-- `decl` is the declension the stem inflects in. -/
  decl : Decl
  deriving DecidableEq, Repr

/-- The segments of a stem are the stem of its lexeme's noun. -/
def Stem.segments (z : Stem) : List String := z.lexeme.noun.stem

/-- `czRoot l` is the root of `l`, its default stem (n. 8), which rule (5), the universal
default rule of paradigm linkage (p. 286), gives every cell that none of the rules of `l`
reaches. -/
def czRoot (l : CzNoun) : Stem := ⟨l, l.rootDecl⟩

/-- A stem is a root when it inflects in its lexeme's root declension. -/
def Stem.IsRoot (z : Stem) : Prop := z.decl = z.lexeme.rootDecl

instance : DecidablePred Stem.IsRoot := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The hard-masculine coradical of a noun of the PRAMEN class is its stem in the
hard-masculine declension. -/
def CzNoun.hardMascCoradical (l : CzNoun) : Option Stem :=
  if l.InPramenClass then some ⟨l, .hardMasc⟩ else none

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
def CzNoun.hardMascStem (l : CzNoun) : Option Stem :=
  if l.rootDecl = .hardMasc then some (czRoot l) else l.hardMascCoradical

/-- The soft-masculine coradical of a noun is the stem that rule (18) infers from its
hard-masculine stem. -/
def CzNoun.softMascCoradical (l : CzNoun) : Option Stem := l.hardMascStem.bind inferSoftMasc

-- (18)
theorem softMascCoradical_isSome_iff :
    ∀ l : CzNoun, l.softMascCoradical.isSome ↔ l = .sluha ∨ l = .filolog := by
  decide

theorem CzNoun.lexeme_of_mem_hardMascCoradical {l : CzNoun} {z : Stem}
    (hz : z ∈ l.hardMascCoradical) : z.lexeme = l := by
  unfold CzNoun.hardMascCoradical at hz
  split at hz
  · cases hz; rfl
  · cases hz

theorem CzNoun.lexeme_of_mem_softMascCoradical {l : CzNoun} {z : Stem}
    (hz : z ∈ l.softMascCoradical) : z.lexeme = l := by
  obtain ⟨y, hy, hz⟩ := Option.mem_bind_iff.mp hz
  have hy : y.lexeme = l := by
    unfold CzNoun.hardMascStem at hy
    split at hy
    · cases hy; rfl
    · exact l.lexeme_of_mem_hardMascCoradical hy
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
abbrev CellRule : Type := DomainRule CzCell Stem

/-- `plural` is the set of plural cells, `{plural X}` in the paper's notation. -/
def plural : Finset CzCell := {σ | σ.number = .plural}

/-- `datLocSg` is the set of dative and locative singular cells. -/
def datLocSg : Finset CzCell := {σ | σ.number = .singular ∧ (σ.case = .dat ∨ σ.case = .loc)}

/-- `locPl` is the locative plural cell, `{locative plural X}` in the paper's notation. -/
def locPl : Finset CzCell := {σ | σ.case = .loc ∧ σ.number = .plural}

/-- Rule (14) (p. 289) reads "Where L is a nominal lexeme that belongs to the PRAMEN class and
has s as its hard-masculine coradical, if σ = {plural X}, then the content-cell ⟨L, σ⟩ has
⟨s, σ⟩ as its form-correspondent." -/
def rule14 (l : CzNoun) : Option CellRule := l.hardMascCoradical.map (⟨plural, ·⟩)

/-- Rule (15) (p. 290) reads "Where L is a nominal lexeme that belongs to the PŘEDSEDA subclass
and has s as its hard-masculine coradical, if σ = {α singular X} and α = dative or locative,
then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its form-correspondent." -/
def rule15 (l : CzNoun) : Option CellRule :=
  if l.InPredsedaSubclass then l.hardMascCoradical.map (⟨datLocSg, ·⟩) else none

/-- Rule (17) (p. 292) reads "Where L is a nominal lexeme having s as its soft-masculine
coradical, if σ = {locative plural X}, then the content-cell ⟨L, σ⟩ has ⟨s, σ⟩ as its
form-correspondent." -/
def rule17 (l : CzNoun) : Option CellRule := l.softMascCoradical.map (⟨locPl, ·⟩)

/-- The language-specific rules of paradigm linkage applying to a noun are those of (14), (15)
and (17) whose coradicals and classes the noun has. The universal default (5) is not among
them: it is the root that `Linkage.ofRules` falls back on. -/
def czRules (l : CzNoun) : List CellRule :=
  (rule14 l).toList ++ (rule15 l).toList ++ (rule17 l).toList

/-- The stem of a cell's form correspondent is the one Pāṇini's principle selects, that of an
applicable rule no applicable rule is narrower than, or the root where no rule applies. -/
def stemFor (l : CzNoun) (σ : CzCell) : Stem :=
  RuleSet.realizeMinimalD (czRules l) (·.dom) (fun _ ↦ czRoot l) σ

theorem lexeme_stem_of_mem_czRules {l : CzNoun} {r : CellRule} (hr : r ∈ czRules l) :
    r.exponent.lexeme = l := by
  simp only [czRules, List.mem_append, Option.mem_toList] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact l.lexeme_of_mem_hardMascCoradical hz
  · unfold rule15 at hr
    split at hr
    · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
      exact l.lexeme_of_mem_hardMascCoradical hz
    · cases hr
  · obtain ⟨z, hz, rfl⟩ := Option.mem_map.mp hr
    exact l.lexeme_of_mem_softMascCoradical hz

theorem stemFor_lexeme (l : CzNoun) (σ : CzCell) : (stemFor l σ).lexeme = l :=
  RuleSet.realizeMinimalD_induction (fun z ↦ z.lexeme = l) rfl fun _ hr ↦
    lexeme_stem_of_mem_czRules hr

/-! ### Realization -/

/-- The endings of a stem at a cell are the fragment's endings of its noun in the class its
declension is for the noun's animacy: the class's endings on the noun's stem, a velar stem of the
hard masculines taking the vocative singular -u (Short, p. 465; *Mluvnice češtiny*, p. 292) and a
velar stem of the hard masculines or the masculine a-stems the locative plural -ích (*Mluvnice
češtiny*, p. 292), with the noun's lexical nominative plural. -/
def Stem.classEndings (z : Stem) (σ : CzCell) : List (List String) :=
  z.lexeme.noun.endingsIn (z.decl.toClass z.lexeme.IsAnimate) σ

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

/-- The nominative and vocative plural endings of Tables 6 and 8 that neither grammar gives:
FILOSOF's -ové. Short's tables leave out the "many formally and semantically distinctive groups
with nominative plural in -é or -ové" without placing *filosof* in one (Short, p. 466), and
*Mluvnice češtiny* gives no plural of *filozof*, its borrowed compounds in -ové being those in
-graf, -fil, -fob and -nom (p. 296). -/
def nomPlOverride : CzNoun → Option (List (List String))
  | .filosof => some [["o", "v", "é"]]
  | _ => none

/-- The endings of a stem at a cell are those of the fragment, save FILOSOF's at the nominative
and vocative plural, the vocative plural being the nominative (Short, p. 465). -/
def Stem.endings (z : Stem) (σ : CzCell) : Finset (List String) :=
  if σ ∈ nomVocPl then ((nomPlOverride z.lexeme).map List.toFinset).getD (z.tableEndings σ)
  else z.tableEndings σ

/-- A stem is inflected with an ending as the fragment inflects the noun's stem in the stem's
class, palatalized before the masculine locative plural -ích and the animate nominative plural
-i (*Mluvnice češtiny*, p. 279). So the soft-masculine coradical of a velar stem palatalizes
before -ích, as Short's *geolozích* (Short, p. 462) and *sluzích* (Short, p. 467) show. -/
def Stem.inflect (z : Stem) (σ : CzCell) (e : List String) : List String :=
  (z.decl.toClass z.lexeme.IsAnimate).inflect z.segments σ e

/-- The form cell `⟨z, σ⟩` is realized as `z` inflected with each of its endings. -/
def czRealize (z : Stem) (σ : CzCell) : Finset (List String) := (z.endings σ).image (z.inflect σ)

/-- The Czech paradigm linkage gives each content cell the stem its rules select, and
preserves its property set. -/
def czLinkage : Linkage CzNoun Stem CzCell CzCell := Linkage.ofRules id (·.dom) czRules czRoot

theorem czRealize_stemFor : ∀ l σ, czRealize (stemFor l σ) σ = attested l σ := by
  decide +kernel

/-- The rules of paradigm linkage, with the endings of the fragment and FILOSOF's nominative
plural, realize every form of Tables 1, 6 and 8. -/
theorem realize_matches_tables (l : CzNoun) (σ : CzCell) :
    czLinkage.realized czRealize l σ = {(attested l σ, σ)} :=
  (Linkage.ofFun_realized _ _ czRealize l σ).trans <|
    congrArg (fun w ↦ {(w, σ)}) (czRealize_stemFor l σ)

-- Tables 6 and 8, Table 9.2
theorem filosof_nomPl :
    attested .filosof (.of .nom .plural) = {Czech.Declension.segments "filosofové"} ∧
      Czech.filosof.forms (.of .nom .plural) = [Czech.Declension.segments "filosofi"] := by
  decide +kernel

-- n. 14, Table 9.5, p. 467, p. 292
theorem coradical_no_u : ∀ l : CzNoun, l.InPredsedaSubclass → ∀ σ ∈ datLocSg,
    czRealize ⟨l, .hardMasc⟩ σ = {l.noun.stem ++ ["o", "v", "i"]} := by
  decide

-- (14), (15), Table 9.5
theorem predseda_eq_hrdina : ∀ σ, czRealize (stemFor .predseda σ) σ =
    ((Czech.predseda.cls.endings σ).map (Czech.predseda.stem ++ ·)).toFinset := by
  decide +kernel

-- (17), (18)
theorem sluha_eq_hrdina_iff : ∀ σ, czRealize (stemFor .sluha σ) σ =
    ((Czech.sluha.cls.endings σ).map (Czech.sluha.stem ++ ·)).toFinset ↔
      σ ≠ .of .loc .plural := by
  decide +kernel

-- (17), (18), p. 467, pp. 292
theorem sluha_locPl : czRealize (stemFor .sluha (.of .loc .plural)) (.of .loc .plural) =
      {Czech.Declension.segments "sluzích"} ∧
    czRealize ⟨.sluha, .hardMasc⟩ (.of .loc .plural) = {Czech.Declension.segments "sluzích"} := by
  decide +kernel

-- (17), (18), p. 462, p. 295
theorem filolog_locPl : czRealize (stemFor .filolog (.of .loc .plural)) (.of .loc .plural) =
      {Czech.Declension.segments "filolozích"} ∧
    czRealize ⟨.filolog, .hardMasc⟩ (.of .loc .plural) =
      {Czech.Declension.segments "filolozích"} := by
  decide +kernel

-- p. 465, p. 292
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

theorem segments_invariant (l : CzNoun) : czLinkage.IsInvariantAlong Stem.segments l :=
  Linkage.ofFun_isInvariantAlong_iff.mpr fun σ σ' ↦
    show (stemFor l σ).segments = (stemFor l σ').segments by
      simp only [Stem.segments, stemFor_lexeme]

-- pp. 282–283
theorem pramen_suppletive : czLinkage.IsSuppletive .pramen := pramen_heteroclite.isSuppletive

-- (14), p. 469, p. 310
theorem pramen_eq_koren_pattern :
    ∀ σ, (cellClass .pramen σ).toClass CzNoun.pramen.IsAnimate = Czech.koren.clsAt σ.number := by
  decide

/-! ### The degree of correlation -/

section Correlation

variable {C V K : Type*} [Fintype C] [Fintype V] [Fintype K] [DecidableEq V] [DecidableEq K]

/-- `degreeNum A cls` is the numerator of the degree of `A`-correlation (p. 309), the sum over
the values `v` of `A` of "the largest number of cells in P that carry the specification vᵢ and
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

The cells of a paradigm are of any type `C`, with `props σ c` the value at the cell `σ` of the
inflectional category `c`, and `cls` gives the inflection class of each cell. -/

section Correlates

variable {ι C K L E : Type*} {V : ι → Type*} {props : C → ∀ c, V c} {cls : C → K} {c : ι}

/-- Categories are intersective correlates of a paradigm's heteroclisis when "for each
well-formed property set τ specified for exactly the categories A₁, . . . , A_n there is a
single inflection class C such that every cell in P realizing τ inflects as a member of C"
(p. 313): cells that agree in every category of `S` inflect in one class. -/
def IsIntersectiveCorrelate (props : C → ∀ c, V c) (cls : C → K) (S : Finset ι) : Prop :=
  ∀ ⦃σ τ⦄, (∀ c ∈ S, props σ c = props τ c) → cls σ = cls τ

/-- A category is an absolute correlate of a paradigm's heteroclisis "if and only if the degree
of A-correlation in that paradigm is 1.0" (p. 309), that is, when it is by itself an
intersective correlate. -/
abbrev IsAbsoluteCorrelate (props : C → ∀ c, V c) (c : ι) (cls : C → K) : Prop :=
  IsIntersectiveCorrelate props cls {c}

theorem isAbsoluteCorrelate_iff_factorsThrough :
    IsAbsoluteCorrelate props c cls ↔ cls.FactorsThrough (props · c) := by
  simp [IsIntersectiveCorrelate, Function.FactorsThrough]

/-- A paradigm is cloven when it is heteroclite and has an absolute correlate (p. 309). -/
@[mk_iff]
structure IsCloven (props : C → ∀ c, V c) (cls : C → K) : Prop where
  /-- Two cells inflect in distinct classes. -/
  heteroclite : ∃ σ τ, cls σ ≠ cls τ
  /-- Some category is an absolute correlate. -/
  absolute : ∃ c, IsAbsoluteCorrelate props c cls

/-- A paradigm is fractured when it is heteroclite and lacks any absolute correlate (p. 309). -/
@[mk_iff]
structure IsFractured (props : C → ∀ c, V c) (cls : C → K) : Prop where
  /-- Two cells inflect in distinct classes. -/
  heteroclite : ∃ σ τ, cls σ ≠ cls τ
  /-- No category is an absolute correlate. -/
  not_absolute : ∀ c, ¬ IsAbsoluteCorrelate props c cls

theorem isIntersectiveCorrelate_id_iff {cls : (∀ c, V c) → K} {S : Finset ι} :
    IsIntersectiveCorrelate id cls S ↔ DependsOn cls S :=
  Iff.rfl

theorem IsIntersectiveCorrelate.mono {S T : Finset ι} (h : IsIntersectiveCorrelate props cls S)
    (hST : S ⊆ T) : IsIntersectiveCorrelate props cls T :=
  fun _ _ hστ ↦ h fun c hc ↦ hστ c (hST hc)

theorem isIntersectiveCorrelate_univ [Fintype ι] (hprops : Function.Injective props)
    (cls : C → K) : IsIntersectiveCorrelate props cls univ :=
  fun _ _ h ↦ congrArg cls (hprops (funext fun c ↦ h c (mem_univ c)))

theorem minimal_univ_of_isFractured [Fintype ι] (hprops : Function.Injective props)
    (hι : Fintype.card ι = 2) (h : IsFractured props cls) :
    Minimal (IsIntersectiveCorrelate props cls) univ := by
  refine ⟨isIntersectiveCorrelate_univ hprops cls, fun S hS _ ↦ ?_⟩
  by_contra hne
  have hlt : #S < 2 := by
    rw [← hι]
    exact (card_lt_iff_ne_univ S).mpr fun hS ↦ hne hS.ge
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨c, hc⟩ := card_le_one_iff_subset_singleton.mp (Nat.lt_succ_iff.mp hlt)
  exact h.not_absolute c (hS.mono hc)

/-- A rule is sensitive to the value of a category when the other categories are not
intersective correlates of its applicability. -/
def SensitiveTo [Fintype ι] [DecidableEq ι] (props : C → ∀ c, V c) (r : DomainRule C E)
    (c : ι) : Prop :=
  ¬ IsIntersectiveCorrelate props (Applies r) {c}ᶜ

theorem sensitiveTo_iff [Fintype ι] [DecidableEq ι] {r : DomainRule C E} :
    SensitiveTo props r c ↔
      ∃ σ τ, (∀ c' ≠ c, props σ c' = props τ c') ∧ ¬ (σ ∈ r.dom ↔ τ ∈ r.dom) := by
  simp [SensitiveTo, IsIntersectiveCorrelate]

/-- A category is privileged for a family `cls` of class maps, one for each lexeme, when it
serves as an absolute correlate of a cloven paradigm: "the inflectional categories serving as
absolute correlates of heteroclisis in a given language are PRIVILEGED" (p. 315). -/
def Privileged (props : C → ∀ c, V c) (cls : L → C → K) (c : ι) : Prop :=
  ∃ l, IsCloven props (cls l) ∧ IsAbsoluteCorrelate props c (cls l)

/-- Claim (39) (p. 313) reads "Suppose S is a nonempty set of inflectional categories serving as
absolute correlates in cloven paradigms of lexemes belonging to syntactic category C in language
ℓ. In that case, every fractured paradigm of category C in ℓ has a member of S as one of its
minimal intersective correlates." -/
def FracturedHavePrivilegedCorrelate (props : C → ∀ c, V c) (cls : L → C → K) : Prop :=
  (∃ c, Privileged props cls c) → ∀ l, IsFractured props (cls l) →
    ∃ S, Minimal (IsIntersectiveCorrelate props (cls l)) S ∧ ∃ c ∈ S, Privileged props cls c

-- (39), p. 313
theorem fracturedHavePrivilegedCorrelate_of_card_eq_two [Fintype ι]
    (hprops : Function.Injective props) (hι : Fintype.card ι = 2) (cls : L → C → K) :
    FracturedHavePrivilegedCorrelate props cls :=
  fun ⟨c, hc⟩ _ h ↦ ⟨univ, minimal_univ_of_isFractured hprops hι h, c, mem_univ c, hc⟩

/-- A system of rules satisfies the privileged category restriction (40) (p. 316), which reads
"If a rule of paradigm linkage applies to lexemes belonging to a privileged syntactic category C
and this rule is sensitive to the value of any inflectional category, then it is sensitive to
the value of a privileged inflectional category for members of C." The lexemes `L` are taken to
form one privileged syntactic category, so the antecedent on the syntactic category is left
implicit. -/
def SatisfiesPCR [Fintype ι] [DecidableEq ι] (props : C → ∀ c, V c) (cls : L → C → K)
    (rules : L → RuleSet (DomainRule C E)) : Prop :=
  ∀ l, ∀ r ∈ rules l, (∃ c, SensitiveTo props r c) →
    ∃ c, Privileged props cls c ∧ SensitiveTo props r c

section Decidable

variable [Fintype C] [DecidableEq K] [∀ c, DecidableEq (V c)]

instance (S : Finset ι) : Decidable (IsIntersectiveCorrelate props cls S) :=
  inferInstanceAs (Decidable (∀ σ τ, (∀ c ∈ S, props σ c = props τ c) → cls σ = cls τ))

instance [Fintype ι] : Decidable (IsCloven props cls) :=
  decidable_of_iff' _ (isCloven_iff ..)

instance [Fintype ι] : Decidable (IsFractured props cls) :=
  decidable_of_iff' _ (isFractured_iff ..)

variable [Fintype ι] [DecidableEq ι] [DecidableEq C]

instance (r : DomainRule C E) (c : ι) : Decidable (SensitiveTo props r c) :=
  decidable_of_iff' _ sensitiveTo_iff

instance [Fintype L] (cls : L → C → K) (c : ι) : Decidable (Privileged props cls c) :=
  inferInstanceAs (Decidable (∃ _, _))

instance [Fintype L] (cls : L → C → K) (rules : L → RuleSet (DomainRule C E)) :
    Decidable (SatisfiesPCR props cls rules) :=
  have (r : DomainRule C E) : Decidable ((∃ c, SensitiveTo props r c) →
      ∃ c, Privileged props cls c ∧ SensitiveTo props r c) :=
    inferInstance
  inferInstanceAs (Decidable (∀ _, _))

end Decidable

section Degree

variable [Fintype C] [Fintype K] [DecidableEq K] [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]

/-- A category is a maximal correlate when its degree "is higher than any other inflectional
category's degree of correlation in that paradigm" (p. 309). -/
def IsMaximalCorrelate (props : C → ∀ c, V c) (c : ι) (cls : C → K) : Prop :=
  ∀ c' ≠ c, degreeNum (props · c') cls < degreeNum (props · c) cls

theorem isAbsoluteCorrelate_iff_degree [Nonempty C] :
    IsAbsoluteCorrelate props c cls ↔ degree (props · c) cls = 1 :=
  isAbsoluteCorrelate_iff_factorsThrough.trans degree_eq_one_iff.symm

theorem IsAbsoluteCorrelate.isMaximalCorrelate (h : IsAbsoluteCorrelate props c cls)
    (h' : ∀ c' ≠ c, ¬ IsAbsoluteCorrelate props c' cls) : IsMaximalCorrelate props c cls := by
  intro c' hc'
  rw [(degreeNum_eq_card_iff _ _).mpr (isAbsoluteCorrelate_iff_factorsThrough.mp h)]
  exact (degreeNum_le_card _ _).lt_of_ne fun hEq ↦
    h' c' hc' (isAbsoluteCorrelate_iff_factorsThrough.mpr ((degreeNum_eq_card_iff _ _).mp hEq))

instance [Fintype ι] [DecidableEq ι] (c : ι) : Decidable (IsMaximalCorrelate props c cls) :=
  inferInstanceAs (Decidable (∀ _, _ → _))

end Degree

end Correlates

/-! ### Case and number -/

section CaseNumber

universe u

variable {A B : Type u} {K : Type*}

/-- The inflectional categories of a nominal are number and case. -/
inductive Category
  | number
  | case
  deriving DecidableEq, Fintype, Repr

/-- The values of a category are the numbers `B` or the cases `A`. -/
@[reducible] def Category.Value (A B : Type u) : Category → Type u
  | .number => B
  | .case => A

instance [DecidableEq A] [DecidableEq B] : ∀ c : Category, DecidableEq (c.Value A B)
  | .number => inferInstanceAs (DecidableEq B)
  | .case => inferInstanceAs (DecidableEq A)

instance [Fintype A] [Fintype B] : ∀ c : Category, Fintype (c.Value A B)
  | .number => inferInstanceAs (Fintype B)
  | .case => inferInstanceAs (Fintype A)

/-- `caseNumber σ c` is the value of the category `c` at a cell `σ` pairing a case with a
number. -/
def caseNumber (σ : A × B) : ∀ c : Category, c.Value A B
  | .number => σ.2
  | .case => σ.1

theorem caseNumber_injective : Function.Injective (caseNumber (A := A) (B := B)) :=
  fun _ _ h ↦ Prod.ext (congrFun h .case) (congrFun h .number)

theorem eq_of_isAbsoluteCorrelate_number_of_case {cls : A × B → K}
    (hn : IsAbsoluteCorrelate caseNumber .number cls)
    (hc : IsAbsoluteCorrelate caseNumber .case cls) (σ τ : A × B) : cls σ = cls τ :=
  ((isAbsoluteCorrelate_iff_factorsThrough.mp hc) (a := σ) (b := (σ.1, τ.2)) rfl).trans
    ((isAbsoluteCorrelate_iff_factorsThrough.mp hn) rfl)

end CaseNumber

/-! ### Correlates of Czech heteroclisis -/

theorem pramen_degrees : degree (caseNumber · .number) (cellClass .pramen) = 1 ∧
    degree (caseNumber · .case) (cellClass .pramen) = 1 / 2 := by
  decide +kernel

theorem predseda_degrees : degree (caseNumber · .number) (cellClass .predseda) = 6 / 7 ∧
    degree (caseNumber · .case) (cellClass .predseda) = 9 / 14 := by
  decide +kernel

theorem sluha_degrees : degree (caseNumber · .number) (cellClass .sluha) = 11 / 14 ∧
    degree (caseNumber · .case) (cellClass .sluha) = 4 / 7 := by
  decide +kernel

-- p. 313
theorem filolog_degrees : degree (caseNumber · .number) (cellClass .filolog) = 13 / 14 ∧
    degree (caseNumber · .case) (cellClass .filolog) = 13 / 14 := by
  decide +kernel

theorem pramen_cloven : IsCloven caseNumber (cellClass .pramen) := by decide

theorem predseda_fractured : IsFractured caseNumber (cellClass .predseda) := by decide

theorem sluha_fractured : IsFractured caseNumber (cellClass .sluha) := by decide

theorem filolog_fractured : IsFractured caseNumber (cellClass .filolog) := by decide

-- (38), p. 312
theorem number_maximal_predseda_sluha :
    IsMaximalCorrelate caseNumber .number (cellClass .predseda) ∧
      IsMaximalCorrelate caseNumber .number (cellClass .sluha) := by
  decide

-- p. 313
theorem filolog_no_maximal : ∀ c, ¬ IsMaximalCorrelate caseNumber c (cellClass .filolog) := by
  decide

/-! ### Rules sensitive to a category -/

-- (14), p. 316
theorem pramen_number_absolute : IsAbsoluteCorrelate caseNumber .number (cellClass .pramen) := by
  have h : ∀ r ∈ czRules .pramen, ∀ ⦃σ τ : CzCell⦄,
      caseNumber σ .number = caseNumber τ .number → (Applies r σ ↔ Applies r τ) := by
    decide
  exact isAbsoluteCorrelate_iff_factorsThrough.mpr <|
    (RuleSet.realizeMinimalD_factorsThrough (key := fun r : CellRule ↦ r.dom)
      (fallback := fun _ ↦ czRoot .pramen) (fun _ _ _ ↦ rfl) h).comp_left Stem.decl

theorem number_maximal_pramen : IsMaximalCorrelate caseNumber .number (cellClass .pramen) :=
  pramen_number_absolute.isMaximalCorrelate (by decide)

/-! ### The privileged category restriction -/

theorem privileged_number : Privileged caseNumber cellClass .number :=
  ⟨.pramen, pramen_cloven, pramen_number_absolute⟩

-- p. 316
theorem not_privileged_case : ¬ Privileged caseNumber cellClass .case := by decide +kernel

/-- The Czech rules (14), (15) and (17) satisfy the privileged category restriction (40). -/
theorem pcr : SatisfiesPCR caseNumber cellClass czRules := by decide +kernel

-- (39), p. 313
theorem fracturedHavePrivilegedCorrelate : FracturedHavePrivilegedCorrelate caseNumber cellClass :=
  fracturedHavePrivilegedCorrelate_of_card_eq_two caseNumber_injective rfl _

/-! ### The hypothetical language of (41)

The rules (41a,b) give a type-I verb its class-B coradical in the plural and a type-II verb its
class-B coradical in the third person of the past (Table 26). -/

/-- The inflectional categories of the hypothetical verbs are tense, person and number. -/
inductive VCategory
  | tense
  | person
  | number
  deriving DecidableEq, Fintype, Repr

/-- The tenses of Table 26 are the present and the past. -/
inductive HTense
  | present
  | past
  deriving DecidableEq, Fintype, Repr

/-- The persons of Table 26 are the first, the second and the third. -/
inductive HPerson
  | first
  | second
  | third
  deriving DecidableEq, Fintype, Repr

/-- The numbers of Table 26 are the singular and the plural. -/
inductive HNumber
  | singular
  | plural
  deriving DecidableEq, Fintype, Repr

/-- A cell of Table 26 has a tense, a person and a number. -/
structure HCell where
  /-- `tense` is the cell's tense. -/
  tense : HTense
  /-- `person` is the cell's person. -/
  person : HPerson
  /-- `number` is the cell's number. -/
  number : HNumber
  deriving DecidableEq, Fintype, Repr

/-- The values of a category of the hypothetical verbs. -/
@[reducible] def VCategory.Value : VCategory → Type
  | .tense => HTense
  | .person => HPerson
  | .number => HNumber

instance : ∀ c : VCategory, DecidableEq c.Value
  | .tense => inferInstanceAs (DecidableEq HTense)
  | .person => inferInstanceAs (DecidableEq HPerson)
  | .number => inferInstanceAs (DecidableEq HNumber)

/-- `hProps σ c` is the value of the category `c` at the cell `σ`. -/
def hProps (σ : HCell) : ∀ c : VCategory, c.Value
  | .tense => σ.tense
  | .person => σ.person
  | .number => σ.number

/-- The hypothetical verbs are of type I or of type II. -/
inductive HLexeme
  | typeI
  | typeII
  deriving DecidableEq, Fintype, Repr

/-- The inflection classes of Table 26 are A, that of each verb's root, and B, that of its
coradical. -/
inductive HClass
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- The rules (41) (p. 317) read "a. If L is a type-I verbal lexeme having s as its class B
coradical and σ = {plural X}, then ⟨L, σ⟩ has ⟨s, σ⟩ as its form-correspondent. b. If L is a
type-II verbal lexeme having s as its class B coradical and σ = {past 3rd X}, then ⟨L, σ⟩ has
⟨s, σ⟩ as its form-correspondent." -/
def hRules : HLexeme → List (DomainRule HCell HClass)
  | .typeI => [⟨{σ | σ.number = .plural}, .b⟩]
  | .typeII => [⟨{σ | σ.tense = .past ∧ σ.person = .third}, .b⟩]

/-- `hClass l σ` is the class that the cell `σ` of a verb of type `l` inflects in, class A where
its rule does not apply. -/
def hClass (l : HLexeme) (σ : HCell) : HClass :=
  RuleSet.realizeMinimalD (hRules l) (·.dom) (fun _ ↦ .a) σ

-- (41a), p. 317
theorem typeI_cloven : IsCloven hProps (hClass .typeI) := by decide

theorem privileged_iff_number : ∀ c, Privileged hProps hClass c ↔ c = .number := by decide

-- (41b), p. 317
theorem typeII_fractured : IsFractured hProps (hClass .typeII) := by decide

-- (41b), p. 317
theorem typeII_minimal :
    Minimal (IsIntersectiveCorrelate hProps (hClass .typeII)) {.tense, .person} := by
  unfold Minimal
  decide

/-- The hypothetical language violates the privileged category restriction (40), its type-II
rule being sensitive to tense and person but not to number, the privileged category. -/
theorem not_satisfiesPCR_hRules : ¬ SatisfiesPCR hProps hClass hRules := by decide

-- (39)
theorem not_fracturedHavePrivilegedCorrelate_hClass :
    ¬ FracturedHavePrivilegedCorrelate hProps hClass := by
  have key : ∀ S : Finset VCategory, .number ∈ S →
      ¬ Minimal (IsIntersectiveCorrelate hProps (hClass .typeII)) S := by
    unfold Minimal
    decide
  intro h
  obtain ⟨S, hS, c, hc, hpriv⟩ :=
    h ⟨.number, (privileged_iff_number _).mpr rfl⟩ .typeII typeII_fractured
  exact key S ((privileged_iff_number c).mp hpriv ▸ hc) hS

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

theorem hrd_form_suppletive : hrdLinkage.IsHeteroclite SktStem.form .hrdaya := by decide

-- p. 313, p. 310
theorem hrd_cloven : IsCloven caseNumber hrdClass ∧
    IsAbsoluteCorrelate caseNumber .case hrdClass := by
  decide

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

/-- A property set is strong or weak, as (19) defines. -/
inductive Strength
  | strong
  | weak
  deriving DecidableEq, Repr

/-- Clause (19a) makes strong the direct-case property sets of a masculine and the direct-case
plural ones of a neuter. -/
def rule19a (g : SktGender) : DomainRule SktCell Strength :=
  ⟨{σ | σ.1.1 ∈ direct ∧ (g = .masc ∨ σ.2.1 = .plural)}, .strong⟩

/-- Clause (19b) makes weak the accusative plural property set of a masculine. -/
def rule19b (g : SktGender) : DomainRule SktCell Strength :=
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
  RuleSet.realizeMinimalD [rule19a g, rule19b g] (·.dom) (fun _ ↦ .weak) σ

/-- `weak g` is the set of weak property sets of a lexeme of gender `g`. -/
def weak (g : SktGender) : Finset SktCell := {σ | strength g σ = .weak}

/-- A Sanskrit row expresses the concept `pid` in the gender `g` at the cell `σ`. -/
def SktRow (pid : String) (g : SktGender) (σ : SktCell) (f : Form Wordlist.Cell) : Bool :=
  f.languageId == .sanskrit && f.parameterId == pid && f.cell.gender = ↑g.ud &&
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
abbrev SktRule : Type := DomainRule SktCell SktStem

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
default (12) is not among them: it is the root that `RuleSet.realizeMinimalD` falls
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
  RuleSet.realizeMinimalD (sktRules l) (·.dom) (fun _ ↦ sktRoot l) σ

/-- The Sanskrit paradigm linkage gives each content cell the stem its rules select, with the
form property set that `f₁` maps its property set to. -/
def sktLinkage : Linkage SktLex SktStem SktCell SktForm where
  realize l σ := {sktStem l σ}
  pm l := f₁ (sktEntry l).gender

/-- The grade of a stem in an entry is weakest for its Weakest coradical, middle for its Middle
coradical, and strong for its root. -/
def SktEntry.gradeOf (e : SktEntry) (z : SktStem) : Wordlist.Grade :=
  if e.weakest = some z then .weakest else if e.middle = some z then .middle else .strong

/-- `grade l σ` is the grade of the stem that the rules select at the cell `σ` of `l`. -/
def grade (l : SktLex) (σ : SktCell) : Wordlist.Grade := (sktEntry l).gradeOf (sktStem l σ)

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

-- (20a)
theorem sktEndings_length : ∀ l σ, ∀ z ∈ (sktEntry l).weakest,
    (sktEndings z.decl (sktEntry l).gender (f₁ (sktEntry l).gender σ)).length = 1 := by decide

-- (20a), (20b), p. 295
theorem rule20a_lt_rule20b : ∀ l, ∀ a ∈ rule20a (sktEntry l), ∀ b ∈ rule20b (sktEntry l),
    a.dom ⊂ b.dom := by decide

-- (19), (20a,b), Table 9, p. 294
theorem rules_match_table9 : ∀ l ∈ [SktLex.pratyancM, .pratyancN], ∀ σ,
    (l.analyses σ).map (·.grade) = [some (grade l σ)] := by decide

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
  RuleSet.realizeMinimalD_induction (· ∈ (sktEntry l).stems) List.mem_cons_self
    fun _ hr ↦ SktEntry.exponent_mem_stems hr

-- §3.2
theorem sktLinkage_isHeteroclite_iff {l : SktLex} :
    sktLinkage.IsHeteroclite SktStem.decl l ↔ ∃ σ τ, sktClass l σ ≠ sktClass l τ := by
  simp [Linkage.isHeteroclite_iff, sktLinkage, sktClass]

theorem not_isHeteroclite_of_stems {l : SktLex} {d : SktDecl}
    (h : ∀ z ∈ (sktEntry l).stems, z.decl = d) : ¬ sktLinkage.IsHeteroclite SktStem.decl l := by
  intro hh
  obtain ⟨σ, σ', z, hz, z', hz', hne⟩ := Linkage.isHeteroclite_iff.1 hh
  rw [Finset.mem_singleton.mp hz, Finset.mem_singleton.mp hz'] at hne
  exact hne ((h _ (sktStem_mem_stems l σ)).trans (h _ (sktStem_mem_stems l σ')).symm)

-- p. 294, p. 318
theorem pratyanc_not_heteroclite :
    ∀ l ∈ [SktLex.pratyancM, .pratyancN], ¬ sktLinkage.IsHeteroclite SktStem.decl l := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> exact not_isHeteroclite_of_stems (d := .consStem) (by decide)

-- p. 295
theorem ahan_heteroclite : sktLinkage.IsHeteroclite SktStem.decl .ahan := by decide

-- (20a), p. 295
theorem ahan_grade_eq_pratyancN : ∀ σ, grade .ahan σ = grade .pratyancN σ := by decide

theorem ahan_class_counts : #{σ | sktClass .ahan σ = .anStem} = 14 ∧
    #{σ | sktClass .ahan σ = .asStem} = 10 := by decide

-- Table 21, p. 312
theorem ahan_degrees : degree (caseNumber · .case) (sktClass .ahan) = 17 / 24 ∧
    degree (caseNumber · .number) (sktClass .ahan) = 7 / 12 := by
  decide +kernel

-- Table 25, p. 317
theorem ahan_fractured : IsFractured caseNumber (sktClass .ahan) := by decide

-- Table 21, p. 312
theorem ahan_case_maximal : IsMaximalCorrelate caseNumber .case (sktClass .ahan) := by decide

/-! ### The property mapping `f₁` -/

theorem pratyancM_pm (σ : SktCell) : sktLinkage.pm .pratyancM σ = ι σ := rfl

theorem neut_corr_nom_eq_acc : ∀ l, (sktEntry l).gender = .neut → ∀ n : SktNumber,
    sktLinkage.corr l (⟨.nom, by decide⟩, n) = sktLinkage.corr l (⟨.acc, by decide⟩, n) := by decide

theorem sktLinkage_isSyncretic : sktLinkage.IsSyncretic := by
  refine Linkage.isSyncretic_of_not_disjoint (l := .ahan) (σ₁ := .of .nom .singular)
    (σ₂ := .of .acc .singular) (by decide) ?_
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

-- p. 318
theorem privileged_case : Privileged caseNumber sktClasses .case := ⟨.inl .hrdaya, hrd_cloven⟩

theorem not_privileged_number : ¬ Privileged caseNumber sktClasses .number := by
  rintro ⟨_ | l, hcl, hn⟩
  · obtain ⟨σ, τ, hne⟩ := hcl.heteroclite
    exact hne (eq_of_isAbsoluteCorrelate_number_of_case hn hrd_cloven.2 σ τ)
  · cases l
    case ahan => exact ahan_fractured.not_absolute .number hn
    all_goals
      exact pratyanc_not_heteroclite _ (by simp) (sktLinkage_isHeteroclite_iff.mpr hcl.heteroclite)

-- (20a,b), p. 318
theorem sktRules_sensitiveTo_case : ∀ l, ∀ r ∈ sktRules l, SensitiveTo caseNumber r .case := by
  decide

-- (20a,b)
theorem sktRules_sensitiveTo_number :
    ∀ l, ∀ r ∈ sktRules l, SensitiveTo caseNumber r .number := by
  decide

-- (40)
theorem pcr_skt : SatisfiesPCR caseNumber sktClasses sktNominalRules := by
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

/-- `matRule` gives the cells other than the nominative and accusative singular form
correspondents built on the coradical *mater'*. -/
def matRule : DomainRule RuCell RuStem :=
  ⟨{σ | ¬ (σ.2.1 = .singular ∧ (σ.1 = .nom ∨ σ.1 = .acc))}, .mater⟩

/-- `matLinkage` builds MAT' on its root *mat'* in the nominative and accusative singular and on
*mater'* elsewhere. -/
def matLinkage : Linkage RuNoun RuStem RuCell RuCell :=
  Linkage.ofRules id (·.dom) (fun _ ↦ [matRule]) fun _ ↦ .mat

-- p. 318
theorem matRule_sensitiveTo_number : SensitiveTo caseNumber matRule .number := by decide

-- p. 283
theorem mat_suppletive_not_heteroclite :
    matLinkage.IsSuppletive .mat ∧ ¬ matLinkage.IsHeteroclite RuStem.decl .mat := by
  decide

end Stump2006
