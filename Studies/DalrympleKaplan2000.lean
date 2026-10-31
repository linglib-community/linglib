module

public import Linglib.Core.Order.Flat.Finset
public import Linglib.Data.Examples.DalrympleKaplan2000
public import Linglib.Syntax.Agreement.Resolution
public import Linglib.Syntax.Person.System
public import Linglib.Fragments.Chichewa.Gender
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.German.Pronouns
public import Linglib.Fragments.German.Verbs
public import Linglib.Fragments.Slavic.Polish.Pronouns
public import Linglib.Fragments.Xhosa.Basic
public import Linglib.Morphology.Paradigm.Morphome
public import Studies.Corbett1991
public import Studies.Shieber1986
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Linglib.Data.Examples.Readers

/-!
# Dalrymple and Kaplan, feature indeterminacy and feature resolution (2000)

A syncretic form such as German *was* satisfies conflicting case requirements at once, and a
coordinate noun phrase has a person or gender of its own computed from those of its conjuncts.
Dalrymple and Kaplan represent both with set-valued features. An indeterminate value is the set
of atomic values the form can realize and a contextual requirement is membership in it, so one
value meets two requirements where equality against an atomic value, whether disjoined or left
unspecified, cannot; a syncretic agreement form imposes an indeterminate requirement that
distributes to the conjuncts of a coordinate subject. A resolving value is a set of markers, and
the person or gender of a coordination is the union of its conjuncts' sets, the least set the
subset annotations of the coordination rule allow. Resolving features are never indeterminate.

We prove that an indeterminate value is a syncretism class of a paradigm, read off the fragments
for *was*, *kogo*, *set*, *kaufen* and the Xhosa and Chichewa subject prefixes, that unification
of the two verbs' atomic requirements fails, and that underspecification, the universal set,
overgenerates. The marker set of a person value is its largest participant set, and union on
marker sets is the substrate's join of persons (`markers_sup`), so the Spanish, Slovak and Fula
judgments follow from the conjuncts' persons; two markers bound the persons at four, and the
intersection analysis of Sag, Gazdar, Wasow and Weisler is the complement dual, which loses
Fula's clusivity with their first person. For gender, union reproduces Corbett's resolution
rules on every coordination, not only on the paper's tables of pairs: Hindi's, Icelandic's
(`Corbett1991.Icelandic.rules`), and Slovene's (`Corbett1991.Slovene.rules`) once the
conjunction contributes a marker, which is where Slovene departs from same-gender congruence.

## Implementation notes

* The syncretism class is the maximal indeterminate value a form can bear; §4.5 leaves it to
  the speaker's lexicon whether a form bears it or the disjunction of its singletons, and the
  file analyses the grammars that accept the paper's examples.
* The resolved value of a coordination `cs` is `cs.toFinset.sup mark`. That it is the minimal
  model of the subset annotations (93) is `Finset.isLUB_sup`, and the intersection dual of
  §6.5 is `Finset.compl_sup`.
* Fula's first singular *min* has the exclusive's marker set (87), so it is the quadripartition's
  `firstExclusive`; the first person unmarked for clusivity has `{S,H}` (91).
* A union claim reads only which genders occur, as Corbett's rules do
  (`Agreement.ResolutionRule.resolve_congr`), so it is checked on the sublists of a language's
  genders.

## TODO

* The paper offers two accounts of Slovene and declines to choose; only the one on which the
  conjunction contributes `F` is formalized, and on the other coordinated neuters are neuter
  and the neuter plural verb form is what is restricted.

## References

* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
* [A. Zaenen and L. Karttunen, *Morphological non-distinctiveness and coordination*
  (1984)][zaenen-karttunen-1984]
* [G. K. Pullum and A. M. Zwicky, *Phonological resolution of syntactic feature conflict*
  (1986)][pullum-zwicky-1986]
* [A. Groos and H. van Riemsdijk, *Matching effects in free relatives*
  (1981)][groos-van-riemsdijk-1981]
* [S. Dyła, *Across-the-board dependencies and case in Polish* (1984)][dyla-1984]
* [E. Voeltz, *Surface constraints and agreement resolution* (1971)][voeltz-1971]
* [G. G. Corbett, *Hierarchies, targets and controllers* (1983)][corbett-1983]
* [G. G. Corbett, *Resolution rules: Agreement in person, number, and gender*
  (1983)][corbett-1983b]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett and A. D. Mtenje, *Gender agreement in Chichewa* (1987)][corbett-mtenje-1987]
* [I. A. Sag, G. Gazdar, T. Wasow and S. Weisler, *Coordination and how to distinguish
  categories* (1985)][sag-etal-1985]
* [A. M. Zwicky, *Hierarchies of person* (1977)][zwicky-1977b]
* [R. M. Kaplan and J. Bresnan, *Lexical-functional grammar* (1982)][kaplan-bresnan-1982]
* [S. M. Shieber, *An introduction to unification-based approaches to grammar*
  (1986)][shieber-1986]
* [R. Noyer, *Features, positions, and affixes in autonomous morphological structure*
  (1992)][noyer-1992]
-/

@[expose] public section

namespace DalrympleKaplan2000

open Morphology Agreement.ResolutionRule

/-- The paper's judgment on `e` is the prediction `P`. -/
abbrev AcceptableIff (e : Datum) (P : Prop) : Prop := e.judgment = .acceptable ↔ P

/-- A distributive requirement on a coordinate structure holds of each conjunct ((44), (73)). -/
abbrev Distributes {α : Type*} (P : α → Prop) (s : Finset α) : Prop := ∀ f ∈ s, P f

/-! ### Indeterminacy: set values and membership (§§3–4) -/

-- (17)
theorem requirements_not_compatible :
    ¬ Compat (Morphology.Features.of (case := some .acc))
      (Morphology.Features.of (case := some .nom)) := by
  decide

open German.Pronouns in
-- (26), (32)
theorem german_cases :
    formCellsOf wer "wer" = {German.Case.nom} ∧ formCellsOf wer "wem" = {.dat} ∧
      formCellsOf was "was" = {.nom, .acc} := by
  decide

open German.Pronouns in
-- (28), (31), (36)
theorem was_isLeast :
    IsLeast {v | German.Case.acc ∈ v ∧ German.Case.nom ∈ v} (formCellsOf was "was") := by
  rw [german_cases.2.2]
  exact ⟨by simp, fun v ⟨ha, hn⟩ ↦ by simp [Finset.insert_subset_iff, ha, hn]⟩

open German.Pronouns in
-- (22), §3.2
theorem underspecification_overgenerates :
    (∀ x : Flat German.Case, formCellsOf was "was" ⊆ x.extensions ↔ x = ⊥) ∧
      German.Case.dat ∈ (⊥ : Flat German.Case).extensions \ formCellsOf was "was" ∧
      German.Case.gen ∈ (⊥ : Flat German.Case).extensions \ formCellsOf was "was" := by
  rw [german_cases.2.2]
  exact ⟨fun _ ↦ Flat.subset_extensions_iff_eq_bot ⟨.nom, by simp, .acc, by simp, by decide⟩,
    by decide, by decide⟩

open German.Pronouns in
-- (28), (30), (32), (33)
theorem free_relatives :
    AcceptableIff Examples.ex_17
        (German.Case.acc ∈ formCellsOf was "was" ∧
          German.Case.nom ∈ formCellsOf was "was") ∧
      AcceptableIff Examples.ex_32
        (German.Case.dat ∈ formCellsOf wer "wem" ∧
          German.Case.nom ∈ formCellsOf wer "wem") := by
  decide

open Polish.Pronouns in
-- (40), (41), (46)
theorem polish_cases :
    formCellsOf kto "kogo" = {Polish.Case.acc, .gen} ∧
      formCellsOf co "co" = {Polish.Case.nom, .acc} := by
  decide

open Polish.Pronouns in
-- (40), (46), (41)
theorem polish_coordination :
    AcceptableIff Examples.ex_40
        (Polish.Case.acc ∈ formCellsOf kto "kogo" ∧
          Polish.Case.gen ∈ formCellsOf kto "kogo") ∧
      AcceptableIff Examples.ex_41
        (Polish.Case.acc ∈ formCellsOf co "co" ∧
          Polish.Case.gen ∈ formCellsOf co "co") := by
  decide

open English
open English.Verbs hiding Verb
-- (50)
theorem set_cells :
    formCells set_.realize "set" =
      {English.Verbs.Verb.Cell.base, .plainPresent, .past, .pastParticiple} := by
  decide

open English
open English.Verbs hiding Verb
-- (49), (50), (47), (48)
theorem will_and_have :
    AcceptableIff Examples.ex_49 (English.Verbs.Verb.Cell.base ∈ formCells set_.realize "set" ∧
        English.Verbs.Verb.Cell.pastParticiple ∈ formCells set_.realize "set") ∧
      AcceptableIff Examples.ex_47
        (English.Verbs.Verb.Cell.base ∈ formCells clarify.realize "clarify" ∧
          English.Verbs.Verb.Cell.pastParticiple ∈ formCells clarify.realize "clarify") ∧
      AcceptableIff Examples.ex_48
        (English.Verbs.Verb.Cell.base ∈ formCells clarify.realize "clarified" ∧
          English.Verbs.Verb.Cell.pastParticiple ∈ formCells clarify.realize "clarified") := by
  decide

-- (54), (56)
theorem zibomvu_genders :
    formCells Xhosa.Gender.plSubjPrefix "zi" = {Xhosa.Gender.genderD, .genderE} := by
  decide

-- (54), (56), (53)
theorem xhosa_coordination :
    AcceptableIff Examples.ex_54
        (Distributes (· ∈ formCells Xhosa.Gender.plSubjPrefix "zi")
          {Xhosa.Gender.genderD, .genderE}) ∧
      AcceptableIff Examples.ex_53a (Distributes (fun g : Xhosa.Gender ↦ g.pluralClass = .cl6)
          {Xhosa.Gender.genderC, .genderD}) ∧
      AcceptableIff Examples.ex_53b (Distributes (fun g : Xhosa.Gender ↦ g.pluralClass = .cl8)
          {Xhosa.Gender.genderC, .genderD}) := by
  decide

open Chichewa.Gender in
-- (57), (59)
theorem chichewa_coordination :
    AcceptableIff Examples.ex_57
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {lalanje.gender, samba.gender}) ∧
      AcceptableIff Examples.ex_58
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {mphaka.gender, galu.gender}) ∧
      AcceptableIff Examples.ex_59
        (Distributes (· ∈ formCells Value.plSubjPrefix .a) {mphaka.gender, lalanje.gender}) := by
  decide

open German.Verbs in
-- (62), (65)
theorem kaufen_cells :
    formCells kaufen (some "kaufen") = {(Person.first, Number.plural), (.third, .plural)} ∧
      formCells kaufen (some "kauft") = {(Person.second, Number.plural), (.third, .singular)} := by
  decide

open German.Verbs in
-- (61), (63), (64)
theorem right_node_raising :
    AcceptableIff Examples.ex_61 (Distributes (· ∈ formCells kaufen (some "kaufen"))
        {(Person.first, Number.plural), (.third, .plural)}) ∧
      AcceptableIff Examples.ex_64 (Distributes (· ∈ formCells kaufen (some "kauft"))
        {(Person.second, Number.plural), (.third, .singular)}) := by
  decide

/-! ### Person resolution (§6) -/

/-- A person value as a set of markers, the paper's S and H the two discourse roles (§6.1). -/
abbrev PersonSet := Finset Discourse.Role

-- §6.3
theorem card_personSet : Fintype.card PersonSet = 4 := by
  rw [Fintype.card_finset, Discourse.Role.card]; rfl

/-- The marker set of a person value is the largest participant set it covers: the single set
of a quadripartition value (87), and the inclusive's `{S,H}` for the first person unmarked for
clusivity, which makes only the attested distinctions (91). -/
def markers (p : Person) : PersonSet := p.participantSets.sup id

@[simp] theorem markers_bot : markers ⊥ = ∅ := rfl

/-- Union of marker sets is the join of persons, the resolution of Zwicky's hierarchy (§6). -/
@[simp] theorem markers_sup (p q : Person) : markers (p ⊔ q) = markers p ∪ markers q := by
  revert p q; decide

theorem markers_finset_sup (s : Finset Person) : markers (s.sup id) = s.sup markers :=
  Finset.apply_sup_eq_sup_comp markers markers_sup markers_bot

/-- The conjuncts of the paper's coordinations by person. -/
def personConjuncts : List (String × List Person) :=
  [("3SG and 1SG", [.third, .first]), ("1SG and 2SG", [.first, .second]),
    ("3SG and 2SG", [.third, .second]), ("2 and 3", [.second, .third]),
    ("3 and 3", [.third, .third]), ("2 and 1", [.second, .firstExclusive]),
    ("2, 3 and 1", [.second, .third, .firstExclusive]), ("3 and 1", [.third, .firstExclusive]),
    ("3 and 1EXCL", [.third, .firstExclusive])]

/-- The agreement forms of the paper's coordinations by person. -/
def personAgreement : List (String × Person) :=
  [("1PL", .first), ("2PL", .second), ("2", .second), ("3", .third),
    ("1INCL.PL", .firstInclusive), ("1EXCL.PL", .firstExclusive)]

-- (71), (76), (81), (86), (88), (92), (95), (99)
theorem person_rows : ∀ row ∈ Examples.all, ∀ cs ∈ row.parse? "conjuncts" personConjuncts,
    ∀ p ∈ row.parse? "agreement" personAgreement,
      (row.judgment = .acceptable ↔ cs.toFinset.sup markers = markers p) := by
  decide +kernel

-- (95), (98)
theorem jose_y_tu : [Person.third, .second].toFinset.sup markers ≠ markers .first := by
  decide

-- fn. 12
theorem markers_subset_iff_prominence : ∀ s t : PersonSet,
    markers (Person.tripartitionOf t) ⊆ markers (Person.tripartitionOf s) ↔
      (Person.tripartitionOf t).prominence ≤ (Person.tripartitionOf s).prominence := by
  decide

/-- The dual assignment, each marker set's complement, its markers read as absences ((102)). -/
def dual (p : Person) : PersonSet := (markers p)ᶜ

-- (100)
theorem dual_tripartition :
    dual .first = ∅ ∧ dual .second = {.speaker} ∧ dual .third = {.speaker, .addressee} := by
  decide

-- (101), (103)
theorem inf_dual (s : Finset Person) : s.inf dual = (s.sup markers)ᶜ :=
  (Finset.compl_sup s markers).symm

-- (101), (103)
theorem dual_first_absorbs :
    dual .first ∩ dual .second = dual .first ∩ dual .third ∧
      dual .firstExclusive ∩ dual .second ≠ dual .firstExclusive ∩ dual .third := by
  decide

/-! ### Gender resolution (§7) -/

/-- Gender markers; each language assigns its genders sets of them. -/
inductive GenderMarker where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- A gender value as a set of markers. -/
abbrev GenderSet := Finset GenderMarker

section Union

variable {G : Type*} [DecidableEq G] {rs : List (Agreement.ResolutionRule G G)}

private theorem of_sublists {univ : List G} {P : Option G → Finset G → Prop}
    (h : ∀ l ∈ univ.sublists, l ≠ [] → P (resolve rs l) l.toFinset) {cs : List G}
    (hcs : cs ≠ []) (hu : ∀ c ∈ cs, c ∈ univ) : P (resolve rs cs) cs.toFinset := by
  have hmem : ∀ c, c ∈ univ.filter (· ∈ cs) ↔ c ∈ cs := fun c ↦ by
    simpa using fun hc ↦ hu c hc
  have hne : univ.filter (· ∈ cs) ≠ [] := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hcs
    exact List.ne_nil_of_mem ((hmem c).2 hc)
  have := h _ (List.mem_sublists.2 List.filter_sublist) hne
  rwa [resolve_congr rs hmem,
    show (univ.filter (· ∈ cs)).toFinset = cs.toFinset from
      Finset.ext fun c ↦ by simp only [List.mem_toFinset, hmem]]
    at this

-- (105b)
private theorem pair_self_of_union {mark : G → GenderSet} {g : G}
    (h : (resolve rs [g, g]).map mark = some ([g, g].toFinset.sup mark))
    (hinj : ∀ g' ∈ rs.map out, mark g' = mark g → g' = g) : resolve rs [g, g] = some g := by
  obtain ⟨g', hg', hm⟩ := Option.map_eq_some_iff.mp h
  rw [hg', hinj g' (mem_map_out_of_resolve_eq_some hg') (by simpa using hm)]

end Union

namespace Hindi

/-- The Hindi genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- Corbett's Hindi rules (109): masculine if a conjunct is, feminine otherwise. -/
def rules : List (Agreement.ResolutionRule Value Value) := [.any (· = .masc) .masc, otherwise .fem]

/-- The marker assignment (111). -/
def markers : Value → GenderSet
  | .masc => {.masc}
  | .fem => ∅

theorem markers_injective : Function.Injective markers := by decide

/-- Union of the marker sets reproduces Corbett's rules on every coordination ((112)). -/
theorem map_resolve {cs : List Value} (hcs : cs ≠ []) :
    (resolve rules cs).map markers = some (cs.toFinset.sup markers) :=
  of_sublists (univ := [.masc, .fem]) (P := fun r s ↦ r.map markers = some (s.sup markers))
    (by decide) hcs fun c _ ↦ by cases c <;> simp

-- (105b), (110)
theorem resolve_pair_self (g : Value) : resolve rules [g, g] = some g :=
  pair_self_of_union (map_resolve (by simp)) fun _ _ h ↦ markers_injective h

-- (105c), (110)
theorem markers_fem_subset : markers .fem ⊆ markers .masc := by decide

end Hindi

namespace Icelandic

/-- The marker assignment (119). -/
def markers : _root_.Icelandic.Gender.Value → GenderSet
  | .masculine => {.masc}
  | .feminine => {.fem}
  | .neuter => {.masc, .fem}

theorem markers_injective : Function.Injective markers := by decide

/-- Union of the marker sets reproduces Corbett's rules on every coordination ((120)) ((119)). -/
theorem map_resolve {cs : List _root_.Icelandic.Gender.Value} (hcs : cs ≠ []) :
    (resolve Corbett1991.Icelandic.rules cs).map markers = some (cs.toFinset.sup markers) :=
  of_sublists (univ := [.masculine, .feminine, .neuter])
    (P := fun r s ↦ r.map markers = some (s.sup markers)) (by decide) hcs
    fun c _ ↦ by cases c <;> simp

-- (105b), (118)
theorem resolve_pair_self (g : _root_.Icelandic.Gender.Value) :
    resolve Corbett1991.Icelandic.rules [g, g] = some g :=
  pair_self_of_union (map_resolve (by simp)) fun _ _ h ↦ markers_injective h

-- (105c), (119)
theorem needs_neuter :
    ¬ markers .masculine ⊆ markers .feminine ∧ ¬ markers .feminine ⊆ markers .masculine ∧
      markers .masculine ∪ markers .feminine = markers .neuter := by
  decide

end Icelandic

namespace Slovene

/-- The marker assignment (122). -/
def markers : Corbett1991.Slovene.Value → GenderSet
  | .masc => {.fem, .neut}
  | .fem => {.fem}
  | .neut => {.neut}

/-- With the conjunction contributing the feminine marker (126), union of the marker sets
reproduces Corbett's rules on every coordination ((127)). -/
theorem map_resolve {cs : List Corbett1991.Slovene.Value} (hcs : cs ≠ []) :
    (resolve Corbett1991.Slovene.rules cs).map markers = some (cs.toFinset.sup markers ∪ {.fem}) :=
  of_sublists (univ := [.masc, .fem, .neut])
    (P := fun r s ↦ r.map markers = some (s.sup markers ∪ {.fem})) (by decide) hcs
    fun c _ ↦ by cases c <;> simp

-- (105b), (123)
theorem neuters :
    resolve Corbett1991.Slovene.rules [.neut, .neut] = some .masc ∧
      [Corbett1991.Slovene.Value.neut, .neut].toFinset.sup markers = markers .neut := by
  decide

end Slovene

-- (107), (108), (113)
theorem hindi_rows : ∀ row ∈ Examples.all, row.language = "hind1269" →
    ∀ cs ∈ row.parse? "conjuncts"
      [("MASC and FEM", [Hindi.Value.masc, .fem]), ("FEM and FEM", [.fem, .fem])],
    ∀ g ∈ row.parse? "agreement" [("MASC", Hindi.Value.masc), ("FEM", .fem)],
      (row.judgment = .acceptable ↔ cs.toFinset.sup Hindi.markers = Hindi.markers g) := by
  decide +kernel

-- (115), (117)
theorem icelandic_rows : ∀ row ∈ Examples.all, row.language = "icel1247" →
    ∀ cs ∈ row.parse? "conjuncts"
      [("MASC and FEM", [_root_.Icelandic.Gender.Value.masculine, .feminine]),
        ("MASC and NEUT", [.masculine, .neuter]), ("FEM and NEUT", [.feminine, .neuter])],
    ∀ g ∈ row.parse? "agreement" [("NEUT", _root_.Icelandic.Gender.Value.neuter)],
      (row.judgment = .acceptable ↔ cs.toFinset.sup Icelandic.markers = Icelandic.markers g) := by
  decide +kernel

-- (123), (127)
theorem slovene_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ cs ∈ row.parse? "conjuncts" [("NEUT and NEUT", [Corbett1991.Slovene.Value.neut, .neut])],
    ∀ g ∈ row.parse? "agreement" [("MASC", Corbett1991.Slovene.Value.masc)],
      (row.judgment = .acceptable ↔
        cs.toFinset.sup Slovene.markers ∪ {.fem} = Slovene.markers g) := by
  decide +kernel

/-! ### Resolving features are not indeterminate (§8) -/

/-- Hindi *wah* is masculine or feminine by a wide-scope disjunction of the two genders' marker
sets ((140)); an indeterminate gender would instead be this set of sets, on which union does
not resolve. -/
def wah : Finset GenderSet := {Hindi.markers .masc, Hindi.markers .fem}

-- (141), (128), (113)
theorem wah_examples :
    AcceptableIff Examples.ex_141a (∃ v ∈ wah, v = Hindi.markers .masc) ∧
      AcceptableIff Examples.ex_141b (∃ v ∈ wah, v = Hindi.markers .fem) ∧
      AcceptableIff Examples.ex_128
        (∃ v ∈ wah, v = Hindi.markers .masc ∧ v = Hindi.markers .fem) := by
  decide

end DalrympleKaplan2000
