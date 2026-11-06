module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Agreement.Hierarchy
public import Linglib.Syntax.Agreement.Resolution
public import Linglib.Syntax.Gender.AgreementClasses
public import Linglib.Syntax.Gender.Assignment
public import Linglib.Syntax.Number.Resolve
public import Linglib.Syntax.Person.Lattice
public import Linglib.Fragments.Tamil.Gender
public import Linglib.Fragments.Swahili.Nouns
public import Linglib.Fragments.Afar.Gender
public import Linglib.Fragments.Romanian.Gender
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Fragments.Hausa.Gender
public import Linglib.Fragments.Latin.Gender
public import Linglib.Fragments.Icelandic.Nouns
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Romance.French.Gender
public import Linglib.Fragments.Slavic.Serbian.Gender
public import Linglib.Data.Examples.Corbett1991
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Corbett (1991): Gender

A language's genders are its agreement classes, assigned to nouns by ordered rules that read
meaning or form, never form alone; German diminutives put [a formal rule before the semantic
one](##German.not_semanticFirst). Hybrid nouns take semantic agreement more readily down the
Agreement Hierarchy ([Table 8.1](##hybrids_respectHierarchy)), and in coastal Bantu [semantic
agreement spreads up it stage by stage](##BantuStage.respectsHierarchy). Coordinations resolve
by ordered rules reading the conjuncts' person, meaning or gender, and Serbo-Croat moves from
syntactic to semantic resolution through [a stage varying between the
two](##SerboCroat.stage2_map_resolve), [conditioned by meaning, not
declension](##SerboCroat.not_morphological).

## Implementation notes

* Assignment systems, agreement classes, the hierarchy and resolution rules are the substrate's.
  Rules read a language's fragment nouns or genders where there is a fragment; Lak, Slovene and
  Ojibwa have study-local genders.
* A hybrid records the availability of semantic agreement only where the book reports it;
  §8.3 divides the attributive position into the possessive and the rest (`FinePosition`).
* Number resolution counts the conjuncts, which no resolution rule can
  (`Slovene.numberResolve_ne_resolve`), so it is stated directly and matched to the substrate's
  `Number.System.resolve`.
* Not modelled: chapters 4, 5, 7 and 10, Russian acronyms and indeclinables, and the optional
  Polish resolution rules, which are rows only.

## TODO

* Subgenders and consistent agreement patterns, which want chapter 6's paradigm tables in the
  Russian fragment.
* §9.8: resolution is never less semantic than assignment.
* §9.6.2: resolved forms are the semantically justified ones that mark number clearly, which
  excludes the Slovene neuter.

## References

* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett, *The agreement hierarchy* (1979)][corbett-1979]
* [G. G. Corbett, *Hierarchies, Targets and Controllers* (1983)][corbett-1983]
* [A. A. Zaliznjak, *K voprosu o grammatičeskix kategorijax roda i oduševlennosti*
  (1964)][zaliznjak-1964]
* [J. H. Greenberg, *Some universals of grammar* (1963)][greenberg-1963]
* [C. F. Hockett, *A Course in Modern Linguistics* (1958)][hockett-1958]
* [B. Heine, *African noun class systems* (1982)][heine-1982]
* [T. Givón, *The resolution of gender conflicts in Bantu conjunction* (1970)][givon-1970]
* [R. M. W. Dixon, *The Dyirbal Language of North Queensland* (1972)][dixon-1972]
* [G. R. Tucker, W. E. Lambert, A. A. Rigault, *The French Speaker's Skill with Grammatical
  Gender* (1977)][tucker-lambert-rigault-1977]
-/

@[expose] public section

namespace Corbett1991

open Agreement Agreement.ResolutionRule

/-! ### Assignment systems -/

/-- A semantic opposition on which gender assignment can rest (§2.3) is one of de la
Grasserie's types or of the criteria the book adds. Sex is one opposition here, though the book
separates systems singling out females (Diyari, Dizi) from those singling out males (Kala Lagaw
Ya). -/
inductive Criterion where
  | animacy
  | rationality
  | humanness
  | sex
  | strength
  | size
  | evaluation
  | insect
  | edibility
  | liquidity
  | abstractness
  | canine
  | huntingWeapon
  | lustre
  deriving DecidableEq, Repr, Fintype

/-- The book's typology of assignment systems. -/
inductive AssignmentKind where
  | strictSemantic
  | predominantlySemantic
  | morphological
  | phonological
  deriving DecidableEq, Repr, Fintype

/-- A language of chapters 2 and 3 with the kind of its assignment system and the semantic
criteria its rules use, as this study reads the book's tables; the book draws up no such
list itself. -/
structure SurveyEntry where
  /-- The language. -/
  glottocode : Glottocode
  /-- The kind of assignment system the book describes. -/
  kind : AssignmentKind
  /-- The semantic criteria the book's rules for the language use. -/
  criteria : List Criterion
  deriving DecidableEq, Repr

/-- The assignment systems of chapters 2 and 3 (Tables 2.1 to 2.8 and §3.1 to §3.2). -/
def survey : List SurveyEntry :=
  [⟨.tamil, .strictSemantic, [.rationality, .sex]⟩,
    ⟨.dieri, .strictSemantic, [.sex]⟩,
    ⟨.dizin, .strictSemantic, [.sex, .evaluation]⟩,
    ⟨.halkomelem, .strictSemantic, [.sex, .evaluation]⟩,
    ⟨.defaka, .strictSemantic, [.humanness, .sex]⟩,
    ⟨.english, .strictSemantic, [.humanness, .sex]⟩,
    ⟨.zande, .predominantlySemantic, [.humanness, .sex, .animacy]⟩,
    ⟨.dyirbal, .predominantlySemantic, [.humanness, .sex, .animacy, .edibility]⟩,
    ⟨.ket, .predominantlySemantic, [.animacy, .sex]⟩,
    ⟨.ojibwa, .predominantlySemantic, [.animacy]⟩,
    ⟨.lak, .predominantlySemantic, [.rationality, .sex, .animacy]⟩,
    ⟨.archi, .predominantlySemantic,
      [.rationality, .sex, .animacy, .size, .abstractness, .insect]⟩,
    ⟨.russian, .morphological, [.sex, .animacy]⟩,
    ⟨.swahili, .morphological, [.animacy, .evaluation]⟩,
    ⟨.afar, .phonological, [.sex]⟩,
    ⟨.hausa, .phonological, [.sex]⟩,
    ⟨.godié, .phonological, [.humanness, .size, .liquidity]⟩,
    ⟨.yimas, .phonological, [.sex, .humanness, .animacy]⟩,
    ⟨.french, .phonological, [.sex]⟩]

/-! ### Tamil: a strict semantic system (§2.1.1) -/

namespace Tamil

open _root_.Tamil.Gender

/-- The rules read rationality and the gender the noun restricts its referents to. -/
def sem (n : Tamil.Gender.Noun) : Bool × Option ReferentGender := (n.rational, n.referentGender)

/-- Table 2.1 makes male rationals masculine, female rationals feminine and the residue
neuter. -/
def system : Gender.AssignmentSystem (Bool × Option ReferentGender) Unit Value where
  rules := [.semantic fun
    | (true, some .male) => some .masc
    | (true, some .female) => some .fem
    | _ => none]
  residue := .neut

theorem isStrictSemantic_system : system.IsStrictSemantic := fun _ ↦ rfl

theorem semanticCore_nonempty : (system.semanticCore sem).Nonempty := ⟨aaN, rfl⟩

theorem assign_eq_gender : ∀ n ∈ allNouns, system.assign sem (fun _ ↦ ()) n = n.gender := by
  decide

end Tamil

/-! ### Russian: a morphological system (§3.1.1) -/

namespace Russian

open _root_.Russian.Gender

/-- The declensional types of Figure 3.1 are the four paradigms and the irregular third. -/
inductive Declension where
  | I
  | II
  | III
  | IV
  | irregularIII
  deriving DecidableEq, Repr, Fintype

/-- Corbett's typing of the fragment's declension classes puts *znamja* and *put'* in the
irregular third declension. -/
def declension (n : Russian.Gender.Noun) : Option Declension :=
  if n = znamja ∨ n = put' then some .irregularIII else
    n.declClass.map fun
      | .I => .I
      | .II => .II
      | .III => .III
      | .IV => .IV

/-- The gender the noun restricts its referents to. -/
def sem (n : Russian.Gender.Noun) : Option ReferentGender := n.referentGender

/-- The rules of §3.1.1 for declinable nouns make males masculine and females feminine, then
declension I masculine, declensions II and III feminine and the rest neuter. The rules for
acronyms and indeclinables (Figure 3.4) are not modelled. -/
def system : Gender.AssignmentSystem (Option ReferentGender) (Option Declension) Value where
  rules := [.semantic (Option.map Value.ofReferentGender), .formal fun
    | some .I => some .masc
    | some .II | some .III => some .fem
    | _ => none]
  residue := .neut

-- p. 41
theorem semanticFirst_system : system.SemanticFirst := ⟨[_], [_], rfl⟩

theorem semanticCore_nonempty : (system.semanticCore sem).Nonempty := ⟨djadja, rfl⟩

theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ put' → system.assign sem declension n = n.gender := by
  decide

theorem djadja_precedence :
    system.formal (declension djadja) = some .fem ∧
      system.assign sem declension djadja = .masc := by
  decide

-- §8.1
theorem vrac_by_declension : system.assign sem declension vrač = .masc := by decide

end Russian

/-! ### Swahili: morphological classes and animate concord (§3.1.2) -/

namespace Swahili

open _root_.Swahili

/-- The semantic rules read evaluative derivation and animacy. -/
def sem (n : Swahili.Noun) : Option Evaluative × Animacy := (n.evaluative, n.animacy)

/-- The augmentative rule sends augmentatives to 5/6. -/
def augmentative : Option Evaluative × Animacy → Option _root_.Swahili.Gender
  | (some .augmentative, _) => some .genderC
  | _ => none

/-- The diminutive rule sends diminutives to 7/8. -/
def diminutive : Option Evaluative × Animacy → Option _root_.Swahili.Gender
  | (some .diminutive, _) => some .genderD
  | _ => none

/-- The animacy rule sends animates to 1/2. -/
def animate : Option Evaluative × Animacy → Option _root_.Swahili.Gender
  | (_, a) => if .animate ≤ a then some .genderA else none

/-- The rules of §3.1.2 send augmentatives to 5/6, diminutives to 7/8 and remaining animates
to 1/2, then each morphological class to its own gender, over the fragment's five genders (the
book's 11/10 and 15 are not among them). The formal rule is total, so the residue gender is
never reached. -/
def system : Gender.AssignmentSystem (Option Evaluative × Animacy) _root_.Swahili.Gender
    _root_.Swahili.Gender where
  rules := [.semantic augmentative, .semantic diminutive, .semantic animate, .formal some]
  residue := .genderE

-- p. 48
theorem semanticFirst_system : system.SemanticFirst := ⟨[_, _, _], [_], rfl⟩

theorem semanticCore_nonempty : (system.semanticCore sem).Nonempty := ⟨kitoto, rfl⟩

theorem assign_eq_gender : ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = n.gender := by
  decide

theorem genderA_semantic :
    ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = .genderA →
      (system.semantic (sem n)).isSome := by
  decide

-- p. 47: the semantic rules apply in their order
theorem animate_first_misassigns :
    let A : Gender.AssignmentSystem _ _root_.Swahili.Gender _root_.Swahili.Gender :=
      { system with rules := [.semantic animate, .semantic augmentative, .semantic diminutive,
          .formal some] }
    A.assign sem Noun.morphClass joka = .genderA ∧ joka.gender = .genderC ∧
      A.assign sem Noun.morphClass kitoto = .genderA ∧ kitoto.gender = .genderD := by
  decide

end Swahili

/-! ### Afar and Hausa: phonological systems (§3.2.1, §3.2.2) -/

namespace Afar

open _root_.Afar.Gender

/-- The gender the noun restricts its referents to. -/
def sem (n : Afar.Gender.Noun) : Option ReferentGender := n.referentGender

/-- The referents' sex first; then a citation form ending in an accented vowel is feminine,
the rest masculine. -/
def system : Gender.AssignmentSystem (Option ReferentGender) Bool Value where
  rules := [.semantic (Option.map Value.ofReferentGender),
    .formal fun acc ↦ if acc then some .fem else none]
  residue := .masc

-- p. 52
theorem semanticFirst_system : system.SemanticFirst := ⟨[_], [_], rfl⟩

theorem semanticCore_nonempty : (system.semanticCore sem).Nonempty := ⟨abba, rfl⟩

theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ doonik → system.assign sem Noun.finalAccentedVowel n = n.gender := by
  decide

theorem abba_precedence :
    system.formal abba.finalAccentedVowel = some .fem ∧
      system.assign sem Noun.finalAccentedVowel abba = .masc := by
  decide

end Afar

namespace Hausa

open _root_.Hausa

/-- The gender the noun restricts its referents to. -/
def sem (n : Hausa.Noun) : Option ReferentGender := n.referentGender

/-- The referents' sex first; then a noun in *-ā* is feminine, the rest masculine. -/
def system : Gender.AssignmentSystem (Option ReferentGender) Bool Gender.Value where
  rules := [.semantic (Option.map Gender.Value.ofReferentGender),
    .formal fun aa ↦ if aa then some .feminine else none]
  residue := .masculine

theorem semanticFirst_system : system.SemanticFirst := ⟨[_], [_], rfl⟩

theorem semanticCore_nonempty : (system.semanticCore sem).Nonempty := ⟨uba, rfl⟩

theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ∉ [gida, kada] →
      system.assign sem (fun n ↦ decide n.EndsInAa) n = n.gender := by
  decide

end Hausa

/-! ### German: a formal rule before the semantic rule (§3.1.3) -/

namespace German

open _root_.German.Gender

/-- The diminutive rule makes a noun in *-chen* or *-lein* neuter. -/
def diminutive : Option Suffix → Option Value
  | some .chen | some .lein => some .neut
  | _ => none

/-- German diminutives are neuter whatever the sex of the referent, *Männchen* 'little man'
(p. 50) and *Mädchen* 'girl'. A system whose semantic rules make females feminine therefore
assigns *Mädchen* its neuter only if its semantic rules do not come first. -/
theorem not_semanticFirst {φ : Type*}
    {A : Gender.AssignmentSystem (Option ReferentGender) φ Value} {form : GenderedNoun Value → φ}
    (hfem : A.semantic (some .female) = some .fem)
    (h : A.assign GenderedNoun.referentGender form maedchen = maedchen.gender) :
    ¬ A.SemanticFirst := fun hA ↦
  absurd ((Gender.AssignmentSystem.assign_of_semantic (n := maedchen) hA hfem).symm.trans h)
    (by decide)

/-- With the diminutive rule before the sex rule, a noun in *-chen* is neuter whatever the sex
of its referents, and the semantic rule still makes females feminine. -/
example : let A : Gender.AssignmentSystem (Option ReferentGender) (Option Suffix) Value :=
      ⟨[.formal diminutive, .semantic (Option.map Value.ofReferentGender)], .masc⟩
    let chen : GenderedNoun Value → Option Suffix := fun _ ↦ some .chen
    A.semantic (some .female) = some .fem ∧
      A.assign GenderedNoun.referentGender chen maedchen = maedchen.gender ∧
      A.assign GenderedNoun.referentGender chen buebchen = buebchen.gender := by
  decide

end German

/-! ### Controller and target genders (chapter 6)

The map between two numbers' target genders is parallel, convergent or crossed, and
[greenberg-1963]'s universal that the plural never distinguishes more genders than the singular
is stated over target genders, since in agreement classes the two numbers are not told apart. -/

namespace Romanian

open _root_.Romanian.Gender

-- Figure 6.1
theorem crossed :
    Gender.Crossed (Value.adjForm · (numberSystem.value .singular))
      (Value.adjForm · (numberSystem.value .plural)) := by
  decide

theorem card_range_adjForm :
    Fintype.card (Set.range Value.adjForm) = 3 ∧
      Fintype.card (Gender.targetGenders Value.adjForm (numberSystem.value .singular)) = 2 ∧
        Fintype.card (Gender.targetGenders Value.adjForm (numberSystem.value .plural)) = 2 := by
  decide

-- (5), (10)
theorem rows : ∀ row ∈ Examples.all, row.language = .romanian →
    ∀ n ∈ row.parse? "noun" (allNouns.map fun n ↦ (n.form, n)),
      ∀ pl ∈ row.parse? "number"
          [("singular", numberSystem.value .singular), ("plural", numberSystem.value .plural)],
        ∀ f ∈ row.parse? "form" [("zero", AdjForm.zero), ("ă", .ă), ("i", .i), ("e", .e)],
          (row.judgment = .acceptable ↔ n.gender.adjForm pl = f) := by
  decide +kernel

end Romanian

namespace German

open _root_.German.Determiners in
-- Figure 6.7
theorem convergent :
    Gender.Convergent (fun g ↦ definite (.sg g) .nom) fun _ ↦ definite .pl .nom := by
  decide

end German

namespace Lak

/-- The four genders of Lak and the three sets of verbal agreement markers of Figure 6.5. -/
inductive Value where
  | I
  | II
  | III
  | IV
  deriving DecidableEq, Repr, Fintype

/-- The three sets of forms are prefixal `Ø`/`b`/`d` and internal or suffixal `w`/`w`/`r`. -/
inductive Marker where
  | zeroW
  | bW
  | dR
  deriving DecidableEq, Repr, Fintype

/-- The singular marker of each gender. -/
def Value.sgMarker : Value → Marker
  | .I => .zeroW
  | .II => .dR
  | .III => .bW
  | .IV => .dR

/-- The plural marker of each gender. -/
def Value.plMarker : Value → Marker
  | .I | .II | .III => .bW
  | .IV => .dR

-- Figure 6.10
theorem crossed : Gender.Crossed Value.sgMarker Value.plMarker := by decide

theorem card_plMarker_le :
    Fintype.card (Set.range Value.plMarker) ≤ Fintype.card (Set.range Value.sgMarker) := by
  decide

end Lak

namespace Slovene

/-- An agreeing predicate's endings for the three genders in the three numbers (Table 9.3) are
parallel between singular and plural and convergent with the dual, where feminine and neuter
share a form (Figure 6.11). -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- The endings of the past active participle. -/
inductive Ending where
  | zero
  | a
  | o
  | i
  | e
  deriving DecidableEq, Repr, Fintype

/-- The singular ending of each gender. -/
def Value.sgEnding : Value → Ending
  | .masc => .zero
  | .fem => .a
  | .neut => .o

/-- The dual ending of each gender. -/
def Value.duEnding : Value → Ending
  | .masc => .a
  | .fem | .neut => .i

/-- The plural ending of each gender. -/
def Value.plEnding : Value → Ending
  | .masc => .i
  | .fem => .e
  | .neut => .a

theorem parallel_sg_pl : Gender.Parallel Value.sgEnding Value.plEnding := by decide

theorem convergent_sg_du : Gender.Convergent Value.sgEnding Value.duEnding := by decide

theorem convergent_pl_du : Gender.Convergent Value.plEnding Value.duEnding := by decide

end Slovene

namespace Tamil

open _root_.Tamil.Gender

-- Figure 6.8
theorem convergent : Gender.Convergent Value.sgConcord Value.plConcord := by decide

theorem card_plConcord_lt :
    Nat.card (Set.range Value.plConcord) < Nat.card (Set.range Value.sgConcord) :=
  convergent.card_range_lt

end Tamil

/-! ### Hybrid nouns and the Agreement Hierarchy (chapter 8)

The hybrids of Table 8.1 and the English boat nouns of §6.4.5, each as the availability of
semantic agreement at the positions for which the book has data. -/

/-- French titles such as *Sa Sainteté*: feminine throughout, a masculine personal pronoun
less often. -/
def frenchTitles : Hybrid Position := fun
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic

/-- German *Mädchen* 'girl': neuter, the personal pronoun neuter or feminine; the predicate
shows no gender. -/
def madchen : Hybrid Position := fun
  | .attributive | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | .predicate => none

/-- Spoken Polish *łajdaki* 'wretches': non-masculine personal except for a masculine personal
personal pronoun. -/
def lajdaki : Hybrid Position := fun
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .semanticOnly

/-- Spanish titles: a feminine attributive, masculine elsewhere. -/
def spanishTitles : Hybrid Position := fun
  | .attributive => some .syntacticOnly
  | .predicate | .relativePronoun | .personalPronoun => some .semanticOnly

/-- Konkani nouns denoting young females: a feminine attributive, neuter elsewhere; the relative
pronoun is not available. -/
def konkani : Hybrid Position := fun
  | .attributive => some .syntacticOnly
  | .predicate | .personalPronoun => some .semanticOnly
  | .relativePronoun => none

/-- Russian *vrač* 'doctor' denoting a woman: the attributive masculine and less often feminine,
the predicate either, the pronouns feminine and less often masculine. -/
def vrac : Hybrid Position := fun
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun | .personalPronoun => some .mostlySemantic

/-- Serbo-Croat plural *gazde* 'landlords': the attributive feminine and less often masculine,
the predicate either, the relative pronoun mostly and the personal pronoun only masculine. -/
def gazde : Hybrid Position := fun
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun => some .mostlySemantic
  | .personalPronoun => some .semanticOnly

/-- English boat nouns (§6.4.5): the relative pronoun *which*, the personal pronoun *she* or
*it*. -/
def boat : Hybrid Position := fun
  | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | _ => none

/-- The hybrids by the names the rows use. -/
def hybridNames : List (String × Hybrid Position) :=
  [("frenchTitles", frenchTitles),
    ("mädchen", madchen),
    ("łajdaki", lajdaki),
    ("spanishTitles", spanishTitles),
    ("konkani", konkani),
    ("vrač", vrac),
    ("gazde", gazde),
    ("boat", boat)]

/-- Every hybrid of Table 8.1, and the English boat nouns, respect the Agreement Hierarchy. -/
theorem hybrids_respectHierarchy : ∀ h ∈ hybridNames, RespectsHierarchy h.2 := by decide

/-- At the corpus level, 16.9 per cent of 3,835 of Panov's respondents favour feminine
agreement with *vrač* for the attributive and 51.7 per cent of 3,806 for the predicate. -/
def vracFeminine : Position → Option ℚ
  | .attributive => some (169 / 1000)
  | .predicate => some (517 / 1000)
  | _ => none

theorem vracFeminine_respectsHierarchy : RespectsHierarchy vracFeminine := by decide +kernel

/-! ### The spread of semantic agreement in Bantu (§8.3)

Bantu nouns denoting animates outside gender 1/2 lose their syntactic agreement in stages,
attested side by side in neighbouring languages, and the last stages treat the attributive
possessive apart from the other attributive modifiers, a finer division of the hierarchy. -/

/-- The positions of the hierarchy with the attributive divided into the possessive and the
other attributive modifiers, the possessive above them. -/
inductive FinePosition where
  | possessive
  | attributive
  | predicate
  | relativePronoun
  | personalPronoun
  deriving DecidableEq, Repr, Fintype

namespace FinePosition

/-- The rank of a fine position, the possessive on top. -/
def rank : FinePosition → ℕ
  | .possessive => 4
  | .attributive => 3
  | .predicate => 2
  | .relativePronoun => 1
  | .personalPronoun => 0

theorem rank_injective : Function.Injective rank := by decide

instance : LinearOrder FinePosition := LinearOrder.lift' rank rank_injective

/-- The position of the hierarchy a fine position divides. -/
def toPosition : FinePosition → Position
  | .possessive | .attributive => .attributive
  | .predicate => .predicate
  | .relativePronoun => .relativePronoun
  | .personalPronoun => .personalPronoun

theorem toPosition_monotone : Monotone toPosition := by decide

end FinePosition

/-- The stages of the change, from its beginning in Chichewa, where only a personal pronoun far
from *kamwana* 'small child' may take gender 1/2, through Kimbundu, where semantic agreement is
possible except in attributive position, Chonyi, where it reaches the attributive, Kami, where
it is obligatory in the predicate, and urban Swahili, where it is obligatory except on an
attributive possessive, to Bondei, where it is obligatory everywhere. -/
inductive BantuStage where
  | chichewa
  | kimbundu
  | chonyi
  | kami
  | urbanSwahili
  | bondei
  deriving DecidableEq, Repr, Fintype

namespace BantuStage

instance : LinearOrder BantuStage := LinearOrder.lift' BantuStage.ctorIdx (by decide)

/-- The availability of semantic agreement at each stage, where the book reports it:
*kamwana* in Chichewa, (40) to (44); *kilumba* 'girl' in Kimbundu, (52) and (53); Kami
*ng'ombe* 'cows' and *mbudzi* 'goats', (54) and (55), the possessive reported with class 10
agreement only; Swahili *rafiki* 'friend', (47) to (49). -/
def hybrid : BantuStage → Hybrid FinePosition
  | chichewa => fun
    | .possessive => none
    | .personalPronoun => some .mostlySyntactic
    | _ => some .syntacticOnly
  | kimbundu => fun
    | .attributive => some .syntacticOnly
    | .predicate => some .both
    | _ => none
  | chonyi => fun
    | .attributive | .predicate => some .both
    | _ => none
  | kami => fun
    | .possessive => some .syntacticOnly
    | .attributive => some .both
    | .predicate => some .semanticOnly
    | _ => none
  | urbanSwahili => fun
    | .possessive => some .both
    | _ => some .semanticOnly
  | bondei => fun _ ↦ some .semanticOnly

open OrderDual in
/-- Semantic agreement spreads up the Agreement Hierarchy: of two positions at two stages, the
higher position at the earlier stage is never the more open to semantic agreement. -/
theorem respectsHierarchy :
    RespectsHierarchy fun p : BantuStageᵒᵈ × FinePosition ↦ (ofDual p.1).hybrid p.2 := by
  decide

open OrderDual in
theorem hybrid_respectsHierarchy (s : BantuStage) : RespectsHierarchy s.hybrid :=
  respectsHierarchy.comp_monotone (g := fun i ↦ (toDual s, i)) fun _ _ h ↦ ⟨le_rfl, h⟩

open OrderDual in
theorem hybrid_monotone (i : FinePosition) :
    RespectsHierarchy fun s : BantuStageᵒᵈ ↦ (ofDual s).hybrid i :=
  respectsHierarchy.comp_monotone (g := fun s ↦ (s, i)) fun _ _ h ↦ ⟨h, le_rfl⟩

end BantuStage

/-! ### The judgments of chapter 8

A row with a `hybrid`, a `target` and an `agreement` feature is a use of a hybrid noun at a
position of the hierarchy, acceptable exactly when the hybrid's availability there admits
the agreement. A row with `near` and `far` features is a pair of stacked or parallel targets of
one controller; by the constraints of §8.1.2 the further shows semantic agreement when the two
differ, so the agreement never decreases with distance from the controller. -/

/-- The positions of the hierarchy by the names the rows use. -/
def positionNames : List (String × Position) :=
  [("attributive", .attributive), ("predicate", .predicate),
    ("relativePronoun", .relativePronoun), ("personalPronoun", .personalPronoun)]

/-- The fine positions by the names the rows use. -/
def finePositionNames : List (String × FinePosition) :=
  [("attributivePossessive", .possessive), ("attributive", .attributive),
    ("predicate", .predicate), ("relativePronoun", .relativePronoun),
    ("personalPronoun", .personalPronoun)]

/-- The stages by the hybrids whose names the rows use. -/
def stageNames : List (String × BantuStage) :=
  [("kamwana", .chichewa), ("kilumba", .kimbundu), ("ng'ombe", .kami), ("mbudzi", .kami),
    ("rafiki", .urbanSwahili)]

/-- The two agreements by the names the rows use. -/
def kindNames : List (String × Kind) := [("syntactic", .syntactic), ("semantic", .semantic)]

theorem hybrid_rows : ∀ row ∈ Examples.all, ∀ h ∈ hybridNames, row.feature? "hybrid" = some h.1 →
    ∀ t ∈ row.parse? "target" positionNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.2 t, a.Allows k) := by
  decide +kernel

theorem stage_rows : ∀ row ∈ Examples.all, ∀ s ∈ stageNames, row.feature? "hybrid" = some s.1 →
    ∀ t ∈ row.parse? "target" finePositionNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ s.2.hybrid t, a.Allows k) := by
  decide +kernel

-- Table 8.1, §8.3
theorem hybrid_rows_covered : ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "hybrid",
    (n ∈ hybridNames.map Prod.fst ∨ n ∈ stageNames.map Prod.fst) ∧
      ∀ t ∈ row.feature? "target", t ∈ finePositionNames.map Prod.fst := by
  decide +kernel

theorem stacked_rows : ∀ row ∈ Examples.all, ∀ near ∈ row.parse? "near" kindNames,
    ∀ far ∈ row.parse? "far" kindNames, (row.judgment = .acceptable ↔ near ≤ far) := by
  decide +kernel

/-! ### Resolution (chapter 9) -/

/-- The person resolution rules of §9.1.1, Czech's and claimed universal, give the first
person if a conjunct is first person, else the second if one is second, else the third. -/
def personRules : List (ResolutionRule Person Person) :=
  [.any (· = .first) .first, .any (· = .second) .second, otherwise .third]

theorem resolve_personRules_pair :
    ∀ a ∈ [Person.first, .second, .third], ∀ b ∈ [Person.first, .second, .third],
      resolve personRules [a, b] = some (a ⊔ b).coarsen := by
  decide

/-- By the number resolution rules of §9.1.2, two singular conjuncts alone take the dual where
the system has one, any other coordination with a non-plural conjunct takes the plural, and one
of plurals alone resolves nothing, so that gender resolution is not triggered. -/
def numberResolve (ns : Number.System) (cs : List Number) : Option Number :=
  if .dual ∈ ns.values ∧ cs = [.singular, .singular] then some .dual
  else if ∀ c ∈ cs, c = .plural then none else some .plural

namespace Tamil

open _root_.Tamil.Gender

/-- Whether a gender is one of the rational genders. -/
def Rational : Value → Prop := (· ≠ .neut)

instance : DecidablePred Rational := fun v ↦ inferInstanceAs (Decidable (v ≠ .neut))

/-- By §9.3, all rationals take the rational form and all non-rationals the neuter, and a
mixture has no resolved form. -/
def rules : List (ResolutionRule Value PlConcord) :=
  [.all Rational .rational, .all (¬ Rational ·) .neuter]

-- (16)
theorem resolve_masc_fem : resolve rules [.masc, .fem] = some .rational := by decide

-- (18)
theorem resolve_masc_neut : resolve rules [.masc, .neut] = none := by decide

theorem resolve_factorsThrough :
    Function.FactorsThrough (resolve rules) (List.map (decide <| Rational ·)) :=
  ResolutionRule.resolve_factorsThrough fun r hr a b h ↦ by
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [pred, decide_eq_decide.mp h]

end Tamil

namespace Archi

/-- The plural target genders are I/II for rationals and III/IV for the rest
(Figure 6.12). -/
inductive PlForm where
  | I_II
  | III_IV
  deriving DecidableEq, Repr, Fintype

/-- By §9.3, a conjunct denoting a rational brings gender I/II and any other III/IV; the
descriptor is rationality, so *xalq'* 'people' resolves by what it denotes. -/
def rules : List (ResolutionRule Bool PlForm) := [.any (· = true) .I_II, otherwise .III_IV]

theorem resolve_rational_nonrational : resolve rules [true, false] = some .I_II := by decide

end Archi

namespace Luganda

/-- The resolved forms are the class 2 and class 8 markers. -/
inductive PlForm where
  | cl2
  | cl8
  deriving DecidableEq, Repr, Fintype

/-- By §9.3, all humans take class 2, no humans class 8, and a mixture class 8 if resolution
is forced at all. -/
def rules : List (ResolutionRule Bool PlForm) :=
  [.all (· = true) .cl2, .all (· = false) .cl8, otherwise .cl8]

end Luganda

namespace French

open _root_.French.Gender

/-- The type-A rules of §9.4 give the masculine if a conjunct is masculine and the feminine
otherwise. -/
def rulesA : List (ResolutionRule Value Value) :=
  [.any (· = .masculine) .masculine, otherwise .feminine]

/-- The type-B rules give the feminine if all conjuncts are feminine and the masculine
otherwise. -/
def rulesB : List (ResolutionRule Value Value) :=
  [.all (· = .feminine) .feminine, otherwise .masculine]

-- p. 280
theorem resolve_rulesA_eq_rulesB (cs : List Value) : resolve rulesA cs = resolve rulesB cs :=
  resolve_any_otherwise fun c ↦ by cases c <;> decide

end French

namespace Slovene

/-- The numbers of Slovene. -/
def numbers : Number.System := { values := {.singular, .dual, .plural} }

theorem resolve_numbers :
    ∀ a b, numbers.resolve a b = if a = .singular ∧ b = .singular then .dual else .plural := by
  decide

-- p. 264
theorem numberResolve_eq_resolve (c d : Number) (cs : List Number)
    (h : ∃ x ∈ c :: d :: cs, x ≠ .plural) :
    numberResolve numbers (c :: d :: cs) = some ((d :: cs).foldl numbers.resolve c) := by
  have hpl : ∀ l : List Number, l.foldl numbers.resolve .plural = .plural := fun l ↦ by
    induction l with
    | nil => rfl
    | cons x l ih => simpa [resolve_numbers] using ih
  have hall : ¬ ∀ x ∈ c :: d :: cs, x = .plural := fun hp ↦ by
    obtain ⟨x, hx, hne⟩ := h; exact hne (hp x hx)
  by_cases hsg : c = .singular ∧ d = .singular ∧ cs = []
  · obtain ⟨rfl, rfl, rfl⟩ := hsg
    rfl
  · rw [numberResolve, ite_eq_right (by simp [numbers]; tauto), ite_eq_right hall, List.foldl_cons,
      resolve_numbers]
    rcases cs with _ | ⟨x, cs⟩
    · simp_all
    · split_ifs <;> simp [resolve_numbers, hpl]

theorem numberResolve_ne_resolve (rs : List (ResolutionRule Number Number)) :
    numberResolve numbers ≠ resolve rs := fun h ↦ by
  have := congrFun h [.singular, .singular]
  rw [resolve_congr rs (ds := [.singular, .singular, .singular]) (by simp), ← congrFun h] at this
  exact absurd this (by decide)

/-- By §9.4, all feminines take the feminine and anything else the masculine, a type-B system
in which the neuter never results from resolution. -/
def rules : List (ResolutionRule Value Value) := [.all (· = .fem) .fem, otherwise .masc]

-- (52)
theorem resolve_neuters :
    resolve rules [.neut, .neut, .neut] = some .masc ∧
      numberResolve numbers [.singular, .singular, .singular] = some .plural := by
  decide

theorem resolve_ne_neut (cs : List Value) : resolve rules cs ≠ some .neut := fun h ↦ by
  simpa [rules] using mem_map_out_of_resolve_eq_some h

end Slovene

namespace Icelandic

/-- By §9.4, homogeneous masculines or feminines keep their gender and any mixture takes the
neuter, the semantically justified gender for beings of both sexes; the rules are syntactic,
reading the conjuncts' genders. -/
def rules : List (ResolutionRule _root_.Icelandic.Gender.Value _root_.Icelandic.Gender.Value) :=
  [.all (· = .masculine) .masculine, .all (· = .feminine) .feminine, otherwise .neuter]

end Icelandic

namespace Latin

open _root_.Latin.Gender

/-- A conjunct is described by its gender and the animacy of its referent. -/
abbrev Conjunct := Value × Animacy

/-- §9.5 has two syntactic rules for homogeneous genders, a semantic rule for humans, and the
neuter otherwise. -/
def rules : List (ResolutionRule Conjunct Value) :=
  [.all (·.1 = .masc) .masc, .all (·.1 = .fem) .fem, .all (·.2 = .human) .masc,
    otherwise .neut]

end Latin

namespace Polish

/-- The plural agreement forms. -/
inductive PlForm where
  | mascPers
  | nonMascPers
  deriving DecidableEq, Repr, Fintype

/-- The obligatory rules of §9.5 give the masculine personal if a conjunct is masculine
personal and the non-masculine personal otherwise. The optional rules of (60) to (62) are rows
only. -/
def rules : List (ResolutionRule Bool PlForm) :=
  [.any (· = true) .mascPers, otherwise .nonMascPers]

end Polish

namespace Romanian

open _root_.Romanian.Gender

/-- Whether a noun denotes a male animate. -/
def MaleAnimate (n : Romanian.Gender.Noun) : Prop :=
  .animate ≤ n.animacy ∧ n.referentGender = some .male

instance : DecidablePred MaleAnimate := fun _ ↦ by unfold MaleAnimate; infer_instance

/-- Collapsed over the fragment's nouns, §9.5 gives the masculine if a conjunct is a male
animate or all are masculine, and the feminine otherwise. -/
def rules : List (ResolutionRule Romanian.Gender.Noun Value) :=
  [.any MaleAnimate .masc, .all (·.gender = .masc) .masc, otherwise .fem]

-- (69)
theorem resolve_perete_scaun : resolve rules [perete, scaun] = some .fem := by decide

end Romanian

namespace SerboCroat

open _root_.Serbian.Gender

/-! #### From syntactic to semantic resolution (§9.7)

A conjunct is a fragment noun, read for its gender by a syntactic rule and for the sex of its
referents by a semantic one. -/

/-- Stage 1, as still in Slovene: the feminine if all conjuncts are feminine, else the
masculine. -/
def stage1 : List (ResolutionRule (GenderedNoun Value) Value) :=
  [.all (·.gender = .feminine) .feminine, otherwise .masculine]

/-- Stage 3, hypothetical: the feminine if all conjuncts denote females, else the masculine. -/
def stage3 : List (ResolutionRule (GenderedNoun Value) Value) :=
  [.all (·.referentGender = some .female) .feminine, otherwise .masculine]

/-- Stage 2, present Serbo-Croat in the book's alternative formulation: the feminine if all
conjuncts denote females, optionally the feminine if all are feminine, else the masculine. The
two grammars apply the optional rule and pass it over. -/
def stage2 : List (List (ResolutionRule (GenderedNoun Value) Value)) :=
  [[.all (·.referentGender = some .female) .feminine, .all (·.gender = .feminine) .feminine,
      otherwise .masculine],
    [.all (·.referentGender = some .female) .feminine, otherwise .masculine]]

theorem stage1_factorsThrough :
    Function.FactorsThrough (resolve stage1) (List.map (·.gender)) :=
  ResolutionRule.resolve_factorsThrough fun r hr a b h ↦ by
    simp only [stage1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [pred, otherwise, h]

theorem stage3_factorsThrough :
    Function.FactorsThrough (resolve stage3) (List.map (·.referentGender)) :=
  ResolutionRule.resolve_factorsThrough fun r hr a b h ↦ by
    simp only [stage3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [pred, otherwise, h]

/-- Where nouns denoting females are feminine, as the semantic assignment rule makes them, the
grammars of stage 2 are those of stages 1 and 3: the optional rule keeps the old syntactic
system, and dropping it leaves the semantic one. -/
theorem stage2_map_resolve {cs : List (GenderedNoun Value)}
    (h : ∀ c ∈ cs, c.referentGender = some .female → c.gender = .feminine) :
    stage2.map (resolve · cs) = [resolve stage1 cs, resolve stage3 cs] := by
  simp only [stage2, stage1, stage3, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact resolve_cons_cons_of_applies_imp (fun ha c hc ↦ h c hc (ha c hc)) rfl

-- p. 303: the option makes stage 2 a mixed system, reading the conjuncts' genders and meanings
theorem stage2_mixed :
    ¬ Function.FactorsThrough (fun cs ↦ stage2.map (resolve · cs)) (List.map (·.gender)) ∧
      ¬ Function.FactorsThrough (fun cs ↦ stage2.map (resolve · cs))
        (List.map (·.referentGender)) :=
  ⟨fun h ↦ absurd (h (a := [zena, zena]) (b := [stula, staka]) rfl) (by decide),
    fun h ↦ absurd (h (a := [stula, staka]) (b := [pesak, pesak]) rfl) (by decide)⟩

/-- The nouns of the -Ø declension among the examples (pp. 300–301). -/
def zeroDeclension : List (GenderedNoun Value) := [opreznost, suptilnost, lakomislenost]

/-- The book's first formulation of stage 2, with a morphological condition: the feminine if all
conjuncts are feminine, a rule that is optional when a conjunct is of the -Ø declension, else
the masculine. The two grammars apply the rule and pass it over where they may. -/
def morphological : List (List (ResolutionRule (GenderedNoun Value) Value)) :=
  [stage1, [.all (fun c ↦ c.gender = .feminine ∧ c ∉ zeroDeclension) .feminine,
    otherwise .masculine]]

/-- Two feminines in *-a* with a masculine predicate, (78), refute the morphological condition,
and the semantic condition allows them: the option rests on the conjuncts denoting
inanimates. -/
theorem not_morphological :
    (∀ g ∈ morphological, resolve g [stula, staka] ≠ some .masculine) ∧
      ∃ g ∈ stage2, resolve g [stula, staka] = some .masculine := by
  decide +kernel

-- p. 302: no masculine agreement with feminines denoting persons
theorem females_fem : ∀ g ∈ stage2, resolve g [zena, zena] = some .feminine := by decide

end SerboCroat

namespace Ojibwa

/-- The animate and the inanimate genders. -/
inductive Value where
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- By §9.7, homogeneous conjuncts keep their gender, and animate and inanimate cannot be
conjoined. -/
def rules : List (ResolutionRule Value Value) :=
  [.all (· = .animate) .animate, .all (· = .inanimate) .inanimate]

theorem resolve_mixed : resolve rules [.animate, .inanimate] = none := by decide

end Ojibwa

/-! ### The judgments of chapter 9

A row with a `conjuncts` and a `resolved` feature names its conjuncts and the form the
predicate shows; it is acceptable exactly when the language's rules select that form. -/

theorem czech_rows : ∀ row ∈ Examples.all, row.language = .czech →
    ∀ cs ∈ row.parse? "conjuncts" [("1+2", [Person.first, .second]), ("3+1", [.third, .first]),
      ("3+2", [.third, .second])],
      ∀ p ∈ row.parse? "resolved" [("1", Person.first), ("2", .second)],
        (row.judgment = .acceptable ↔ resolve personRules cs = some p) := by
  decide +kernel

open _root_.Tamil.Gender in
theorem tamil_rows : ∀ row ∈ Examples.all, row.language = .tamil →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [Value.masc, .masc]), ("fem+fem", [.fem, .fem]),
      ("fem+masc", [.fem, .masc]), ("neut+neut", [.neut, .neut]), ("masc+neut", [.masc, .neut])],
      ∀ g ∈ row.parse? "resolved" [("rational", PlConcord.rational), ("neuter", .neuter)],
        (row.judgment = .acceptable ↔ resolve Tamil.rules cs = some g) := by
  decide +kernel

theorem archi_rows : ∀ row ∈ Examples.all, row.language = .archi →
    ∀ cs ∈ row.parse? "conjuncts" [("rational+rational", [true, true]),
      ("rational+nonrational", [true, false]), ("nonrational+nonrational", [false, false])],
      ∀ g ∈ row.parse? "resolved" [("I/II", Archi.PlForm.I_II), ("III/IV", .III_IV)],
        (row.judgment = .acceptable ↔ resolve Archi.rules cs = some g) := by
  decide +kernel

theorem luganda_rows : ∀ row ∈ Examples.all, row.language = .ganda →
    ∀ cs ∈ row.parse? "conjuncts" [("human+human+human", [true, true, true]),
      ("nonhuman+nonhuman+nonhuman+nonhuman", [false, false, false, false]),
      ("human+nonhuman", [true, false])],
      ∀ g ∈ row.parse? "resolved" [("2", Luganda.PlForm.cl2), ("8", .cl8)],
        (row.judgment = .acceptable ↔ resolve Luganda.rules cs = some g) := by
  decide +kernel

theorem french_rows : ∀ row ∈ Examples.all, row.language = .french →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [French.Gender.Value.masculine, .masculine]),
      ("fem+fem", [.feminine, .feminine]), ("masc+fem", [.masculine, .feminine])],
      ∀ g ∈ row.parse? "resolved" [("masc", French.Gender.Value.masculine), ("fem", .feminine)],
        (row.judgment = .acceptable ↔ resolve French.rulesA cs = some g) := by
  decide +kernel

theorem slovene_rows : ∀ row ∈ Examples.all, row.language = .slovenian →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+fem", [Slovene.Value.masc, .fem]),
      ("masc+neut", [.masc, .neut]), ("fem+neut", [.fem, .neut]), ("neut+neut", [.neut, .neut]),
      ("fem+fem", [.fem, .fem]), ("neut+neut+neut", [.neut, .neut, .neut]),
      ("fem+fem+fem", [.fem, .fem, .fem])],
      ∀ g ∈ row.parse? "resolved" [("masc", Slovene.Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Slovene.rules cs = some g) := by
  decide +kernel

theorem slovene_number_rows : ∀ row ∈ Examples.all, row.language = .slovenian →
    ∀ ns ∈ row.parse? "numbers" [("sg+sg", [Number.singular, .singular]),
      ("sg+sg+sg", [.singular, .singular, .singular]), ("sg+du", [.singular, .dual])],
      ∀ n ∈ row.parse? "number" [("dual", Number.dual), ("plural", .plural)],
        (row.judgment = .acceptable ↔ numberResolve Slovene.numbers ns = some n) := by
  decide +kernel

theorem icelandic_rows : ∀ row ∈ Examples.all, row.language = .icelandic →
    ∀ cs ∈ row.parse? "conjuncts"
      [("masc+fem", [_root_.Icelandic.Nouns.drengur, _root_.Icelandic.Nouns.telpa]),
        ("fem+neut", [_root_.Icelandic.Nouns.aer, _root_.Icelandic.Nouns.lamb])],
      ∀ g ∈ row.parse? "resolved" [("neut", _root_.Icelandic.Gender.Value.neuter)],
        (row.judgment = .acceptable ↔ resolve Icelandic.rules (cs.map (·.gender)) = some g) := by
  decide +kernel

theorem polish_rows : ∀ row ∈ Examples.all, row.language = .polish →
    ∀ cs ∈ row.parse? "conjuncts" [("fem+fem", [false, false]),
      ("mascPers+fem+fem", [true, false, false])],
      ∀ g ∈ row.parse? "resolved" [("mascPers", Polish.PlForm.mascPers),
        ("nonMascPers", .nonMascPers)],
        (row.judgment = .acceptable ↔ resolve Polish.rules cs = some g) := by
  decide +kernel

theorem latin_rows : ∀ row ∈ Examples.all, row.language = .latin →
    ∀ cs ∈ row.parse? "conjuncts" [("masc.human+fem.human",
      [((Latin.Gender.Value.masc, .human) : Latin.Conjunct), (.fem, .human)]),
      ("masc.inanimate+fem.inanimate", [(.masc, .inanimate), (.fem, .inanimate)])],
      ∀ g ∈ row.parse? "resolved" [("masc", Latin.Gender.Value.masc), ("neut", .neut)],
        (row.judgment = .acceptable ↔ resolve Latin.rules cs = some g) := by
  decide +kernel

open _root_.Romanian.Gender in
theorem romanian_resolution_rows : ∀ row ∈ Examples.all, row.language = .romanian →
    ∀ cs ∈ row.parse? "conjuncts" [("fată+femeie", [fata, femeie]),
      ("băiat+bărbat", [baiat, barbat]), ("băiat+fată", [baiat, fata]),
      ("uşă+perete", [usa, perete]), ("perete+scaun", [perete, scaun]),
      ("scaun+masă", [scaun, masa]), ("nuc+prun", [nuc, prun]),
      ("frigider+televizor", [frigider, televizor]), ("uşă+masă", [usa, masa])],
      ∀ g ∈ row.parse? "resolved" [("masc", Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Romanian.rules cs = some g) := by
  decide +kernel

open _root_.Serbian.Gender in
theorem serboCroat_rows : ∀ row ∈ Examples.all, row.language = .serbianCroatianBosnian →
    ∀ cs ∈ row.parse? "conjuncts" [("znanje+intuicija", [znanje, intuicija]),
      ("mesto+značenje", [mesto, znacenje]),
      ("opreznost+suptilnost+pedanterija", [opreznost, suptilnost, pedanterija]),
      ("nebriga+lakomislenost", [nebriga, lakomislenost]), ("štula+štaka", [stula, staka])],
      ∀ g ∈ row.parse? "resolved" [("masc", Value.masculine), ("fem", .feminine)],
        (row.judgment = .acceptable ↔ ∃ gr ∈ SerboCroat.stage2, resolve gr cs = some g) := by
  decide +kernel

theorem ojibwa_rows : ∀ row ∈ Examples.all, row.language = .ojibwa →
    ∀ cs ∈ row.parse? "conjuncts" [("animate+animate", [Ojibwa.Value.animate, .animate]),
      ("inanimate+inanimate", [.inanimate, .inanimate]),
      ("animate+inanimate", [.animate, .inanimate])],
      ∀ g ∈ row.parse? "resolved" [("animate", Ojibwa.Value.animate), ("inanimate", .inanimate)],
        (row.judgment = .acceptable ↔ resolve Ojibwa.rules cs = some g) := by
  decide +kernel

/-! ### The judgments of chapter 3

A Swahili row with a `noun` and a `concord` feature is acceptable exactly when the concord
is the gender the assignment rules give the noun. -/

open _root_.Swahili in
theorem swahili_rows : ∀ row ∈ Examples.all, row.language = .swahili →
    ∀ n ∈ row.parse? "noun" (allNouns.map fun n ↦ (n.form, n)),
      ∀ g ∈ row.parse? "concord" [("1/2", Gender.genderA), ("3/4", .genderB), ("7/8", .genderD)],
        (row.judgment = .acceptable ↔ Swahili.system.assign Swahili.sem Noun.morphClass n = g) := by
  decide +kernel

end Corbett1991
