module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Agreement.Hierarchy
public import Linglib.Syntax.Agreement.Resolution
public import Linglib.Syntax.Agreement.Classes
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
public import Linglib.Data.Examples.Corbett1991

/-!
# Corbett (1991): Gender

The book's typology of gender. Gender is a property of nouns shown only in agreement, and a
language's genders are the classes of nouns that take the same agreements. Nouns are assigned to
them by rules reading their meaning or their form: the semantic rules take precedence, the
formal rules, morphological or phonological, sort the semantic residue, and no system is formal
alone (`Gender.AssignmentSystem`). Tamil, Russian, Swahili, Afar and Hausa instantiate the
schema on their fragments, and the assignment systems of chapters 2 and 3 are surveyed by kind
and by the semantic criteria their rules use (`survey`).

Counting the genders starts from agreement classes, the sets of nouns taking identical
agreements in every form on every target, distinguishes the controller genders into which
nouns fall from the target genders marked on agreeing elements, and reads Greenberg's
universal that the plural never distinguishes more genders than the singular off the map
between the two numbers' target genders, parallel, convergent or crossed, exhibited here for
French, German, Tamil, Romanian, Lak and Slovene. Nouns whose meaning and form conflict may
be hybrid, taking semantic agreement on some targets and syntactic agreement on others, and
the hybrids of the book's summary table respect the Agreement Hierarchy
(`hybrids_respectHierarchy`); the Bantu data of §8.3 divide the attributive position into
the possessive and the other modifiers (`FinePosition`), and the corpus proportions of
feminine agreement with Russian *vrač* respect the hierarchy too.

Conjoined controllers are resolved by ordered rules of two shapes, one conjunct of a kind or
all conjuncts of a kind, reading the conjuncts' person, meaning or gender; the rules of
person, of number and of gender are stated for Czech, Tamil, Archi, Luganda, French, Slovene,
Icelandic, Latin, Polish, Romanian, Serbo-Croat and Ojibwa, and a language's resolution is
never less semantic than its assignment. The judgments the book reports are the rows of
`Data/Examples/Corbett1991.json`.

## Implementation notes

* The assignment systems are the substrate's, typed by the meaning their semantic rules read
  and the form their formal rules read; the fragments' natural-gender flag stands in for the
  referent's sex. Corbett's irregular third declension of Russian is the study's refinement
  of the fragment's declension classes.
* Agreement classes, target genders and the map between two numbers' target genders are the
  substrate's `Gender.agreementClasses`, `Gender.targetGenders` and `Gender.Parallel`,
  `Gender.Convergent` and `Gender.Crossed`. Subgenders, inquorate genders and consistent
  agreement patterns are described in the book's prose and not formalised.
* A hybrid noun is an `Agreement.Hybrid`, its availability profile over the positions of
  `Agreement.Position`, or over `FinePosition` where the book divides the attributive; it
  respects the hierarchy when the profile is antitone on the positions where it is recorded,
  and the same predicate serves the corpus proportions.
* Resolution rules are the substrate's `Agreement.ResolutionRule`, applied in order to a
  list of conjunct descriptors and returning no form when no rule applies, the book's
  ineffable coordinations; the descriptors are persons, genders, semantic features, or
  fragment nouns as each language requires. Optional rules are recorded as rows. The number
  rules count the conjuncts, which no resolution rule can (`Slovene.numberResolve_ne_resolve`),
  so they are stated directly and shown to be the substrate's `Number.System.resolve` folded
  over the conjuncts, except that a coordination of plurals alone resolves nothing, the book's
  restriction that keeps gender resolution from being triggered. The gender carriers of French,
  Lak, Slovene and Ojibwa are declared in the study, there being no fragments for them; the
  Icelandic rules read the fragment nouns' genders, and the Romanian ones the nouns.
* Not modelled: the psycholinguistic evidence of chapter 4, the morphology of agreement and
  its limits in chapter 5, syncretism and neutral agreement in chapter 7, the diachrony of
  chapters 8 to 10, Russian acronyms and indeclinables, Chichewa's target-gender rule for
  plural conjuncts, the Polish optional resolution rules, and the case and distance effects
  within a position of the hierarchy (§8.1.2), which are rows only.

## TODO

* Subgenders as minimally different agreement classes, and consistent agreement patterns,
  want the full paradigm tables of the book's chapter 6 in the Russian fragment.
* The corpus-level reading of the hierarchy, proportions of semantic agreement per target,
  is recorded for *vrač* only.
* The generalization of §9.8, that resolution is never less semantic than assignment: a rule
  reads gender or meaning when its sort factors through that map
  (`Agreement.ResolutionRule.resolve_factorsThrough`), but the languages' conjuncts are not
  yet typed by both.

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
  /-- The language, under the book's name. -/
  language : String
  glottocode : String
  /-- The kind of assignment system the book describes. -/
  kind : AssignmentKind
  /-- The semantic criteria the book's rules for the language use. -/
  criteria : List Criterion
  deriving DecidableEq, Repr

/-- The assignment systems of chapters 2 and 3 (Tables 2.1 to 2.8 and §3.1 to §3.2). -/
def survey : List SurveyEntry :=
  [⟨"Tamil", "tami1289", .strictSemantic, [.rationality, .sex]⟩,
    ⟨"Diyari", "dier1241", .strictSemantic, [.sex]⟩,
    ⟨"Dizi", "dizi1235", .strictSemantic, [.sex, .evaluation]⟩,
    ⟨"Halkomelem", "halk1245", .strictSemantic, [.sex, .evaluation]⟩,
    ⟨"Defaka", "defa1248", .strictSemantic, [.humanness, .sex]⟩,
    ⟨"English", "stan1293", .strictSemantic, [.humanness, .sex]⟩,
    ⟨"Zande", "zand1248", .predominantlySemantic, [.humanness, .sex, .animacy]⟩,
    ⟨"Dyirbal", "dyir1250", .predominantlySemantic, [.humanness, .sex, .animacy, .edibility]⟩,
    ⟨"Ket", "kett1243", .predominantlySemantic, [.animacy, .sex]⟩,
    ⟨"Ojibwa", "ojib1241", .predominantlySemantic, [.animacy]⟩,
    ⟨"Lak", "lakk1252", .predominantlySemantic, [.rationality, .sex, .animacy]⟩,
    ⟨"Archi", "arch1244", .predominantlySemantic,
      [.rationality, .sex, .animacy, .size, .abstractness, .insect]⟩,
    ⟨"Russian", "russ1263", .morphological, [.sex, .animacy]⟩,
    ⟨"Swahili", "swah1253", .morphological, [.animacy, .evaluation]⟩,
    ⟨"Afar", "afar1241", .phonological, [.sex]⟩,
    ⟨"Hausa", "haus1257", .phonological, [.sex]⟩,
    ⟨"Godié", "godi1239", .phonological, [.humanness, .size, .liquidity]⟩,
    ⟨"Yimas", "yima1243", .phonological, [.sex, .humanness, .animacy]⟩,
    ⟨"French", "stan1290", .phonological, [.sex]⟩]

/-! ### Tamil: a strict semantic system (§2.1.1) -/

namespace Tamil

open _root_.Tamil.Gender

/-- The rules read rationality and the gender of the referents. -/
def sem (n : Tamil.Gender.Noun) : Bool × Option Gender := (n.rational, n.naturalGender)

/-- Table 2.1 makes male rationals masculine, female rationals feminine and the residue
neuter. -/
def system : Gender.AssignmentSystem (Bool × Option Gender) Unit Value where
  semantic
    | (true, some .masculine) => some .masc
    | (true, some .feminine) => some .fem
    | _ => none
  formal _ := none
  residue := .neut

theorem isStrictSemantic_system : system.IsStrictSemantic := fun _ ↦ rfl

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

/-- The gender of the referents. -/
def sem (n : Russian.Gender.Noun) : Option Gender := n.naturalGender

/-- The rules of §3.1.1 for declinable nouns make males masculine and females feminine, then
declension I masculine, declensions II and III feminine and the rest neuter. The rules for
acronyms and indeclinables (Figure 3.4) are not modelled. -/
def system : Gender.AssignmentSystem (Option Gender) (Option Declension) Value where
  semantic
    | some .masculine => some .masc
    | some .feminine => some .fem
    | _ => none
  formal
    | some .I => some .masc
    | some .II | some .III => some .fem
    | _ => none
  residue := .neut

theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ≠ put' → system.assign sem declension n = n.gender := by
  decide

theorem djadja_precedence :
    system.formal (declension djadja) = some .fem ∧
      system.assign sem declension djadja = .masc := by
  decide

/-- *vrač* 'doctor' as a lexeme is not sex-differentiable, so the declension decides; the
conflict when it denotes a woman is the hybrid pattern of §8.1. -/
theorem vrac_by_declension : system.assign sem declension vrač = .masc := by decide

end Russian

/-! ### Swahili: morphological classes and animate concord (§3.1.2) -/

namespace Swahili

open _root_.Swahili

/-- The semantic rules read evaluative derivation and animacy. -/
def sem (n : Swahili.Noun) : Option Evaluative × Animacy := (n.evaluative, n.animacy)

/-- The rules of §3.1.2 send augmentatives to 5/6, diminutives to 7/8 and remaining animates
to 1/2, then each morphological class to its own gender, over the fragment's five genders (the
book's 11/10 and 15 are not among them). The formal rule is total, so the residue gender is
never reached. -/
def system : Gender.AssignmentSystem (Option Evaluative × Animacy) _root_.Swahili.Gender
    _root_.Swahili.Gender where
  semantic
    | (some .augmentative, _) => some .genderC
    | (some .diminutive, _) => some .genderD
    | (none, a) => if .animate ≤ a then some .genderA else none
  formal := some
  residue := .genderE

theorem assign_eq_gender : ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = n.gender := by
  decide

theorem genderA_semantic :
    ∀ n ∈ allNouns, system.assign sem Noun.morphClass n = .genderA →
      (system.semantic (sem n)).isSome := by
  decide

end Swahili

/-! ### Afar and Hausa: phonological systems (§3.2.1, §3.2.2) -/

namespace Afar

open _root_.Afar.Gender

/-- The gender of the referents. -/
def sem (n : Afar.Gender.Noun) : Option Gender := n.naturalGender

/-- The referents' gender first; then a citation form ending in an accented vowel is feminine,
the rest masculine. -/
def system : Gender.AssignmentSystem (Option Gender) Bool Value where
  semantic
    | some .masculine => some .masc
    | some .feminine => some .fem
    | _ => none
  formal acc := if acc then some .fem else none
  residue := .masc

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

/-- The gender of the referents. -/
def sem (n : Hausa.Noun) : Option Gender := n.naturalGender

/-- The referents' gender first; then a noun in *-ā* is feminine, the rest masculine. -/
def system : Gender.AssignmentSystem (Option Gender) Bool Gender where
  semantic := id
  formal aa := if aa then some .feminine else none
  residue := .masculine

theorem assign_eq_gender :
    ∀ n ∈ allNouns, n ∉ [gida, kada] →
      system.assign sem (fun n ↦ decide n.EndsInAa) n = n.gender := by
  decide

end Hausa

/-! ### Controller and target genders (chapter 6) -/

namespace Romanian

open _root_.Romanian.Gender

/-- Figure 6.1 is a crossed system. -/
theorem crossed :
    Gender.Crossed (Value.adjForm · (numberSystem.value .singular))
      (Value.adjForm · (numberSystem.value .plural)) := by
  decide

theorem card_range_adjForm :
    Fintype.card (Set.range Value.adjForm) = 3 ∧
      Fintype.card (Gender.targetGenders Value.adjForm (numberSystem.value .singular)) = 2 ∧
        Fintype.card (Gender.targetGenders Value.adjForm (numberSystem.value .plural)) = 2 := by
  decide

/-- Every fragment noun takes, in each number, the form of its gender, (5) to (10). -/
theorem rows : ∀ row ∈ Examples.all, row.language = "roma1327" →
    ∀ n ∈ row.parse? "noun" (allNouns.map fun n ↦ (n.form, n)),
      ∀ pl ∈ row.parse? "number"
          [("singular", numberSystem.value .singular), ("plural", numberSystem.value .plural)],
        ∀ f ∈ row.parse? "form" [("zero", AdjForm.zero), ("ă", .ă), ("i", .i), ("e", .e)],
          (row.judgment = .acceptable ↔ n.gender.adjForm pl = f) := by
  decide +kernel

end Romanian

namespace French

/-- The two genders have one form each in both numbers (Figure 6.6). -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

theorem parallel : Gender.Parallel (id : Value → Value) id := by decide

end French

namespace German

open _root_.German.Determiners in
/-- The definite article has three forms for the three genders in the nominative singular and
one in the plural (Figure 6.7). -/
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

/-- Figure 6.10 is a crossed system, with three target genders in the singular and two in the
plural. -/
theorem crossed : Gender.Crossed Value.sgMarker Value.plMarker := by decide

theorem card_plMarker_le :
    Fintype.card (Set.range Value.plMarker) ≤ Fintype.card (Set.range Value.sgMarker) := by
  decide

end Lak

namespace Slovene

/-- An agreeing predicate's endings for the three genders in the three numbers (Table 9.5) are
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

/-- In Figure 6.8 three singular target genders converge on two in the plural. -/
theorem convergent : Gender.Convergent Value.sgConcord Value.plConcord := by decide

theorem card_plConcord_le :
    Nat.card (Set.range Value.plConcord) ≤ Nat.card (Set.range Value.sgConcord) :=
  convergent.1.card_range_le

end Tamil

/-! ### Hybrid nouns and the Agreement Hierarchy (chapter 8) -/

/-- Table 8.1, with the English boat nouns of §6.4.5 and the Bantu hybrids of §8.3. -/
def frenchTitles : Hybrid Position := fun
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic

def madchen : Hybrid Position := fun
  | .attributive | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | .predicate => none

def lajdaki : Hybrid Position := fun
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .semanticOnly

def spanishTitles : Hybrid Position := fun
  | .attributive => some .syntacticOnly
  | .predicate | .relativePronoun | .personalPronoun => some .semanticOnly

def konkani : Hybrid Position := fun
  | .attributive => some .syntacticOnly
  | .predicate | .personalPronoun => some .semanticOnly
  | .relativePronoun => none

def vrac : Hybrid Position := fun
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun | .personalPronoun => some .mostlySemantic

def gazde : Hybrid Position := fun
  | .attributive => some .mostlySyntactic
  | .predicate => some .both
  | .relativePronoun => some .mostlySemantic
  | .personalPronoun => some .semanticOnly

def boat : Hybrid Position := fun
  | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .both
  | _ => none

/-- *kamwana* takes gender 12/13 forms normally, and gender 1/2 is also possible for a
personal pronoun sufficiently removed from the controller. -/
def kamwana : Hybrid Position := fun
  | .attributive | .predicate | .relativePronoun => some .syntacticOnly
  | .personalPronoun => some .mostlySyntactic

def kilumba : Hybrid Position := fun
  | .attributive => some .syntacticOnly
  | .predicate => some .both
  | _ => none

/-- The hybrids of Table 8.1 by the names the rows use. -/
def hybridNames : List (String × Hybrid Position) :=
  [("frenchTitles", frenchTitles),
    ("mädchen", madchen),
    ("łajdaki", lajdaki),
    ("spanishTitles", spanishTitles),
    ("konkani", konkani),
    ("vrač", vrac),
    ("gazde", gazde),
    ("boat", boat),
    ("kamwana", kamwana),
    ("kilumba", kilumba)]

/-- Every hybrid of Table 8.1 respects the Agreement Hierarchy. -/
theorem hybrids_respectHierarchy : ∀ h ∈ hybridNames, RespectsHierarchy h.2 := by decide

/-- At the corpus level, 16.9 per cent of 3,835 of Panov's respondents favour feminine
agreement with *vrač* for the attributive and 51.7 per cent of 3,806 for the predicate. -/
def vracFeminine : Position → Option ℚ
  | .attributive => some (169 / 1000)
  | .predicate => some (517 / 1000)
  | _ => none

theorem vracFeminine_respectsHierarchy : RespectsHierarchy vracFeminine := by decide +kernel

/-- By the stacked-target constraint of §8.1.2, when stacked or parallel targets of one
controller differ, the further one shows semantic agreement. -/
def StackedAllowed (near far : Kind) : Prop := near = .semantic → far = .semantic

instance (near far : Kind) : Decidable (StackedAllowed near far) := by
  unfold StackedAllowed; infer_instance

/-! ### Attributive possessives (§8.3)

The last stages of the loss of syntactic agreement in coastal Bantu treat the attributive
possessive differently from the other attributive modifiers, a finer division of the
hierarchy. -/

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

/-- Swahili *rafiki* 'friend', (47) to (49), is an animate of morphological class 9/10 with
gender 1/2 agreement throughout, class 9/10 agreement remaining possible on an attributive
possessive alone. -/
def rafiki : Hybrid FinePosition := fun
  | .possessive => some .both
  | .attributive | .predicate => some .semanticOnly
  | _ => none

/-- With Kami *ng'ombe* 'cows' and *mbudzi* 'goats', (54) and (55), syntactic agreement of the
predicate is rejected and both forms are accepted on attributives other than the possessive,
which the book reports with class 10 agreement only. -/
def ngombe : Hybrid FinePosition := fun
  | .possessive => some .syntacticOnly
  | .attributive => some .both
  | .predicate => some .semanticOnly
  | _ => none

/-- The Bantu hybrids of §8.3 by the names the rows use. -/
def fineHybridNames : List (String × Hybrid FinePosition) :=
  [("rafiki", rafiki),
    ("ng'ombe", ngombe),
    ("mbudzi", ngombe)]

theorem fineHybrids_respectHierarchy : ∀ h ∈ fineHybridNames, RespectsHierarchy h.2 := by
  decide

/-! ### The judgments of chapter 8

A row with a `hybrid`, a `target` and an `agreement` feature is a use of a hybrid noun at a
position of the hierarchy, acceptable exactly when the hybrid's availability there admits
the agreement; a row with `near` and `far` features is a pair of stacked targets. The
hybrids are listed by the names the rows use. -/

/-- The positions of the hierarchy by the names the rows use. -/
def positionNames : List (String × Position) :=
  [("attributive", .attributive), ("predicate", .predicate),
    ("relativePronoun", .relativePronoun), ("personalPronoun", .personalPronoun)]

/-- The fine positions by the names the rows use. -/
def finePositionNames : List (String × FinePosition) :=
  [("attributivePossessive", .possessive), ("attributive", .attributive),
    ("predicate", .predicate), ("relativePronoun", .relativePronoun),
    ("personalPronoun", .personalPronoun)]

/-- The two agreements by the names the rows use. -/
def kindNames : List (String × Kind) := [("syntactic", .syntactic), ("semantic", .semantic)]

theorem hybrid_rows : ∀ row ∈ Examples.all, ∀ h ∈ hybridNames, row.feature? "hybrid" = some h.1 →
    ∀ t ∈ row.parse? "target" positionNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.2 t, a.Allows k) := by
  decide +kernel

theorem fine_rows : ∀ row ∈ Examples.all, ∀ h ∈ fineHybridNames, row.feature? "hybrid" = some h.1 →
    ∀ t ∈ row.parse? "target" finePositionNames, ∀ k ∈ row.parse? "agreement" kindNames,
      (row.judgment = .acceptable ↔ ∃ a ∈ h.2 t, a.Allows k) := by
  decide +kernel

/-- Every row naming a hybrid names one of Table 8.1 or one of §8.3, at a position one of
the two theorems reads. -/
theorem hybrid_rows_covered : ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "hybrid",
    (n ∈ hybridNames.map Prod.fst ∨ n ∈ fineHybridNames.map Prod.fst) ∧
      ∀ t ∈ row.feature? "target", t ∈ finePositionNames.map Prod.fst := by
  decide +kernel

theorem stacked_rows : ∀ row ∈ Examples.all, ∀ near ∈ row.parse? "near" kindNames,
    ∀ far ∈ row.parse? "far" kindNames, (row.judgment = .acceptable ↔ StackedAllowed near far) := by
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

/-- Masculine and feminine together resolve to the rational form, (16). -/
theorem resolve_masc_fem : resolve rules [.masc, .fem] = some .rational := by decide

/-- A rational and a non-rational cannot be resolved, (18). -/
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

/-- The type-A rules of §9.4 give the masculine if a conjunct is masculine and the feminine
otherwise. -/
def rulesA : List (ResolutionRule Value Value) := [.any (· = .masc) .masc, otherwise .fem]

/-- The type-B rules give the feminine if all conjuncts are feminine and the masculine
otherwise. -/
def rulesB : List (ResolutionRule Value Value) := [.all (· = .fem) .fem, otherwise .masc]

/-- With exactly two genders the two formulations are logically equivalent (p. 280), the
feminine being the complement of the masculine. -/
theorem resolve_rulesA_eq_rulesB (cs : List Value) : resolve rulesA cs = resolve rulesB cs :=
  resolve_any_otherwise fun c ↦ by cases c <;> decide

end French

namespace Slovene

/-- The numbers of Slovene. -/
def numbers : Number.System := { values := {.singular, .dual, .plural} }

theorem resolve_numbers :
    ∀ a b, numbers.resolve a b = if a = .singular ∧ b = .singular then .dual else .plural := by
  decide

/-- When the number rules apply, their forms are semantically justified (p. 264), since a
coordination with a non-plural conjunct takes the substrate's resolution of its conjuncts. -/
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

/-- Three neuter singulars take the masculine plural, gender resolution triggered by number
resolution, (52). -/
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
def rules : List (ResolutionRule _root_.Gender _root_.Gender) :=
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
  .animate ≤ n.animacy ∧ n.naturalGender = some .masculine

instance : DecidablePred MaleAnimate := fun _ ↦ by unfold MaleAnimate; infer_instance

/-- Collapsed over the fragment's nouns, §9.5 gives the masculine if a conjunct is a male
animate or all are masculine, and the feminine otherwise. -/
def rules : List (ResolutionRule Romanian.Gender.Noun Value) :=
  [.any MaleAnimate .masc, .all (·.gender = .masc) .masc, otherwise .fem]

/-- A masculine and a neuter inanimate resolve to the feminine, the form the neuter takes in
the plural, (69). -/
theorem resolve_perete_scaun : resolve rules [perete, scaun] = some .fem := by decide

end Romanian

namespace SerboCroat

/-- Stage 2 of §9.7, the alternative formulation, stage 1 being Slovene's rules, gives the
feminine if all conjuncts are female, optionally the feminine if all are feminine, and the
masculine otherwise. The optional rule
yields a second grammar. -/
def stage2 : List (List (ResolutionRule (Slovene.Value × Bool) Slovene.Value)) :=
  [[.all (fun c ↦ c.1 = .fem ∧ c.2) .fem, .all (·.1 = .fem) .fem, otherwise .masc],
    [.all (fun c ↦ c.1 = .fem ∧ c.2) .fem, otherwise .masc]]

/-- Feminine inanimates may take the masculine, (77) and (78). -/
theorem feminine_inanimates_masc :
    ∃ g ∈ stage2, resolve g [(.fem, false), (.fem, false)] = some .masc := by
  decide

theorem females_fem : ∀ g ∈ stage2, resolve g [(.fem, true), (.fem, true)] = some .fem := by
  decide

end SerboCroat

namespace Ojibwa

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

theorem czech_rows : ∀ row ∈ Examples.all, row.language = "czec1258" →
    ∀ cs ∈ row.parse? "conjuncts" [("1+2", [Person.first, .second]), ("3+1", [.third, .first]),
      ("3+2", [.third, .second])],
      ∀ p ∈ row.parse? "resolved" [("1", Person.first), ("2", .second)],
        (row.judgment = .acceptable ↔ resolve personRules cs = some p) := by
  decide +kernel

open _root_.Tamil.Gender in
theorem tamil_rows : ∀ row ∈ Examples.all, row.language = "tami1289" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [Value.masc, .masc]), ("fem+fem", [.fem, .fem]),
      ("fem+masc", [.fem, .masc]), ("neut+neut", [.neut, .neut]), ("masc+neut", [.masc, .neut])],
      ∀ g ∈ row.parse? "resolved" [("rational", PlConcord.rational), ("neuter", .neuter)],
        (row.judgment = .acceptable ↔ resolve Tamil.rules cs = some g) := by
  decide +kernel

theorem archi_rows : ∀ row ∈ Examples.all, row.language = "arch1244" →
    ∀ cs ∈ row.parse? "conjuncts" [("rational+rational", [true, true]),
      ("rational+nonrational", [true, false]), ("nonrational+nonrational", [false, false])],
      ∀ g ∈ row.parse? "resolved" [("I/II", Archi.PlForm.I_II), ("III/IV", .III_IV)],
        (row.judgment = .acceptable ↔ resolve Archi.rules cs = some g) := by
  decide +kernel

theorem luganda_rows : ∀ row ∈ Examples.all, row.language = "gand1255" →
    ∀ cs ∈ row.parse? "conjuncts" [("human+human+human", [true, true, true]),
      ("nonhuman+nonhuman+nonhuman+nonhuman", [false, false, false, false]),
      ("human+nonhuman", [true, false])],
      ∀ g ∈ row.parse? "resolved" [("2", Luganda.PlForm.cl2), ("8", .cl8)],
        (row.judgment = .acceptable ↔ resolve Luganda.rules cs = some g) := by
  decide +kernel

theorem french_rows : ∀ row ∈ Examples.all, row.language = "stan1290" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+masc", [French.Value.masc, .masc]),
      ("fem+fem", [.fem, .fem]), ("masc+fem", [.masc, .fem])],
      ∀ g ∈ row.parse? "resolved" [("masc", French.Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve French.rulesA cs = some g) := by
  decide +kernel

theorem slovene_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc+fem", [Slovene.Value.masc, .fem]),
      ("masc+neut", [.masc, .neut]), ("fem+neut", [.fem, .neut]), ("neut+neut", [.neut, .neut]),
      ("fem+fem", [.fem, .fem]), ("neut+neut+neut", [.neut, .neut, .neut]),
      ("fem+fem+fem", [.fem, .fem, .fem])],
      ∀ g ∈ row.parse? "resolved" [("masc", Slovene.Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Slovene.rules cs = some g) := by
  decide +kernel

theorem slovene_number_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ ns ∈ row.parse? "numbers" [("sg+sg", [Number.singular, .singular]),
      ("sg+sg+sg", [.singular, .singular, .singular]), ("sg+du", [.singular, .dual])],
      ∀ n ∈ row.parse? "number" [("dual", Number.dual), ("plural", .plural)],
        (row.judgment = .acceptable ↔ numberResolve Slovene.numbers ns = some n) := by
  decide +kernel

theorem icelandic_rows : ∀ row ∈ Examples.all, row.language = "icel1247" →
    ∀ cs ∈ row.parse? "conjuncts"
      [("masc+fem", [_root_.Icelandic.Nouns.drengur, _root_.Icelandic.Nouns.telpa]),
        ("fem+neut", [_root_.Icelandic.Nouns.aer, _root_.Icelandic.Nouns.lamb])],
      ∀ g ∈ row.parse? "resolved" [("neut", _root_.Gender.neuter)],
        (row.judgment = .acceptable ↔ resolve Icelandic.rules (cs.map (·.gender)) = some g) := by
  decide +kernel

theorem polish_rows : ∀ row ∈ Examples.all, row.language = "poli1260" →
    ∀ cs ∈ row.parse? "conjuncts" [("fem+fem", [false, false]),
      ("mascPers+fem+fem", [true, false, false])],
      ∀ g ∈ row.parse? "resolved" [("mascPers", Polish.PlForm.mascPers),
        ("nonMascPers", .nonMascPers)],
        (row.judgment = .acceptable ↔ resolve Polish.rules cs = some g) := by
  decide +kernel

theorem latin_rows : ∀ row ∈ Examples.all, row.language = "lati1261" →
    ∀ cs ∈ row.parse? "conjuncts" [("masc.human+fem.human",
      [((Latin.Gender.Value.masc, .human) : Latin.Conjunct), (.fem, .human)]),
      ("masc.inanimate+fem.inanimate", [(.masc, .inanimate), (.fem, .inanimate)])],
      ∀ g ∈ row.parse? "resolved" [("masc", Latin.Gender.Value.masc), ("neut", .neut)],
        (row.judgment = .acceptable ↔ resolve Latin.rules cs = some g) := by
  decide +kernel

open _root_.Romanian.Gender in
theorem romanian_resolution_rows : ∀ row ∈ Examples.all, row.language = "roma1327" →
    ∀ cs ∈ row.parse? "conjuncts" [("fată+femeie", [fata, femeie]),
      ("băiat+bărbat", [baiat, barbat]), ("băiat+fată", [baiat, fata]),
      ("uşă+perete", [usa, perete]), ("perete+scaun", [perete, scaun]),
      ("scaun+masă", [scaun, masa]), ("nuc+prun", [nuc, prun]),
      ("frigider+televizor", [frigider, televizor]), ("uşă+masă", [usa, masa])],
      ∀ g ∈ row.parse? "resolved" [("masc", Value.masc), ("fem", .fem)],
        (row.judgment = .acceptable ↔ resolve Romanian.rules cs = some g) := by
  decide +kernel

theorem ojibwa_rows : ∀ row ∈ Examples.all, row.language = "ojib1241" →
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
theorem swahili_rows : ∀ row ∈ Examples.all, row.language = "swah1253" →
    ∀ n ∈ row.parse? "noun" (allNouns.map fun n ↦ (n.form, n)),
      ∀ g ∈ row.parse? "concord" [("1/2", Gender.genderA), ("3/4", .genderB), ("7/8", .genderD)],
        (row.judgment = .acceptable ↔ Swahili.system.assign Swahili.sem Noun.morphClass n = g) := by
  decide +kernel

end Corbett1991
