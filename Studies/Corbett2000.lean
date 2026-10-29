module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Linglib.Syntax.Gender.AgreementClasses
public import Linglib.Syntax.Number.Resolve
public import Linglib.Syntax.Agreement.ConjunctAgreement
public import Linglib.Fragments.Bayso.Number
public import Linglib.Fragments.Teop.Nouns
public import Studies.Corbett1991
public import Linglib.Syntax.Clause.Basic
public import Linglib.Data.Examples.Corbett2000

/-!
# Corbett (2000): Number

This file formalizes the typology of number of [corbett-2000]. Number has more shape than the
singular and plural of English. A language may express a noun's meaning outside the number
system, the general number of Bayso, with a form of its
own, or of Japanese, where the general form is the singular's; within the system the values
are chosen in order, the determinate dual and trial dividing the plural before the
indeterminate paucals and greater plural divide it further, so that the systems from
Russian's two values to Lihir's five are the sequences of binary choices, and a facultative
value, one whose use is not required, can only be a last choice, every choice after it
facultative too. Which nominals distinguish number follows the Animacy Hierarchy, from the
speaker through the addressee, the third person, kin and humans to animates and inanimates:
the likelihood of number being distinguished never increases rightwards, so that a value's
range is a top segment, each further choice has a range no wider than the choice before it,
and obligatory marking lies above facultative. Minor numbers, the Hebrew dual or the Avar
paucal, escape the hierarchy but only inside systems attested with and without them;
associativity is a category of its own; and a second system lower on the hierarchy may
conflate values or add a mass number no top system has. Number is expressed by words,
syntax, morphology and suppletion, and by three arrangements that add no values outside the
typology: inverse marking, minimal-augmented paradigms, and numbers constructed from two
coarser markings. In syntax, controller and target numbers may differ in system, in default,
or for particular controllers, the corporate nouns of English and the honorific plurals of
Slavonic taking semantic agreement in the measure the Agreement Hierarchy and the Predicate
Hierarchy allow; conjoined noun phrases take agreement with the nearest conjunct or with all,
resolved to the dual for two singulars where there is one and to the plural otherwise,
resolution favoured by animacy and precedence. Verbal number, of events or of participants,
is a category apart. The book's examples are the rows of `Data/Examples/Corbett2000.json`.

## Implementation notes

* A system is the book's sequence of binary choices: a shape, how many determinate and how
  many indeterminate choices are made and whether a greater plural is, with the kind of
  general number and how many final choices are facultative. The substrate's system, its
  values and its facultative values, is derived from the choices, and in every system the
  determinate values are an initial segment, by enumeration of the finite type of shapes.
* A range is a function from the positions of the Animacy Hierarchy, with the animate position
  split as Miya needs, to a three-way
  marking; constraint III of chapter 3 is monotonicity, the top-segment constraint I a
  theorem of it, and constraints I–III of chapter 4 are read as a pointwise order between
  successive choices, which is stronger than their letter. The optional marking of chapter 3,
  Kannada's or Comanche's, is the general number of a second system in chapter 4, not a
  facultative value: the profiles carry chapter 3's presentation, the second systems chapter
  4's.
* Corporate nouns and the honorific plurals reuse the hybrid profiles and availabilities of
  Corbett's typology of gender; the Predicate Hierarchy is a linear order on the predicate's
  four sub-positions, and the rows of Table 6.11 are profiles over it.
* The options for agreement with conjoined noun phrases (§6.5.1) are the substrate's
  `Agreement.ConjunctAgreement`, which derives the exclusion of the more distant last conjunct
  (`Agreement.ConjunctAgreement.eq_nearest_of_conjuncts_eq_singleton`).
* Number resolution is the book's rule and is shown to be the substrate's resolution, the
  value of the sum of the conjuncts' referents; the corpus tables are typed here, in percentages,
  with the book's readings of them as theorems.
* Second systems and constructed numbers are represented by what their forms cover; the
  data of Kiowa, Hopi, Rembarrnga and the Slavonic honorifics live here for want of
  fragments.

## TODO

* Japanese's table of plural marking by referent and noun-phrase type, the count and mass
  effects of §3.6 and §3.7, distributives and collectives, agreement with quantified
  expressions, the special uses of chapter 7 and verbal number are prose only.
* Constraint IV, the relative size of a minor number, Table 5.22's defectives, the mass
  form of the dialects of north-west Spain, which has no value in the substrate, and the
  irregular plurals of Bayso are not modelled.

## References

* [corbett-2000]
* [corbett-1991]
* [corbett-1998]
* [corbett-1979]
* [comrie-1975]
* [smith-stark-1974]
* [corbett-hayward-1987]
-/

@[expose] public section

namespace Corbett2000

open Agreement Corbett1991

/-- Singular, dual and plural. -/
def sgDuPl : List Number := [.singular, .dual, .plural]

/-! ### Number values and systems (chapter 2) -/

/-- The shape of a system records the choices that fix its values, how many of the determinate
values, dual then trial, divide the plural, how many paucals, a paucal then a greater paucal,
divide it further, and whether a greater plural does. -/
structure Shape where
  /-- The determinate choices made, in order none, the dual, or the dual and the trial. -/
  determinate : Fin 3 := 0
  /-- The indeterminate choices made, none, a paucal, or a paucal and a greater paucal. -/
  indeterminate : Fin 3 := 0
  /-- Whether the plural is divided by a greater plural. -/
  greaterPlural : Bool := false
  deriving DecidableEq, Repr, Fintype

namespace Shape

/-- The values of a shape in order, the singular and plural with the choices between. -/
def values (s : Shape) : List Number :=
  .singular :: ([Number.dual, .trial].take s.determinate ++
    [Number.paucal, .greaterPaucal].take s.indeterminate ++
      .plural :: (if s.greaterPlural then [.greaterPlural] else []))

end Shape

/-- General number, the meaning outside the number system, is expressed not at all, by a form
of its own, as in Bayso, or by the singular's form, as in Japanese. General
meaning in the plural's form is found for particular nouns, in Arbore, never as a system. -/
inductive General where
  | none
  | separate
  | withSingular
  deriving DecidableEq, Repr, Fintype

/-- A number system is the book's sequence of binary choices, given by its shape, the kind of
general number, and how many of the choices, counted from the last, are facultative. -/
structure Choices extends Shape where
  /-- The kind of general number. -/
  general : General := .none
  /-- How many of the choices, from the last, are facultative; all of them when the count
  exceeds them. -/
  facultative : Fin 6 := 0
  deriving DecidableEq, Repr, Fintype

namespace Choices

/-- The values the choices carve from the plural, in the order they are made. -/
def divisions (c : Choices) : List Number :=
  c.values.filter fun v ↦ v ≠ .singular ∧ v ≠ .plural

/-- The facultative values are the last choices. -/
def facultativeValues (c : Choices) : List Number :=
  c.divisions.drop (c.divisions.length - c.facultative)

/-- The substrate's system. -/
def toSystem (c : Choices) : Number.System :=
  { values := c.values.toFinset, hasGeneral := decide (c.general ≠ .none),
    facultative := c.facultativeValues.toFinset }

theorem facultativeValues_suffix (c : Choices) : c.facultativeValues <:+ c.divisions :=
  List.drop_suffix _ _

theorem toSystem_determinateInitial (c : Choices) : c.toSystem.DeterminateInitial := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  change (Choices.mk ⟨d, p, gp⟩ .none 0).toSystem.DeterminateInitial
  fin_cases d <;> fin_cases p <;> cases gp <;> decide

theorem paucal_mem_facultativeValues_of_dual_mem (c : Choices)
    (hd : .dual ∈ c.facultativeValues) (hp : .paucal ∈ c.divisions) :
    .paucal ∈ c.facultativeValues := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  revert d p gp f hd hp
  cases g <;> decide

end Choices

/-- Russian has singular and plural, both obligatory. -/
def russian : Choices := {}

/-- English has Russian's system. -/
def english : Choices := russian

/-- Sanskrit has an obligatory dual. -/
def sanskrit : Choices := { determinate := 1 }

/-- Upper Sorbian has Sanskrit's system. -/
def upperSorbian : Choices := sanskrit

/-- Slovene has a facultative dual. -/
def slovene : Choices := { determinate := 1, facultative := 1 }

/-- Maŋarayi, and Tuyuca's conflated system, have dual and trial, all obligatory. -/
def dualTrial : Choices := { determinate := 2 }

/-- Ngan'gityemerri has dual and trial, the trial facultative. -/
def ngangityemerri : Choices := { determinate := 2, facultative := 1 }

/-- Larike has dual and trial, both facultative. -/
def larike : Choices := { determinate := 2, facultative := 2 }

/-- Yimas has dual and paucal. -/
def yimas : Choices := { determinate := 1, indeterminate := 1 }

/-- Longgu has dual and paucal, both facultative in the subject pronouns. -/
def longgu : Choices := { determinate := 1, indeterminate := 1, facultative := 2 }

/-- Walapai has paucal and plural, the system Bayso's nouns oppose to their general
number. -/
def walapai : Choices := { indeterminate := 1 }

/-- Bayso has Walapai's values with a general number of its own. -/
def bayso : Choices := { walapai with general := .separate }

/-- Lihir has dual, trial and paucal. -/
def lihir : Choices := { determinate := 2, indeterminate := 1 }

/-- Marshallese has Lihir's system with every choice facultative. -/
def marshallese : Choices := { determinate := 2, indeterminate := 1, facultative := 3 }

/-- Sursurunga has dual and two paucals; Figure 2.7 misprints the greater paucal as a greater
plural, against §2.2.5 and the position of the branch. -/
def sursurunga : Choices := { determinate := 1, indeterminate := 2 }

/-- Mokilese has dual and a greater plural. -/
def mokilese : Choices := { determinate := 1, greaterPlural := true }

/-- Mele-Fila has dual, paucal and greater plural, constructed from article and pronoun. -/
def meleFila : Choices := { determinate := 1, indeterminate := 1, greaterPlural := true }

/-- Kaytetye has dual and greater plural, the general number sharing the singular's form. -/
def kaytetye : Choices := { determinate := 1, greaterPlural := true, general := .withSingular }

/-- Japanese has general number in the singular's form. -/
def japanese : Choices := { general := .withSingular }

/-- Hamer has a general form of its own, singular, plural and global plural. -/
def hamer : Choices := { greaterPlural := true, general := .separate }

/-- Pirahã has no number at all. -/
def piraha : Number.System := { values := ∅ }

/-- Rembarrnga has minimal, unit augmented and augmented, Table 5.18. -/
def rembarrnga : Number.System :=
  { values := {.minimal, .unitAugmented, .augmented} }

/-- Ilocano has minimal and augmented, Table 5.20. -/
def ilocano : Number.System := { values := {.minimal, .augmented} }

/-! ### The Animacy Hierarchy (chapters 3 and 4) -/

/-- The Animacy Hierarchy of Figure 3.1, speaker > addressee > third person > kin >
human > animate > inanimate, with the animate position split into higher and lower animates
where Miya splits it (Table 3.6). -/
inductive AnimacyHierarchy where
  | inanimate
  | lowerAnimate
  | higherAnimate
  | human
  | kin
  | thirdPerson
  | addressee
  | speaker
  deriving DecidableEq, Repr, Fintype

/-- The rank on the hierarchy, 0 for the inanimates up to 7 for the speaker. -/
def AnimacyHierarchy.rank : AnimacyHierarchy → ℕ
  | .inanimate => 0
  | .lowerAnimate => 1
  | .higherAnimate => 2
  | .human => 3
  | .kin => 4
  | .thirdPerson => 5
  | .addressee => 6
  | .speaker => 7

instance : LinearOrder AnimacyHierarchy := LinearOrder.lift' AnimacyHierarchy.rank (by decide)

/-- The range of a number value says whether it is distinguished at each position of the
hierarchy obligatorily, optionally or not at all, ordered by the likelihood of number being
distinguished. -/
abbrev Range := AnimacyHierarchy → Clause.Occurrence

namespace Range

/-- By constraint III, the likelihood of number being distinguished never increases rightwards
along the hierarchy, downwards in the substrate's order. -/
abbrev Respects (r : Range) : Prop := Monotone r

-- Constraint I
theorem Respects.isUpperSet {r : Range} (h : r.Respects) : IsUpperSet {p | ⊥ < r p} :=
  (isUpperSet_Ioi _).preimage h

/-- The range obligatory down to `o`, optional down to `f`, excluded below. -/
def downTo (o f : AnimacyHierarchy) : Range :=
  fun p ↦ if o ≤ p then .obligatory else if f ≤ p then .optional else ⊥

theorem downTo_respects (o f : AnimacyHierarchy) : (downTo o f).Respects := by
  revert o f; decide

end Range

/-- The ranges of a language's number values, from the plural on through its choices. -/
structure Profile where
  /-- The language. -/
  language : String
  /-- Its system. -/
  system : Choices
  /-- The range of each value. -/
  range : Number → Range

/-- By constraints I to III of chapter 4, with III of chapter 3, every range respects the
hierarchy, and each choice's range is nowhere wider than the previous choice's, facultative
use counting as narrower than obligatory. -/
def Profile.Respects (p : Profile) : Prop :=
  (∀ v ∈ (.plural :: p.system.divisions), (p.range v).Respects) ∧
    List.IsChain (fun v w ↦ ∀ q, p.range w q ≤ p.range v q) (.plural :: p.system.divisions)

instance (p : Profile) : Decidable p.Respects := by unfold Profile.Respects; infer_instance

/-- The plural and the dual over the same nominals, Figure 4.2. -/
def mansi : Profile :=
  ⟨"Mansi", sanskrit,
    fun | .plural | .dual => .downTo .inanimate .inanimate | _ => ⊥⟩

/-- The dual in the first person only, Figure 4.3. -/
def arapesh : Profile :=
  ⟨"Arapesh", sanskrit,
    fun | .plural => .downTo .inanimate .inanimate
        | .dual => .downTo .speaker .speaker | _ => ⊥⟩

/-- Pronouns with three numbers, nine nouns, mainly kin, with two, Figure 4.4. -/
def maori : Profile :=
  ⟨"Maori", sanskrit,
    fun | .plural => .downTo .kin .kin | .dual => .downTo .thirdPerson .thirdPerson | _ => ⊥⟩

/-- The paucal on pronouns only, Figure 4.6. -/
def yimasProfile : Profile :=
  ⟨"Yimas", yimas,
    fun | .plural | .dual => .downTo .inanimate .inanimate
        | .paucal => .downTo .thirdPerson .thirdPerson | _ => ⊥⟩

/-- The dual and the paucal for humans and higher animals, Figure 4.7. -/
def manam : Profile :=
  ⟨"Manam", yimas,
    fun | .plural => .downTo .inanimate .inanimate
        | .dual | .paucal => .downTo .higherAnimate .higherAnimate | _ => ⊥⟩

/-- The dual obligatory for pronouns and facultative for nouns, Figure 4.8. -/
def sloveneProfile : Profile :=
  ⟨"Slovene", slovene,
    fun | .plural => .downTo .inanimate .inanimate
        | .dual => .downTo .thirdPerson .inanimate | _ => ⊥⟩

/-- The plural obligatory down to humans and optional below. -/
def kannada : Profile :=
  ⟨"Kannada", russian, fun | .plural => .downTo .human .inanimate | _ => ⊥⟩

/-- Pronouns obligatory; the plural suffix optional for humans, and for dogs as a lexical
exception the book declines to make a position. -/
def slave : Profile :=
  ⟨"Slave", russian, fun | .plural => .downTo .thirdPerson .human | _ => ⊥⟩

/-- Dual and plural obligatory for humans, optional for animates, seldom for inanimates. -/
def comanche : Profile :=
  ⟨"Comanche", sanskrit, fun | .plural | .dual => .downTo .human .inanimate | _ => ⊥⟩

/-- The profiles of chapters 3 and 4. -/
def profiles : List Profile :=
  [mansi, arapesh, maori, yimasProfile, manam, sloveneProfile, kannada, slave, comanche]

theorem profiles_respect : ∀ p ∈ profiles, p.Respects := by decide

-- Figure 4.5
theorem not_respects_dual_wider :
    ¬ Profile.Respects ⟨"", sanskrit,
      fun | .plural => .downTo .speaker .speaker
          | .dual => .downTo .inanimate .inanimate | _ => ⊥⟩ := by
  decide

theorem facultative_optional :
    (∀ v ∈ sloveneProfile.system.facultativeValues, ∃ p, sloveneProfile.range v p = .optional) ∧
      (∃ p, kannada.range .plural p = .optional) ∧
        .plural ∉ kannada.system.facultativeValues := by
  decide

/-- Mayali marks number on the verb for humans and uses the minimal form for the rest. -/
def mayaliAgreement : Range := .downTo .human .human

/-- In Miya, Table 3.6, number marking is obligatory for humans and higher animals and
optional below. -/
def miyaMarking : Range := .downTo .higherAnimate .inanimate

/-- In Miya, Table 3.6, number agreement is obligatory for humans and higher animals and
excluded below. -/
def miyaAgreement : Range := .downTo .higherAnimate .higherAnimate

/-- In Muna plural agreement is obligatory for humans, optional for animates and excluded for
inanimates, which may carry a plural marker. -/
def munaAgreement : Range := .downTo .human .lowerAnimate

theorem tests_respect :
    miyaMarking.Respects ∧ miyaAgreement.Respects ∧ munaAgreement.Respects ∧
      mayaliAgreement.Respects := by
  decide

/-! ### Minor numbers (§4.2) -/

/-- By constraints VI and VII, a minor number's system and the system without it are both
possible systems of values. -/
def Dispensable (c : Choices) (minor : List Number) : Prop :=
  (∀ v ∈ minor, v ∈ c.divisions) ∧ ∃ s : Shape, s.values = c.values.filter (· ∉ minor)

instance (c : Choices) (minor : List Number) : Decidable (Dispensable c minor) := by
  unfold Dispensable; infer_instance

-- Figure 4.11
theorem hebrew_dispensable : Dispensable sanskrit [.dual] := by decide

theorem avar_dispensable : Dispensable walapai [.paucal] := by decide

theorem mangarayi_dispensable : Dispensable dualTrial [.trial] := by decide

-- Constraint VII
theorem not_dispensable_dual_of_trial : ¬ Dispensable dualTrial [.dual] := by decide

/-- The Hebrew dual, on a few nouns for measures of time and facultative there. -/
def hebrewDual : Range := fun p ↦ if p = .inanimate then .optional else ⊥

theorem hebrewDual_not_respects :
    ¬ hebrewDual.Respects ∧
      ∀ p, hebrewDual p ≤ Range.downTo .inanimate .inanimate p := by
  decide

/-! ### Top and second systems (§4.5) -/

/-- A second system operates below the top system on the hierarchy, and is one of chapter 2's
systems, general number included, as Yimas's dual–plural nouns, Qafar's, Japanese's,
Kaytetye's and Bayso's general number; one conflating every value but the plural, constraint
IX, as Pame's and Kala Lagaw Ya's inanimates, Tuyuca's, and Larike's non-humans; or the mass
number of the dialects of north-west Spain. Constraint VIII, that conflated systems are
second systems, holds by construction. -/
inductive Second where
  | regular (c : Choices)
  | conflated (c : Choices)
  | mass
  deriving DecidableEq, Repr

/-- Each form of a second system covers a set of values, a regular system having its general
form, if any, and one form per value, and a conflated system one form for every value but the
plural and one for the plural; the mass form has no value in the substrate and is not listed. -/
def Second.cells : Second → List (Finset Number)
  | .regular c => (if c.general = .none then [] else [{.general}]) ++ c.values.map (fun v ↦ {v})
  | .conflated c => [c.values.toFinset.erase .plural, {.plural}]
  | .mass => [{.singular}, {.plural}]

-- Figure 4.18
theorem qafar_cells :
    (Second.regular japanese).cells = [{.general}, {.singular}, {.plural}] := by decide

-- Figure 4.16
theorem tuyuca_cells :
    (Second.conflated dualTrial).cells = [{.singular, .dual, .trial}, {.plural}] := by decide

/-! ### The expression of number (chapter 5) -/

namespace Kiowa

/-- The two main classes of noun, Table 5.13. -/
inductive Class where
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- The basic, unmarked numbers of each class are one and two for animates and two and more
for inanimates. -/
def basic : Class → List Number
  | .animate => [.singular, .dual]
  | .inanimate => [.dual, .plural]

/-- The inverse suffix marks the number outside the basic ones. -/
def Inverse (k : Class) (n : Number) : Prop := n ∉ basic k

instance (k : Class) (n : Number) : Decidable (Inverse k n) := by unfold Inverse; infer_instance

/-- The verb's object marking, (21) to (23), distinguishes the singular, the dual, and the
inverse for the plural. -/
inductive ObjectMarker where
  | sg
  | du
  | inv
  deriving DecidableEq, Repr, Fintype

/-- The verb's object marker for each of the three numbers. -/
def verbObject : Number → ObjectMarker
  | .singular => .sg
  | .dual => .du
  | _ => .inv

theorem noun_conflates_verb_not :
    ¬ (sgDuPl.map fun n ↦ decide (Inverse .animate n)).Nodup ∧
      ¬ (sgDuPl.map fun n ↦ decide (Inverse .inanimate n)).Nodup ∧
        (sgDuPl.map verbObject).Nodup := by
  decide

end Kiowa

-- Table 5.15, Table 5.16
theorem teop_inverse :
    Morphology.Polar (fun (c : {c : Teop.NounClass // c ≠ .e}) pl ↦ Teop.headArticle c pl) ∧
      ¬ Morphology.Polar Teop.headArticle ∧ Gender.Faithful Teop.headArticle :=
  ⟨by decide, fun h ↦ absurd h.card_le_two (by decide), by decide⟩

namespace Rembarrnga

/-- The logical minimum of referents is two for the inclusive and one otherwise. Beside the
inclusive, the first person of Rembarrnga is the exclusive. -/
def minimum : Person → ℕ
  | .firstInclusive => 2
  | _ => 1

/-- In the minimal-augmented analysis of Table 5.18, the form for at least the minimum of
referents counts those beyond it. -/
def relative (p : Person) (n : ℕ) : Number :=
  match n - minimum p with
  | 0 => .minimal
  | 1 => .unitAugmented
  | _ => .augmented

theorem unitAugmented_one_more :
    relative .firstInclusive 3 = relative .firstExclusive 2 ∧
      Number.fromCard 3 ≠ Number.fromCard 2 := by
  decide

end Rembarrnga

namespace Hopi

/-- The pronoun and the verb each mark the singular against the plural. -/
def numberSystem : Number.System := .singularPlural

/-- The pronoun sets the singular against dual and plural, (40) to (42). -/
def pronounNumber : Number → numberSystem.values
  | .singular => (numberSystem.value .singular)
  | _ => (numberSystem.value .plural)

/-- The verb sets singular and dual against the plural. -/
def verbNumber : Number → numberSystem.values
  | .plural => (numberSystem.value .plural)
  | _ => (numberSystem.value .singular)

theorem constructed :
    ¬ (sgDuPl.map pronounNumber).Nodup ∧ ¬ (sgDuPl.map verbNumber).Nodup ∧
      (sgDuPl.map fun n ↦ (pronounNumber n, verbNumber n)).Nodup := by
  decide

end Hopi

/-- Whether a noun distinguishes number semantically, syntactically by agreement, and
morphologically, Table 5.21. -/
structure Differentiability where
  /-- Individuals against collections of them. -/
  semantic : Bool
  /-- Distinct agreements. -/
  syntactic : Bool
  /-- Distinct forms. -/
  morphological : Bool
  deriving DecidableEq, Repr, Fintype

namespace Differentiability

/-- Morphological differentiation entails syntactic, and syntactic semantic. -/
abbrev Valid (d : Differentiability) : Prop :=
  (d.morphological → d.syntactic) ∧ (d.syntactic → d.semantic)

/-- *dog* is differentiated in every way. -/
def dog : Differentiability := ⟨true, true, true⟩

/-- *sheep* has no distinct forms. -/
def sheep : Differentiability := ⟨true, true, false⟩

/-- *scissors* is countable, with one form and one agreement. -/
def scissors : Differentiability := ⟨true, false, false⟩

/-- *friendliness* is off the scale. -/
def friendliness : Differentiability := ⟨false, false, false⟩

theorem valid_iff (d : Differentiability) : d.Valid ↔ d ∈ [dog, sheep, scissors, friendliness] := by
  revert d; decide

end Differentiability

/-! ### The syntax of number (chapter 6) -/

-- Table 6.5
theorem bayso_pronounConcord_surjective :
    Function.Surjective (Function.uncurry Bayso.Gender.pronounConcord) := by decide

theorem bayso_concord_not_injective :
    ¬ Function.Injective (Function.uncurry Bayso.Gender.concord) := by decide

/-! ### The Agreement Hierarchy (§6.2) -/

/-- British English *committee* takes syntactic agreement only in attributive position and
either agreement elsewhere, (19) to (22). -/
def britishCommittee : Hybrid Position :=
  fun | .attributive => some .syntacticOnly | .predicate | .relativePronoun => some .both
      | .personalPronoun => some .both

/-- American English *committee* takes plural agreement rarely in the predicate and admits it
in the personal pronoun. -/
def americanCommittee : Hybrid Position :=
  fun | .attributive => some .syntacticOnly | .predicate => some .mostlySyntactic
      | .personalPronoun => some .both | _ => none

theorem committee_respectHierarchy :
    RespectsHierarchy britishCommittee ∧ RespectsHierarchy americanCommittee := by decide

/-- Nixon's corpus gives the percentage of plural agreement with corporate nouns by target, the
pronouns pooling the possessive with the personal. -/
def nixon : Position → Option ℚ
  | .attributive => some 0
  | .predicate => some (122 / 10)
  | .personalPronoun => some (274 / 10)
  | _ => none

theorem nixon_respectsHierarchy : RespectsHierarchy nixon := by decide +kernel

/-- The varieties of English. -/
inductive Variety where
  | british
  | american
  | newZealand
  deriving DecidableEq, Repr, Fintype

/-- Table 6.10 gives the percentage of respondents accepting *the audience were enjoying*. -/
def acceptance : Variety → ℚ
  | .british => 772 / 10
  | .american => 54 / 10
  | .newZealand => 725 / 10

theorem acceptance_diverges :
    acceptance .american < acceptance .newZealand ∧
      acceptance .newZealand < acceptance .british := by
  norm_num [acceptance]

/-! ### The Predicate Hierarchy (§6.4) -/

/-- The sub-positions of the predicate are, by the likelihood of semantic agreement, the finite
verb, the participle, the adjective and the noun. -/
inductive PredicateTarget where
  | verb
  | participle
  | adjective
  | noun
  deriving DecidableEq, Repr, Fintype

namespace PredicateTarget

/-- The position of a target in the Predicate Hierarchy. -/
def rank : PredicateTarget → ℕ
  | .verb => 3
  | .participle => 2
  | .adjective => 1
  | .noun => 0

theorem rank_injective : Function.Injective rank := by decide

instance : LinearOrder PredicateTarget := LinearOrder.lift' rank rank_injective

end PredicateTarget

/-- Agreement with the honorific plural *vy* in a Slavonic language (Table 6.11) records the
availability of singular, semantic, agreement at each sub-position. -/
structure Honorific where
  /-- The language. -/
  language : String
  /-- The availability of semantic agreement at each sub-position. -/
  profile : PredicateTarget → Availability

namespace Honorific

/-- A row of the table gives the language and its four sub-positions. -/
def ofRow (language : String) (v p a n : Availability) : Honorific :=
  ⟨language, fun | .verb => v | .participle => p | .adjective => a | .noun => n⟩

/-- By the Predicate Hierarchy, the likelihood of semantic agreement never decreases from the
verb to the noun. -/
abbrev Respects (h : Honorific) : Prop := Antitone h.profile

end Honorific

/-- In Macedonian, (28) to (30), the verb and participle are plural, the adjective singular for
preference and the noun singular. -/
def macedonian : Honorific :=
  .ofRow "Macedonian" .syntacticOnly .syntacticOnly .mostlySemantic .semanticOnly

/-- The rows of Table 6.11, the Russian adjective split into its short and long forms; the
table prints Slovene's adjective as *pl(SG)* for *pl/(SG)*. -/
def slavonic : List Honorific :=
  [.ofRow "Czech" .syntacticOnly .mostlySemantic .mostlySemantic .semanticOnly,
    .ofRow "Slovak" .syntacticOnly .mostlySyntactic .semanticOnly .semanticOnly,
    .ofRow "Lower Sorbian" .syntacticOnly .syntacticOnly .both .semanticOnly,
    .ofRow "Upper Sorbian" .syntacticOnly .mostlySemantic .mostlySemantic .semanticOnly,
    .ofRow "Polish dialects" .syntacticOnly .both .both .semanticOnly,
    .ofRow "Bulgarian" .syntacticOnly .mostlySyntactic .mostlySemantic .semanticOnly,
    macedonian,
    .ofRow "Serbo-Croat" .syntacticOnly .syntacticOnly .mostlySyntactic .semanticOnly,
    .ofRow "Slovene" .syntacticOnly .mostlySyntactic .mostlySyntactic .semanticOnly,
    .ofRow "Ukrainian" .syntacticOnly .mostlySyntactic .mostlySemantic .semanticOnly,
    .ofRow "Belarusian" .syntacticOnly .syntacticOnly .semanticOnly .semanticOnly,
    .ofRow "Russian, short-form adjective"
      .syntacticOnly .syntacticOnly .mostlySyntactic .semanticOnly,
    .ofRow "Russian, long-form adjective"
      .syntacticOnly .syntacticOnly .mostlySemantic .semanticOnly]

theorem slavonic_respect : ∀ h ∈ slavonic, h.Respects := by decide

/-! ### Conjoined noun phrases (§6.5) -/

/-- The number resolution rules give the dual for exactly two singular conjuncts where the
system has a dual and the plural in all other cases. -/
def resolveNumber (c : Choices) (ns : List Number) : Number :=
  if .dual ∈ c.values ∧ ns = [.singular, .singular] then .dual else .plural

theorem resolveNumber_eq_resolve :
    (∀ a ∈ slovene.values, ∀ b ∈ slovene.values,
      resolveNumber slovene [a, b] = slovene.toSystem.resolve a b) ∧
      ∀ a ∈ english.values, ∀ b ∈ english.values,
        resolveNumber english [a, b] = english.toSystem.resolve a b := by
  decide

/-- Table 6.12 gives the percentage of number resolution with Russian conjoined noun phrases by
target. -/
def russianConjoined : Position → Option ℚ
  | .attributive => some 12
  | .predicate => some 70
  | .relativePronoun => some 100
  | .personalPronoun => some 100

theorem russianConjoined_respectsHierarchy : RespectsHierarchy russianConjoined := by decide

/-- A row of Table 6.13 gives the percentage of plural predicates with conjoined subjects by the
animacy of the conjuncts and their position relative to the predicate. -/
structure Resolution where
  /-- The language. -/
  language : String
  /-- Animate conjuncts before the predicate. -/
  animateBefore : ℕ
  /-- Inanimate conjuncts before the predicate. -/
  inanimateBefore : ℕ
  /-- Animate conjuncts after the predicate. -/
  animateAfter : ℕ
  /-- Inanimate conjuncts after the predicate. -/
  inanimateAfter : ℕ
  deriving DecidableEq, Repr

/-- Medieval Spanish, Table 6.13. -/
def spanishResolution : Resolution := ⟨"Medieval Spanish", 96, 31, 69, 6⟩

/-- German, Table 6.13. -/
def germanResolution : Resolution := ⟨"German", 96, 67, 93, 40⟩

/-- Russian, Table 6.13. -/
def russianResolution : Resolution := ⟨"Russian", 100, 85, 84, 28⟩

/-- Serbo-Croat, Table 6.13. -/
def serboCroatResolution : Resolution := ⟨"Serbo-Croat", 100, 91, 70, 26⟩

/-- The rows of Table 6.13. -/
def resolutionRates : List Resolution :=
  [spanishResolution, germanResolution, russianResolution, serboCroatResolution]

theorem factors_favour_resolution :
    ∀ r ∈ resolutionRates,
      r.inanimateBefore < r.animateBefore ∧ r.animateAfter < r.animateBefore ∧
        r.inanimateAfter < r.animateAfter ∧ r.inanimateAfter < r.inanimateBefore := by
  decide

theorem animacy_vs_precedence :
    spanishResolution.inanimateBefore < spanishResolution.animateAfter ∧
      germanResolution.inanimateBefore < germanResolution.animateAfter ∧
        serboCroatResolution.animateAfter < serboCroatResolution.inanimateBefore := by
  decide

/-! ### The book's examples -/

/-- The controller numbers by name. -/
def numberNames : List (String × Number) :=
  [("general", .general), ("singular", .singular), ("dual", .dual), ("trial", .trial),
    ("paucal", .paucal), ("plural", .plural)]

/-- The positions of the hierarchy by name. -/
def rankNames : List (String × AnimacyHierarchy) :=
  [("speaker", .speaker), ("addressee", .addressee), ("thirdPerson", .thirdPerson),
    ("kin", .kin), ("human", .human), ("higherAnimate", .higherAnimate),
    ("lowerAnimate", .lowerAnimate), ("inanimate", .inanimate)]

/-- The markings by name. -/
def markingNames : List (String × Clause.Occurrence) :=
  [("obligatory", .obligatory), ("optional", .optional), ("excluded", .excluded)]

-- (24), (28), Table 3.6
theorem miya_rows : ∀ row ∈ Examples.all, row.language = "miya1266" →
    ∀ p ∈ row.parse? "position" rankNames,
      (∀ m ∈ row.parse? "marking" markingNames, m = miyaMarking p) ∧
        ∀ a ∈ row.parse? "agreement" markingNames, a = miyaAgreement p := by
  decide +kernel

-- (21), (23), (5), (6)
theorem agreement_rows : ∀ row ∈ Examples.all, ∀ p ∈ row.parse? "position" rankNames,
    ∀ a ∈ row.parse? "agreement" markingNames,
      (row.language = "muna1247" → a = munaAgreement p) ∧
        (row.language = "gunw1252" → a = mayaliAgreement p) := by
  decide +kernel

-- (2), (4)
theorem slave_rows : ∀ row ∈ Examples.all, row.language = "slav1253" →
    ∀ p ∈ row.parse? "position" rankNames, ∀ m ∈ row.parse? "marking" markingNames,
      m = slave.range .plural p ∨ p = .higherAnimate := by
  decide +kernel

-- (1), (3)
theorem hebrew_rows : ∀ row ∈ Examples.all, row.language = "hebr1245" →
    ∀ c ∈ row.parse? "controller" numberNames, ∀ t ∈ row.parse? "target" numberNames,
      ({} : Choices).toSystem.coarsen c = t := by
  decide +kernel

-- (12), (14)
theorem default_rows : ∀ row ∈ Examples.all, ∀ d ∈ row.parse? "default" numberNames,
    (row.language = "stan1293" → d = .singular) ∧ (row.language = "kiow1266" → d = .plural) := by
  decide +kernel

-- (1), (4), (11)
theorem bayso_rows : ∀ row ∈ Examples.all, row.language = "bais1246" →
    ∀ n ∈ row.parse? "noun" (Bayso.allNouns.map fun n ↦ (n.form, n)),
    ∀ v ∈ row.parse? "number" [("general", (⟨.general, by decide⟩ : Bayso.nounNumbers)),
      ("singular", ⟨.singular, by decide⟩), ("paucal", ⟨.paucal, by decide⟩),
      ("plural", ⟨.plural, by decide⟩)],
      (∀ f ∈ row.feature? "form", f = n.formAt v) ∧
        ∀ c ∈ row.parse? "concord" [("masc", Bayso.Concord.masc), ("fem", .fem),
          ("plural", .plural)], c = n.gender.concord v := by
  decide +kernel

-- (34), (37)
theorem slovene_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ cs ∈ row.parse? "conjuncts" [("sg+sg", [Number.singular, .singular]),
      ("du+sg", [.dual, .singular]), ("sg+sg+sg", [.singular, .singular, .singular])],
    ∀ r ∈ row.parse? "resolved" numberNames, r = resolveNumber slovene cs := by
  decide +kernel

-- (28), (30)
theorem macedonian_rows : ∀ row ∈ Examples.all, row.language = "mace1250" →
    ∀ t ∈ row.parse? "target" [("verb", PredicateTarget.verb), ("participle", .participle),
      ("adjective", .adjective), ("noun", .noun)],
    ∀ k ∈ row.parse? "agreement" [("plural", Kind.syntactic), ("singular", .semantic)],
      (row.judgment = .acceptable ↔ (macedonian.profile t).Allows k) := by
  decide +kernel

-- (19), (22)
theorem committee_rows : ∀ row ∈ Examples.all, row.language = "stan1293" →
    ∀ t ∈ row.parse? "target" positionNames, ∀ k ∈ row.parse? "agreement" kindNames,
    ∀ a ∈ britishCommittee t, (row.judgment = .acceptable ↔ a.Allows k) := by
  decide +kernel

-- (40), (42)
theorem hopi_rows : ∀ row ∈ Examples.all, row.language = "hopi1249" →
    ∀ p ∈ row.parse? "pronoun"
      [("sg", Hopi.numberSystem.value .singular), ("pl", Hopi.numberSystem.value .plural)],
    ∀ v ∈ row.parse? "verb"
      [("sg", Hopi.numberSystem.value .singular), ("pl", Hopi.numberSystem.value .plural)],
    ∀ n ∈ row.parse? "number" numberNames,
      Hopi.pronounNumber n = p ∧ Hopi.verbNumber n = v := by
  decide +kernel

-- (21), (23)
theorem kiowa_rows : ∀ row ∈ Examples.all, row.language = "kiow1266" →
    ∀ k ∈ row.parse? "class" [("animate", Kiowa.Class.animate), ("inanimate", .inanimate)],
    ∀ n ∈ row.parse? "number" numberNames,
    ∀ i ∈ row.parse? "inverse" [("yes", true), ("no", false)],
      (i = true ↔ Kiowa.Inverse k n) := by
  decide +kernel

-- (40), (41)
theorem hungarian_rows : ∀ row ∈ Examples.all, row.language = "hung1274" →
    ∀ an ∈ row.parse? "animate" [("yes", true), ("no", false)],
    ∀ r ∈ row.parse? "agreement" numberNames,
      (row.judgment = .acceptable ↔ (r = .singular ∨ an = true)) := by
  decide +kernel

-- (42), (44)
theorem moroccan_rows : ∀ row ∈ Examples.all, row.language = "moro1292" →
    ∀ vf ∈ row.parse? "verbFirst" [("yes", true), ("no", false)],
    ∀ a ∈ row.parse? "conjunctAgreement" [("nearest", ConjunctAgreement.nearest), ("all", .all)],
      (row.judgment = .acceptable ↔ (a = .all ∨ vf = true)) := by
  decide +kernel

end Corbett2000
