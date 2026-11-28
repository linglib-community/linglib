module

public import Linglib.Core.Data.List.DropRight
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Linglib.Syntax.Feature.Gender.AgreementClasses
public import Linglib.Semantics.Plurality.Cardinality
public import Linglib.Semantics.Plurality.Configuration
public import Linglib.Syntax.Agreement.ConjunctAgreement
public import Linglib.Syntax.Feature.Bundle
public import Linglib.Languages.Bayso.Number
public import Linglib.Languages.Teop.Nouns
public import Studies.Corbett1991
public import Linglib.Syntax.Clause.Basic
public import Linglib.Data.Examples.Corbett2000
public import Linglib.Data.Statistics.Corbett2000
public import Linglib.Data.Examples.Gloss
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Morphology.Word.Bundle
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

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
  `Agreement.ConjunctAgreement`; those found are agreement with the nearest conjunct, with the
  first and with all, which leaves out the last conjunct when it is the more distant. An
  example fits an option when its target agrees in φ-features (`Agreement.Bundle.index`) with
  the conjunct the option picks or with the resolved
  features, all read off the glosses' category labels (`GlossedWord.features`), a conjunct
  whose gloss marks no number being singular; the target's side is read off the order of the
  words.
* Number resolution is the book's rule and is shown to be the substrate's resolution, the
  value of the sum of the conjuncts' referents; the counts of chapter 6 are the tables of
  `Data/Statistics/Corbett2000.json`, with the book's readings of them as theorems. A cell of
  Table 6.11 printed with a percentage is read as admitting the other number as the less frequent
  variant, and the Slovene adjective, printed *pl(SG)*, is read as *pl/(SG)*.
* Second systems and constructed numbers are represented by what their forms cover; the
  data of Kiowa, Hopi, Rembarrnga and the Slavonic honorifics live here for want of
  language files.

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
  c.divisions.rtake c.facultative

/-- The substrate's system. -/
def toSystem (c : Choices) : Finset Number :=
  c.values.toFinset

theorem facultativeValues_suffix (c : Choices) : c.facultativeValues <:+ c.divisions :=
  List.rtake_suffix _ _

theorem toSystem_determinateInitial (c : Choices) : Number.DeterminateInitial c.toSystem := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  change Number.DeterminateInitial (Choices.mk ⟨d, p, gp⟩ .none 0).toSystem
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
def piraha : Finset Number := ∅

/-- Rembarrnga has minimal, unit augmented and augmented, Table 5.18. -/
def rembarrnga : Finset Number :=
  {.minimal, .unitAugmented, .augmented}

/-- Ilocano has minimal and augmented, Table 5.20. -/
def ilocano : Finset Number := {.minimal, .augmented}

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
abbrev Range := AnimacyHierarchy → Obligatoriness

namespace Range

/-- By constraint III, the likelihood of number being distinguished never increases rightwards
along the hierarchy, downwards in the substrate's order. -/
abbrev Respects (r : Range) : Prop := Monotone r

-- Constraint I
theorem Respects.isUpperSet {r : Range} (h : r.Respects) : IsUpperSet (Obligatoriness.possible r) :=
  (Obligatoriness.monotone_iff.1 h).2

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

open Person (Configuration)

/-- The traditional analysis of Table 5.17 counts the members of a referent. -/
def traditional (x : Configuration) : Number :=
  if x.card ≤ 1 then .singular else if x.card = 2 then .dual
  else if x.card = 3 then .trial else .plural

/-- The minimal-augmented analysis of Table 5.18 counts the others beyond the logical minimum
of the referent's person, two members for the speaker with the addressee and one otherwise. -/
def relative (x : Configuration) : Number :=
  if x.others ≤ Configuration.minimum x.participants then .minimal
  else if x.others = Configuration.minimum x.participants + 1 then .unitAugmented
  else .augmented

theorem unitAugmented_one_more :
    relative ⟨{.speaker, .addressee}, 1⟩ = relative ⟨{.speaker}, 1⟩ ∧
      traditional ⟨{.speaker, .addressee}, 1⟩ ≠ traditional ⟨{.speaker}, 1⟩ := by
  decide

theorem relative_eq_minimal_iff {x : Configuration} (hx : x ≠ ⊥) :
    relative x = .minimal ↔
      x ∈ Mereology.atomize (Configuration.OfParticipants x.participants) := by
  have h := Configuration.ne_bot_iff_minimum_le.1 hx
  rw [Configuration.atomize_ofParticipants_iff, Configuration.ext_iff]
  simp only [relative, true_and]
  split_ifs <;> simp <;> omega

theorem relative_eq_unitAugmented_iff {x : Configuration} (hx : x ≠ ⊥) :
    relative x = .unitAugmented ↔
      x ∈ Mereology.atomize (Number.Feature.restrict .minimal false
        (Configuration.OfParticipants x.participants)) := by
  have h := Configuration.ne_bot_iff_minimum_le.1 hx
  rw [Configuration.atomize_restrict_minimal_false_ofParticipants_iff, Configuration.ext_iff]
  simp only [relative, true_and]
  split_ifs <;> simp <;> omega

/-- Within a person the traditional values determine the minimal-augmented ones: the second
analysis draws no distinction the first lacks. -/
theorem relative_eq_of_traditional_eq {x y : Configuration} (hx : x ≠ ⊥) (hy : y ≠ ⊥)
    (hp : x.participants = y.participants) (h : traditional x = traditional y) :
    relative x = relative y := by
  obtain ⟨s, n⟩ := x
  obtain ⟨t, m⟩ := y
  obtain rfl : s = t := hp
  have hs : s.card ≤ 2 := s.card_le_univ
  have hn := Configuration.ne_bot_iff_minimum_le.1 hx
  have hm := Configuration.ne_bot_iff_minimum_le.1 hy
  have hmin : (Configuration.minimum s = 1 ∧ s.card = 0) ∨
      (Configuration.minimum s = 0 ∧ 1 ≤ s.card) := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact Or.inr ⟨Configuration.minimum_of_nonempty hne, Finset.card_pos.2 hne⟩
  simp only [traditional, relative, Configuration.card] at h ⊢
  split_ifs at h ⊢ <;> first | rfl | (exfalso; omega)

-- Table 5.17
theorem traditional_ne_of_relative_eq :
    relative ⟨{.speaker}, 2⟩ = relative ⟨{.speaker}, 3⟩ ∧
      traditional ⟨{.speaker}, 2⟩ ≠ traditional ⟨{.speaker}, 3⟩ := by
  decide

end Rembarrnga

namespace Hopi

/-- The pronoun and the verb each mark the singular against the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- The pronoun sets the singular against dual and plural, (40) to (42). -/
def pronounNumber : Number → numberSystem
  | .singular => ⟨.singular, by decide⟩
  | _ => ⟨.plural, by decide⟩

/-- The verb sets singular and dual against the plural. -/
def verbNumber : Number → numberSystem
  | .plural => ⟨.plural, by decide⟩
  | _ => ⟨.singular, by decide⟩

theorem constructed :
    ¬ (sgDuPl.map pronounNumber).Nodup ∧ ¬ (sgDuPl.map verbNumber).Nodup ∧
      (sgDuPl.map fun n ↦ (pronounNumber n, verbNumber n)).Nodup := by
  decide

/-- A referent the pronoun counts as more than one and the verb as at most two is one of two
members, the `[−atomic, +minimal]` region of its person: the two markers construct the dual. -/
theorem constructed_iff_dual {x : Person.Configuration} :
    1 < x.card ∧ x.card ≤ 2 ↔
      x ∈ Number.Feature.restrict .minimal true (Number.Feature.restrict .atomic false
        (Person.Configuration.OfParticipants x.participants)) := by
  rw [Person.Configuration.dual_ofParticipants_iff]
  exact ⟨fun h ↦ ⟨rfl, by omega⟩, fun h ↦ by omega⟩

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
def britishCommittee : Position → Option Availability :=
  fun | .attributive => some .syntacticOnly | .predicate | .relativePronoun => some .both
      | .personalPronoun => some .both

/-- American English *committee* takes plural agreement rarely in the predicate and admits it
in the personal pronoun. -/
def americanCommittee : Position → Option Availability :=
  fun | .attributive => some .syntacticOnly | .predicate => some .mostlySyntactic
      | .personalPronoun => some .both | _ => none

theorem committee_monotoneOn :
    MonotoneOn (fun i ↦ (britishCommittee i).getD .syntacticOnly)
        {i | (britishCommittee i).isSome} ∧
      MonotoneOn (fun i ↦ (americanCommittee i).getD .syntacticOnly)
        {i | (americanCommittee i).isSome} := by
  simp only [MonotoneOn, Set.mem_ofPred_eq]; exact ⟨by decide, by decide⟩

theorem corporate_percentPlural_lt :
    (corporate .predicate).percentPlural.toRat < (corporate .pronoun).percentPlural.toRat := by
  norm_num [corporate, Data.Statistics.Decimal.toRat]

-- Table 6.10
theorem judgement_noCorrection_lt :
    (judgement .us .noCorrection).percent.toRat < (judgement .nz .noCorrection).percent.toRat ∧
      (judgement .nz .noCorrection).percent.toRat <
        (judgement .gb .noCorrection).percent.toRat := by
  norm_num [judgement, Data.Statistics.Decimal.toRat]

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

instance : LinearOrder PredicateTarget := LinearOrder.lift' PredicateTarget.ctorIdx (by decide)

end PredicateTarget

/-- The availability of semantic, singular, agreement that a cell of Table 6.11 records. -/
def Mark.availability : Mark → Availability
  | .pl => .syntacticOnly
  | .plRarelySg => .mostlySyntactic
  | .either => .both
  | .sgRarelyPl => .mostlySemantic
  | .sg => .semanticOnly

/-- The availability at a cell printed with a percentage: every percentage in the table is below
one hundred, so the other number occurs as the less frequent variant. -/
def Mark.availabilityAt (m : Mark) (percent : Option Data.Statistics.Decimal) : Availability :=
  match m, percent with
  | .pl, some _ => .mostlySyntactic
  | .sg, some _ => .mostlySemantic
  | m, _ => m.availability

/-- The availability of semantic agreement with honorific *vy* at each sub-position of the
predicate. -/
def Honorific.profile (h : Honorific) : PredicateTarget → Availability
  | .verb => h.finiteVerb.availability
  | .participle => h.participle.availabilityAt h.participlePercent
  | .adjective => h.adjective.availabilityAt h.adjectivePercent
  | .noun => h.noun.availability

/-- By the Predicate Hierarchy, the likelihood of semantic agreement never decreases from the
verb to the noun, in every row of Table 6.11. -/
theorem honorific_profile_monotone : ∀ l, Monotone (honorific l).profile := by decide

/-! ### Conjoined noun phrases (§6.5) -/

/-- The number resolution rules give the dual for exactly two singular conjuncts where the
system has a dual and the plural in all other cases. -/
def resolveNumber (c : Choices) (ns : List Number) : Number :=
  if .dual ∈ c.values ∧ ns = [.singular, .singular] then .dual else .plural

theorem resolveNumber_eq_resolve :
    (∀ a ∈ slovene.values, ∀ b ∈ slovene.values,
      resolveNumber slovene [a, b] = Number.resolve slovene.toSystem a b) ∧
      ∀ a ∈ english.values, ∀ b ∈ english.values,
        resolveNumber english [a, b] = Number.resolve english.toSystem a b := by
  decide

/-- The features a conjunct's gloss marks, its number being singular where the gloss marks none,
as in the Arabic examples. -/
def conjunctFeatures (w : GlossedWord) : Morphology.Features :=
  let f := w.features
  Function.update f .number ↑((f .number).unbotD .singular)

/-- Slovene resolves the gender of conjuncts by its rules (`Corbett1991.Slovene.rules`): all
feminines take the feminine and anything else the masculine. -/
def sloveneGender (gs : List (Flat UD.Gender)) : Option UD.Gender :=
  ((gs.mapM fun (g : Option UD.Gender) ↦ g.bind fun
      | .Masc => some Slovenian.Gender.Value.masculine | .Fem => some .feminine
      | .Neut => some .neuter | .Com => none).bind (ResolutionRule.resolve Slovene.rules)).map fun
    | .masculine => .Masc | .feminine => .Fem | .neuter => .Neut

section Fits

variable (r : Morphology.Features) (d : HeadDirection) (cs : List Morphology.Features)
  (t : Morphology.Features)

/-- A target with the features `t` beside conjuncts `cs` that resolve to `r` fits the option `a`
when it agrees with what the option gives it access to: the conjunct it picks, or the resolved
features under agreement with all (§6.5.1). -/
def Fits : ConjunctAgreement → Prop
  | .all => Compat (Bundle.ofFeatures t).index (Bundle.ofFeatures r).index
  | .single e => ∃ x ∈ (ConjunctAgreement.single e).conjuncts cs,
      Compat (Bundle.ofFeatures t).index (Bundle.ofFeatures x).index

instance : DecidablePred (Fits r cs t)
  | .all => inferInstanceAs (Decidable (Compat _ _))
  | .single _ => inferInstanceAs (Decidable (∃ x ∈ _, _))

/-- A target on side `d` of the conjuncts fits the option `a` and no other of the options found,
agreement with the nearest conjunct, with the first and with all, unless the other selects
conjuncts with the same features. -/
def FitsOnly (a : ConjunctAgreement) : Prop :=
  Fits r cs t a ∧ ∀ b ∈ [.nearest d, .first, .all], Fits r cs t b →
    b.conjuncts cs = a.conjuncts cs

instance : DecidablePred (FitsOnly r d cs t) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ ∀ b ∈ [_, _, _], _))

end Fits

/-- The position of the Agreement Hierarchy a target of Table 6.12 names. -/
def Target.position : Target → Position
  | .attributive => .attributive
  | .predicate => .predicate
  | .relativePronoun => .relativePronoun
  | .personalPronoun => .personalPronoun

-- Table 6.12
theorem russianConjoined_monotone : ∀ t u : Target, t.position ≤ u.position →
    (russianConjoined t).percentPlural.toRat ≤ (russianConjoined u).percentPlural.toRat := by
  decide +kernel

/-- In every language of Table 6.13 animate conjuncts and conjuncts before the predicate each
favour resolution, whatever the other factor. -/
theorem resolution_factors : ∀ l,
    (∀ o, (resolution l o .inanimate).percentPlural.toRat <
      (resolution l o .animate).percentPlural.toRat) ∧
    ∀ a, (resolution l .predicateSubject a).percentPlural.toRat <
      (resolution l .subjectPredicate a).percentPlural.toRat := by
  decide +kernel

theorem animacy_vs_precedence :
    (∀ l ∈ [ConjoinedLanguage.medievalSpanish, .german],
      (resolution l .subjectPredicate .inanimate).percentPlural.toRat <
        (resolution l .predicateSubject .animate).percentPlural.toRat) ∧
    (resolution .serboCroat .predicateSubject .animate).percentPlural.toRat <
      (resolution .serboCroat .subjectPredicate .inanimate).percentPlural.toRat := by
  decide +kernel

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
def markingNames : List (String × Obligatoriness) :=
  [("obligatory", .obligatory), ("optional", .optional), ("excluded", .excluded)]

-- (24), (28), Table 3.6
theorem miya_rows : ∀ row ∈ Examples.all, row.language = .miya →
    ∀ p ∈ row.parse? "position" rankNames,
      (∀ m ∈ row.parse? "marking" markingNames, m = miyaMarking p) ∧
        ∀ a ∈ row.parse? "agreement" markingNames, a = miyaAgreement p := by
  decide +kernel

-- (21), (23), (5), (6)
theorem agreement_rows : ∀ row ∈ Examples.all, ∀ p ∈ row.parse? "position" rankNames,
    ∀ a ∈ row.parse? "agreement" markingNames,
      (row.language = .muna → a = munaAgreement p) ∧
        (row.language = .bininjKunWok → a = mayaliAgreement p) := by
  decide +kernel

-- (2), (4)
theorem slave_rows : ∀ row ∈ Examples.all, row.language = .slave →
    ∀ p ∈ row.parse? "position" rankNames, ∀ m ∈ row.parse? "marking" markingNames,
      m = slave.range .plural p ∨ p = .higherAnimate := by
  decide +kernel

-- (1), (3)
theorem hebrew_rows : ∀ row ∈ Examples.all, row.language = .modernHebrew →
    ∀ c ∈ row.parse? "controller" numberNames, ∀ t ∈ row.parse? "target" numberNames,
      Number.coarsen ({} : Choices).toSystem c = t := by
  decide +kernel

-- (12), (14)
theorem default_rows : ∀ row ∈ Examples.all, ∀ d ∈ row.parse? "default" numberNames,
    (row.language = .english → d = .singular) ∧ (row.language = .kiowa → d = .plural) := by
  decide +kernel

-- (1), (4), (11)
theorem bayso_rows : ∀ row ∈ Examples.all, row.language = .baiso →
    ∀ n ∈ row.parse? "noun" (Bayso.allNouns.map fun n ↦ (n.form, n)),
    ∀ v ∈ row.parse? "number" [("general", (⟨.general, by decide⟩ : Bayso.nounNumbers)),
      ("singular", ⟨.singular, by decide⟩), ("paucal", ⟨.paucal, by decide⟩),
      ("plural", ⟨.plural, by decide⟩)],
      (∀ f ∈ row.feature? "form", f = n.formAt v) ∧
        ∀ c ∈ row.parse? "concord" [("masc", Bayso.Concord.masc), ("fem", .fem),
          ("plural", .plural)], c = n.gender.concord v := by
  decide +kernel

/-- `conjuncts? row` lists the features of a row's conjuncts, in order. -/
def conjuncts? (row : Datum) : Option (List Morphology.Features) :=
  (row.features "conjunct").mapM fun w ↦ (row.glossedWord? w).map conjunctFeatures

/-- `target? row` is the features a row's target marks. -/
def target? (row : Datum) : Option Morphology.Features :=
  ((row.feature? "targetForm").bind row.glossedWord?).map (·.features)

/-- `targetSide? row` is the side of the conjuncts a row's target is on, read off the order of its
words, head-initial if it precedes them. -/
def targetSide? (row : Datum) : Option HeadDirection :=
  (row.feature? "targetForm").bind fun t ↦ (row.features "conjunct").head?.map fun c ↦
    if row.surfaceTokens.idxOf t < row.surfaceTokens.idxOf c then .headInitial else .headFinal

/-- `resolved? row` is what a row's conjuncts resolve to: their number by the rules of §6.5.2 in
the language's system and, in Slovene, their gender. Cassubian and Moroccan Arabic are given the
two values of Russian; no example of theirs has a dual. -/
def resolved? (row : Datum) : Option Morphology.Features :=
  (conjuncts? row).bind fun cs ↦
    let number (c : Choices) := some (resolveNumber c (cs.filterMap fun x ↦ x .number))
    row.byLanguage [(.slovenian, Morphology.Features.of (number := number slovene)
        (gender := sloveneGender (cs.map (· .gender)))),
      (.russian, .of (number := number russian)), (.kashubian, .of (number := number russian)),
      (.moroccanArabic, .of (number := number russian))]

/-- Each conjoined example fits the option Corbett names for it, and no other of the options
found unless that one selects conjuncts with the same features (§6.5.1). -/
theorem conjoined_rows : ∀ row ∈ Examples.all,
    ∀ a ∈ row.parse? "conjunctAgreement"
      [("nearest", ConjunctAgreement.nearest), ("first", fun _ ↦ .first), ("all", fun _ ↦ .all)],
    ∃ cs ∈ conjuncts? row, ∃ t ∈ target? row, ∃ d ∈ targetSide? row, ∃ r ∈ resolved? row,
      FitsOnly r d cs t (a d) := by
  decide +kernel

-- (28), (30)
theorem macedonian_rows : ∀ row ∈ Examples.all, row.language = .macedonian →
    ∀ t ∈ row.parse? "target" [("verb", PredicateTarget.verb), ("participle", .participle),
      ("adjective", .adjective), ("noun", .noun)],
    ∀ k ∈ row.parse? "agreement" [("plural", Kind.syntactic), ("singular", .semantic)],
      (row.judgment = .acceptable ↔ ((honorific .macedonian).profile t).Allows k) := by
  decide +kernel

-- (19), (22)
theorem committee_rows : ∀ row ∈ Examples.all, row.language = .english →
    ∀ t ∈ row.parse? "target" positionNames, ∀ k ∈ row.parse? "agreement" kindNames,
    ∀ a ∈ britishCommittee t, (row.judgment = .acceptable ↔ a.Allows k) := by
  decide +kernel

-- (40), (42)
theorem hopi_rows : ∀ row ∈ Examples.all, row.language = .hopi →
    ∀ p ∈ row.parse? "pronoun"
      [("sg", ⟨.singular, by decide⟩), ("pl", ⟨.plural, by decide⟩)],
    ∀ v ∈ row.parse? "verb"
      [("sg", ⟨.singular, by decide⟩), ("pl", ⟨.plural, by decide⟩)],
    ∀ n ∈ row.parse? "number" numberNames,
      Hopi.pronounNumber n = p ∧ Hopi.verbNumber n = v := by
  decide +kernel

-- (21), (23)
theorem kiowa_rows : ∀ row ∈ Examples.all, row.language = .kiowa →
    ∀ k ∈ row.parse? "class" [("animate", Kiowa.Class.animate), ("inanimate", .inanimate)],
    ∀ n ∈ row.parse? "number" numberNames,
    ∀ i ∈ row.parse? "inverse" [("yes", true), ("no", false)],
      (i = true ↔ Kiowa.Inverse k n) := by
  decide +kernel

-- (40), (41)
theorem hungarian_rows : ∀ row ∈ Examples.all, row.language = .hungarian →
    ∀ an ∈ row.parse? "animate" [("yes", true), ("no", false)],
    ∀ r ∈ row.parse? "agreement" numberNames,
      (row.judgment = .acceptable ↔ (r = .singular ∨ an = true)) := by
  decide +kernel

-- (42), (44), p. 202
theorem moroccan_rows : ∀ row ∈ Examples.all, row.language = .moroccanArabic →
    ∃ cs ∈ conjuncts? row, ∃ t ∈ target? row, ∃ d ∈ targetSide? row, ∃ r ∈ resolved? row,
      (row.judgment = .acceptable ↔
        Fits r cs t .all ∨ d = .headInitial ∧ Fits r cs t (.nearest d)) := by
  decide +kernel

end Corbett2000
