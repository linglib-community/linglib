module

public import Linglib.Morphology.DistributedMorphology.Fission
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Person.Features
public import Linglib.Data.Examples.GonzalezPootMcGinnis2006

/-!
# González Poot and McGinnis (2006): Local versus Long-Distance Fission in Distributed Morphology

González Poot and McGinnis's argument that Yucatec Maya has local but not long-distance
Fission. The verbal agreement suffixes come from one node, Agr3, which agrees with both the
ergative subject and the nominative object and is realized by strict scansion of the Vocabulary
(27) with Halle's local Fission: an item discharges its features from one of the node's
two matrices and the residue stays available to the items below (`suffixes`). The second- and
third-person plural suffixes *-éːš* and *-oʔob* are unspecified for case, so their order is fixed
by specificity whatever the grammatical roles, (19) to (22), and one scansion never inserts
*-oʔob* twice, (23) and (24) (`suffixes_rows`), whereas the object–subject template (18) predicts
exactly the starred forms (`template_rows`). Long-distance Fission is rejected: the split of
ergative person onto the auxiliary and number onto the verb, (39), crosses a word boundary, and
first-person number is a person distinction, (42), so the auxiliary and prefix Vocabularies (43)
and (44) recover every row (`aux_prefix_rows`) and derive the paradigm (39) that the paper aligns
with Hebrew, Basque, and Georgian (`ergative_paradigm`, `first_person_paradigm`). The appendix's
privative implementation over Harley and Ritter's features, (A1) to (A4), recovers the
auxiliary and the prefix (`privative_aux_prefix`) but not the suffixes: without negative values,
the nominative residue of a second-person plural object still matches *-en*, so (A4)
over-generates on (20) (`privative_suffixes`).

## Implementation notes

The person features of (26), [±PSE, ±Auth], are the substrate's [±participant, ±author]
decomposition, and [±Pl] a binary feature value. Agr3's list (27) needs the nominative
first-person plural to carry [+PSE] and the singular not to, the reverse of the assignment (42)
gives the ergative auxiliary; the paper does not reconcile the two, so `matrix` follows (27) for
nominative first person and (42) otherwise. The elsewhere *-Ø* is inserted but not counted among
a row's overt suffixes.

## References

* [gonzalez-poot-mcginnis-2006]
* [halle-1997]
* [noyer-1992]
* [halle-marantz-1993]
* [harley-ritter-2002]
-/

@[expose] public section

namespace GonzalezPootMcGinnis2006

open DistributedMorphology
open Minimalist (FeatureVal)
open scoped DistributedMorphology.VocabularyItem

/-! ### Features and matrices, sections 3 to 5 -/

/-- Yucatec Maya distinguishes the singular and the plural. -/
def numberSystem : Number.System := .singularPlural

/-- An argument is a person with a number. -/
abbrev Argument := Person × numberSystem.values

/-- The person features of (26), [±PSE, ±Auth], as the substrate's [±participant, ±author]
decomposition of a person. -/
def personFeatures (p : Person) : Finset FeatureVal :=
  {⟨.participant, decide (.participant ∈ p.toFeatures)⟩,
    ⟨.author, decide (.author ∈ p.toFeatures)⟩}

/-- Number as the feature [±Pl]. -/
def number (n : numberSystem.values) : FeatureVal := ⟨.number, n.1⟩

/-- In an ergative argument's matrix (42), first-person number is a person distinction, singular
[+PSE, +Auth] and plural [+Auth]. -/
def ergMatrix (p : Person) (n : numberSystem.values) : Finset FeatureVal :=
  match p with
  | .first =>
    numberSystem.elim {⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .erg⟩}
      {⟨.author, true⟩, ⟨.case, .erg⟩} (n := n)
  | p => personFeatures p ∪ {number n, ⟨.case, .erg⟩}

/-- An argument's matrix for Agr3 is (42) for ergative arguments and for second and third person,
and for nominative first person the one the assignment (27) presupposes, *-oʔon* 1pl [+PSE, +Auth,
NOM] and *-en* 1sg [+Auth, NOM]. -/
def matrix (p : Person) (n : numberSystem.values) (c : Case) : Finset FeatureVal :=
  match p, c with
  | .first, .nom =>
    numberSystem.elim {⟨.author, true⟩, ⟨.case, .nom⟩}
      {⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .nom⟩} (n := n)
  | p, .erg => ergMatrix p n
  | p, c => personFeatures p ∪ {number n, ⟨.case, c⟩}

/-! ### The Vocabularies (27), (43), (44) -/

/-- The Agr3 Vocabulary Items (27), in scansion order. -/
def agr3 : List (VocabularyItem FeatureVal String) :=
  [{⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .nom⟩} ⟷ "oʔon",
    {⟨.participant, true⟩, number (numberSystem.value .singular), ⟨.case, .nom⟩} ⟷ "etš",
    {⟨.author, true⟩, ⟨.case, .nom⟩} ⟷ "en",
    {⟨.participant, true⟩, number (numberSystem.value .plural)} ⟷ "éːš",
    {number (numberSystem.value .plural)} ⟷ "oʔob", ∅ ⟷ "Ø"]

/-- The Agr1 Vocabulary Items (43) realize the ergative auxiliary suffix. -/
def agr1 : List (VocabularyItem FeatureVal String) :=
  [{⟨.participant, true⟩, ⟨.author, true⟩} ⟷ "in", {⟨.author, true⟩} ⟷ "k",
    {⟨.participant, true⟩} ⟷ "a", ∅ ⟷ "u"]

/-- The Agr2 Vocabulary Items (44) realize the ergative verbal prefix. -/
def agr2 : List (VocabularyItem FeatureVal String) :=
  [{⟨.participant, true⟩} ⟷ "w", {⟨.participant, false⟩} ⟷ "j", ∅ ⟷ ""]

/-- In the overt verbal suffixes of a clause, Agr3 bears the subject's matrix and, in a transitive
clause, the object's, (25) and (28b); strict scansion of (27) realizes them, and the elsewhere *-Ø*
is not overt. -/
def suffixes (subj : Argument) (obj : Option Argument) : List String :=
  (scansion agr3 ∅
    (matrix subj.1 subj.2 .erg :: (obj.map fun o ↦ [matrix o.1 o.2 .nom]).getD []))
    |>.filter (· ≠ "Ø")

/-- The auxiliary suffix of an ergative subject, by the Subset Principle over (43). -/
def aux (subj : Argument) : Option String := subsetPrinciple agr1 (ergMatrix subj.1 subj.2)

/-- The verbal prefix of an ergative subject, by the Subset Principle over (44). -/
def verbPrefix (subj : Argument) : Option String :=
  subsetPrinciple agr2 (ergMatrix subj.1 subj.2)

/-- The rival template (18) has object agreement then subject agreement, each a node of its own
realized by the Subset Principle over (27). -/
def templateSuffixes (subj obj : Argument) : List String :=
  ((subsetPrinciple agr3 (matrix obj.1 obj.2 .nom)).toList ++
    (subsetPrinciple agr3 (matrix subj.1 subj.2 .erg)).toList).filter (· ≠ "Ø")

/-! ### The data pool: (3) to (8), (16), (19) to (24) -/

/-- A row of the pool records the arguments, the auxiliary suffix, the verbal prefix, the overt
verbal suffixes, and the judgment. -/
structure Row where
  subj : Argument
  obj : Option Argument
  aux : String
  verbPrefix : String
  suffixes : List String
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let person := [("1", Person.first), ("2", .second), ("3", .third)]
  let numbers := [("sg", numberSystem.value .singular), ("pl", numberSystem.value .plural)]
  let subj ← ex.parse? "subjPerson" person
  let subjPl ← ex.parse? "subjNumber" numbers
  let obj ← match ex.parse? "objPerson" person, ex.parse? "objNumber" numbers with
    | some p, some pl => some (some (p, pl))
    | none, none => some none
    | _, _ => none
  let aux ← ex.feature? "aux"
  let verbPrefix ← ex.feature? "prefix"
  let s₁ ← ex.feature? "suffix1"
  let s₂ ← ex.feature? "suffix2"
  pure ⟨(subj, subjPl), obj, aux, verbPrefix, [s₁, s₂].filter (· ≠ ""), ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Under Local Fission, a row of (19) to (24) is grammatical iff its suffixes are what strict
scansion of (27) inserts, as in (20), (22) and (24). -/
theorem suffixes_rows :
    ∀ r ∈ rows, r.judgment = .acceptable ↔ suffixes r.subj r.obj = r.suffixes := by
  decide

/-- The template (18) predicts the starred forms of (21) and (23) but fails the grammatical (22) and
(24). -/
theorem template_rows :
    (∀ r ∈ rows, ∀ o ∈ r.obj,
        r.judgment = .ungrammatical → templateSuffixes r.subj o = r.suffixes) ∧
      ∃ r ∈ rows, r.judgment = .acceptable ∧
        ∃ o ∈ r.obj, templateSuffixes r.subj o ≠ r.suffixes := by
  decide

/-- Agr1 (43) and Agr2 (44) recover the auxiliary suffix and verbal prefix of every row, (17) and
(39). -/
theorem aux_prefix_rows :
    ∀ r ∈ rows, aux r.subj = some r.aux ∧ verbPrefix r.subj = some r.verbPrefix := by
  decide

/-! ### Against long-distance Fission, section 5 -/

/-- In the paradigm (39), second and third person mark only person on the auxiliary and prefix and
plurality by a verbal suffix ((36) to (38)). -/
theorem ergative_paradigm (p : Person) (h : p = .second ∨ p = .third) :
    aux (p, numberSystem.value .singular) = aux (p, numberSystem.value .plural) ∧
      verbPrefix (p, numberSystem.value .singular) = verbPrefix (p, numberSystem.value .plural) ∧
      suffixes (p, numberSystem.value .singular) none = [] ∧
      suffixes (p, numberSystem.value .plural) none ≠ [] := by
  rcases h with rfl | rfl <;> decide

/-- In the paradigm (39), first-person number is marked on the auxiliary and by no verbal suffix, a
person distinction under (42) ((3), (4)). -/
theorem first_person_paradigm :
    aux (.first, numberSystem.value .singular) ≠ aux (.first, numberSystem.value .plural) ∧
      ∀ pl, suffixes (.first, pl) none = [] := by
  decide

/-! ### The appendix: a privative implementation -/

/-- [harley-ritter-2002]'s privative features, with the case feature the appendix adds. -/
inductive Privative where
  | participant
  | speaker
  | addressee
  | group
  | nom
  deriving DecidableEq, Repr

/-- The specifications (A1), with nominative case on a nominative argument. -/
def privMatrix (p : Person) (n : numberSystem.values) (c : Case) : Finset Privative :=
  let person : Finset Privative := match p with
    | .first => numberSystem.elim {.participant} {.participant, .speaker} (n := n)
    | .second =>
      numberSystem.elim {.participant, .addressee} {.participant, .addressee, .group} (n := n)
    | _ => numberSystem.elim ∅ {.group} (n := n)
  person ∪ if c = .nom then {.nom} else ∅

/-- The Agr1 Vocabulary Items (A2). -/
def agr1' : List (VocabularyItem Privative String) :=
  [{.speaker} ⟷ "k", {.addressee} ⟷ "a", {.participant} ⟷ "in", ∅ ⟷ "u"]

/-- The Agr2 Vocabulary Items (A3). -/
def agr2' : List (VocabularyItem Privative String) :=
  [{.speaker} ⟷ "", {.participant} ⟷ "w", ∅ ⟷ "j"]

/-- The Agr3 Vocabulary Items (A4). -/
def agr3' : List (VocabularyItem Privative String) :=
  [{.addressee, .group} ⟷ "éːš", {.addressee, .nom} ⟷ "etš", {.speaker, .nom} ⟷ "oʔon",
    {.participant, .nom} ⟷ "en", {.group} ⟷ "oʔob", ∅ ⟷ "Ø"]

/-- The overt verbal suffixes under (A4). -/
def suffixes' (subj : Argument) (obj : Option Argument) : List String :=
  (scansion agr3' ∅
    (privMatrix subj.1 subj.2 .erg :: (obj.map fun o ↦ [privMatrix o.1 o.2 .nom]).getD []))
    |>.filter (· ≠ "Ø")

theorem privative_aux_prefix :
    ∀ r ∈ rows, subsetPrinciple agr1' (privMatrix r.subj.1 r.subj.2 .erg) = aux r.subj ∧
      subsetPrinciple agr2' (privMatrix r.subj.1 r.subj.2 .erg) = verbPrefix r.subj := by
  decide

/-- The privative Agr3 list (A4) wrongly inserts *-en* in the grammatical (20), which the binary
[−Auth] of (27) blocks. -/
theorem privative_suffixes :
    suffixes' (.third, numberSystem.value .plural) (some (.second, numberSystem.value .plural)) =
      ["éːš", "en", "oʔob"] ∧
      ∃ r ∈ rows, r.judgment = .acceptable ∧ suffixes' r.subj r.obj ≠ r.suffixes := by
  decide

end GonzalezPootMcGinnis2006
