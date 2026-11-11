module

public import Linglib.Morphology.DistributedMorphology.Fission
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Person.Features
public import Linglib.Syntax.Agreement.Geometry
public import Linglib.Data.Examples.GonzalezPootMcGinnis2006
public import Linglib.Data.Examples.Readers

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
privative implementation over Harley and Ritter's geometry, (A1) to (A4), recovers the auxiliary
and the prefix (`privative_aux_prefix`) and, with one item of (A4) moved, the suffixes
(`privative_suffixes`).

## Implementation notes

The person features of (26), [±PSE, ±Auth], are the substrate's [±participant, ±author]
decomposition, and [±Pl] a binary feature value. Agr3's list (27) needs the nominative
first-person plural to carry [+PSE] and the singular not to, the reverse of the assignment (42)
gives the ergative auxiliary; the paper does not reconcile the two, so `matrix` follows (27) for
nominative first person and (42) otherwise. The elsewhere *-Ø* is inserted but not counted among
a row's overt suffixes.

The appendix calls [Speaker] and [Addressee] dependents of [Participant] and "therefore more
specific", so an item or argument mentioning a node here bears the nodes it depends on (`nodes`),
and that specificity, not the listing of (A2) and (A3), decides between their items. The paper
works no derivation through (A4). We read discharge the same way: an item that discharges
[Addressee] discharges [Participant] with it. Were [Participant] left behind, the residue of a
second-person plural object would match *-en*, which (20) lacks.

## References

* [gonzalez-poot-mcginnis-2006]
* [halle-1997]
* [noyer-1992]
* [halle-marantz-1993]
* [harley-ritter-2002]
-/

@[expose] public section

namespace GonzalezPootMcGinnis2006

open DistributedMorphology Phi.Geometry
open Minimalist (FeatureVal)
open scoped DistributedMorphology.VocabularyItem

/-! ### Features and matrices, sections 3 to 5 -/

/-- Yucatec Maya distinguishes the singular and the plural. -/
def numberSystem : Finset Number := {.singular, .plural}

/-- An argument is a person with a number. -/
abbrev Argument := Person × numberSystem

/-- The person features of (26), [±PSE, ±Auth], as the substrate's [±participant, ±author]
decomposition of a person. -/
def personFeatures (p : Person) : Finset FeatureVal :=
  {⟨.participant, decide (.participant ∈ p.toFeatures)⟩,
    ⟨.author, decide (.author ∈ p.toFeatures)⟩}

/-- Number as the feature [±Pl]. -/
def number (n : numberSystem) : FeatureVal := ⟨.number, n.1⟩

/-- In an ergative argument's matrix (42), first-person number is a person distinction, singular
[+PSE, +Auth] and plural [+Auth]. -/
def ergMatrix (p : Person) (n : numberSystem) : Finset FeatureVal :=
  match p with
  | .first =>
    Number.elim numberSystem {⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .erg⟩}
      {⟨.author, true⟩, ⟨.case, .erg⟩} (n := n)
  | p => personFeatures p ∪ {number n, ⟨.case, .erg⟩}

/-- An argument's matrix for Agr3 is (42) for ergative arguments and for second and third person,
and for nominative first person the one the assignment (27) presupposes, *-oʔon* 1pl [+PSE, +Auth,
NOM] and *-en* 1sg [+Auth, NOM]. -/
def matrix (p : Person) (n : numberSystem) (c : Case) : Finset FeatureVal :=
  match p, c with
  | .first, .nom =>
    Number.elim numberSystem {⟨.author, true⟩, ⟨.case, .nom⟩}
      {⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .nom⟩} (n := n)
  | p, .erg => ergMatrix p n
  | p, c => personFeatures p ∪ {number n, ⟨.case, c⟩}

/-! ### The Vocabularies (27), (43), (44) -/

/-- The Agr3 Vocabulary Items (27), in scansion order. -/
def agr3 : List (VocabularyItem FeatureVal String) :=
  [{⟨.participant, true⟩, ⟨.author, true⟩, ⟨.case, .nom⟩} ⟷ "oʔon",
    {⟨.participant, true⟩, number ⟨.singular, by decide⟩, ⟨.case, .nom⟩} ⟷ "etš",
    {⟨.author, true⟩, ⟨.case, .nom⟩} ⟷ "en",
    {⟨.participant, true⟩, number ⟨.plural, by decide⟩} ⟷ "éːš",
    {number ⟨.plural, by decide⟩} ⟷ "oʔob", ∅ ⟷ "Ø"]

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
  let numbers := [("sg", ⟨.singular, by decide⟩), ("pl", ⟨.plural, by decide⟩)]
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
    aux (p, ⟨.singular, by decide⟩) = aux (p, ⟨.plural, by decide⟩) ∧
      verbPrefix (p, ⟨.singular, by decide⟩) = verbPrefix (p, ⟨.plural, by decide⟩) ∧
      suffixes (p, ⟨.singular, by decide⟩) none = [] ∧
      suffixes (p, ⟨.plural, by decide⟩) none ≠ [] := by
  rcases h with rfl | rfl <;> decide

/-- In the paradigm (39), first-person number is marked on the auxiliary and by no verbal suffix, a
person distinction under (42) ((3), (4)). -/
theorem first_person_paradigm :
    aux (.first, ⟨.singular, by decide⟩) ≠ aux (.first, ⟨.plural, by decide⟩) ∧
      ∀ pl, suffixes (.first, pl) none = [] := by
  decide

/-! ### The appendix: a privative implementation -/

/-- The nodes of [harley-ritter-2002]'s geometry, with the case feature the appendix adds. -/
inductive Privative where
  | node (n : Node)
  | nom
  deriving DecidableEq, Repr

/-- The features of the nodes `ns`: a dependent brings what it depends on. -/
def nodes (ns : List Node) : Finset Privative := ((ns.flatMap Node.below).map .node).toFinset

/-- The specifications (A1), with nominative case on a nominative argument. -/
def privMatrix (p : Person) (n : numberSystem) (c : Case) : Finset Privative :=
  let person : List Node := match p with
    | .first => Number.elim numberSystem [.participant] [.speaker] (n := n)
    | .second => Number.elim numberSystem [.addressee] [.addressee, .group] (n := n)
    | _ => Number.elim numberSystem [] [.group] (n := n)
  nodes person ∪ if c = .nom then {.nom} else ∅

/-- The Agr1 Vocabulary Items (A2). -/
def agr1' : List (VocabularyItem Privative String) :=
  [nodes [.speaker] ⟷ "k", nodes [.addressee] ⟷ "a", nodes [.participant] ⟷ "in", ∅ ⟷ "u"]

/-- The Agr2 Vocabulary Items (A3). -/
def agr2' : List (VocabularyItem Privative String) :=
  [nodes [.speaker] ⟷ "", nodes [.participant] ⟷ "w", ∅ ⟷ "j"]

/-- The Agr3 Vocabulary Items (A4). -/
def agr3' : List (VocabularyItem Privative String) :=
  [nodes [.addressee, .group] ⟷ "éːš", insert .nom (nodes [.addressee]) ⟷ "etš",
    insert .nom (nodes [.speaker]) ⟷ "oʔon", insert .nom (nodes [.participant]) ⟷ "en",
    nodes [.group] ⟷ "oʔob", ∅ ⟷ "Ø"]

/-- (A4) with *-oʔon* moved to the top, as in (27). -/
def agr3'' : List (VocabularyItem Privative String) :=
  [insert .nom (nodes [.speaker]) ⟷ "oʔon", nodes [.addressee, .group] ⟷ "éːš",
    insert .nom (nodes [.addressee]) ⟷ "etš", insert .nom (nodes [.participant]) ⟷ "en",
    nodes [.group] ⟷ "oʔob", ∅ ⟷ "Ø"]

/-- The overt verbal suffixes under a privative Agr3 list. -/
def suffixes' (items : List (VocabularyItem Privative String)) (subj : Argument)
    (obj : Option Argument) : List String :=
  (scansion items ∅
    (privMatrix subj.1 subj.2 .erg :: (obj.map fun o ↦ [privMatrix o.1 o.2 .nom]).getD []))
    |>.filter (· ≠ "Ø")

theorem privative_aux_prefix :
    ∀ r ∈ rows, subsetPrinciple agr1' (privMatrix r.subj.1 r.subj.2 .erg) = aux r.subj ∧
      subsetPrinciple agr2' (privMatrix r.subj.1 r.subj.2 .erg) = verbPrefix r.subj := by
  decide

/-- The printed (A4) misorders the suffixes of (19), and with *-oʔon* moved to the top it recovers
every row as (27) does. -/
theorem privative_suffixes :
    suffixes' agr3' (.second, ⟨.plural, by decide⟩)
        (some (.first, ⟨.plural, by decide⟩)) = ["éːš", "oʔon"] ∧
      ∀ r ∈ rows, r.judgment = .acceptable ↔ suffixes' agr3'' r.subj r.obj = r.suffixes := by
  decide

end GonzalezPootMcGinnis2006
