module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Fragments.Swahili.Relativization
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Data.Examples.Scott2021

/-!
# Scott (2021): Two Types of Resumptive Pronouns in Swahili

This file formalizes the paper's account of the resumptive pronouns that the objects of Swahili's
monosyllabic prepositions require (§3.3): bound pronouns, the only option inside adjunct islands
((31)–(33)), match the head in person, while movement copies, diagnosed by parasitic gaps
((35)–(37)), never carry person. Both follow from the Vocabulary of (28) (`resumptiveVocab`) and the
copy theory of movement. A pronoun is a `PhraseStructure.Tree` over D, Num, the animate n and, for
local persons only, a Person projection ((40)–(44), `pronoun`), and the Vocabulary spells out the
Fragment's paradigm of Table 2 (`table2`). A movement copy in a position with a phonological
requirement is reduced rather than deleted, following Landau: MaxElide removes the largest
constituent whose residue can still be spelled out (`Deletable`, `maxElideTarget`), which is PersP,
since *-ye* spells out `[sg + n_anim]` while nothing spells out Num alone ((46)–(48),
`maxElide_persP`). So a movement copy of a local-person pronoun surfaces as the personless pronoun
(`movement_copy_personless`), a bound pronoun is spelled out in full, and a copy in a subject or
object position, which carries no requirement, is deleted ((17)–(18), `gap_without_minimality`); and
since Num is above Pers, a deletion that keeps person keeps number (`person_entails_number`), the
crosslinguistic pattern of the paper's conclusion. The paper's judgments (`Data/Examples/Scott2021`)
instantiate the account: clefts allow either pronoun but fix number ((24)–(25), (29)), islands allow
only the bound pronoun, and for every speaker of Table 4 a personless parasitic pronoun needs a
personless true gap (`cleft_rows`, `island_rows`, `parasitic_rows`).

## Implementation notes

* The structures are `PhraseStructure.Tree`s over the four DP-internal categories, so MaxElide is
  structural deletion rather than feature removal; features are read off the terminals for
  Vocabulary Insertion.
* The interspeaker variation of Table 4 beyond its first two rows is not derived, as the paper
  does not derive it.

## References

* [scott-2021]
* [landau-2006]
-/

@[expose] public section

namespace Scott2021

open Swahili PhraseStructure DistributedMorphology
open Minimalist (FeatureVal)

/-! ### The structure of pronouns (§5.1) -/

/-- The DP-internal projections of (40)–(41) are D, Num, the animate n, and the Person
projection that only local-person pronouns have. -/
inductive DPCat where
  | D | Num | n | Pers
  deriving DecidableEq, Repr, Fintype

/-- A pronoun is `[DP D [NumP Num [nP n_anim [PersP Pers]]]]` ((41)), without PersP for the
personless pronouns of (42). -/
def pronoun (person : Option Person) (number : Number) : Tree DPCat String :=
  .node .D [
    .terminal .D "",
    .node .Num [
      .terminal .Num (if number = .plural then "pl" else "sg"),
      .node .n ((.terminal .n "anim") ::
        match person with
        | some .first => [.node .Pers [.terminal .Pers "1"]]
        | some .second => [.node .Pers [.terminal .Pers "2"]]
        | _ => [])]]

/-- A terminal contributes its person, its number, or the animate gender. -/
def terminalFeature : DPCat → String → Option FeatureVal
  | .Pers, "1" => some ⟨.person, .first⟩
  | .Pers, "2" => some ⟨.person, .second⟩
  | .Num, "sg" => some ⟨.number, .singular⟩
  | .Num, "pl" => some ⟨.number, .plural⟩
  | .n, "anim" => some ⟨.gender, .animate⟩
  | _, _ => none

/-- The features at a tree's terminals, left to right. -/
def featureList (t : Tree DPCat String) : List FeatureVal :=
  t.terminals.filterMap fun (c, w) ↦ terminalFeature c w

/-! ### Vocabulary Insertion (§3.4) -/

/-- The Vocabulary Items of (28), the person-specified animate entries and the personless
animate defaults *-ye* and *-o*. -/
def resumptiveVocab : List (VocabularyItem FeatureVal String) :=
  let entry (fs : Finset FeatureVal) (e : String) : VocabularyItem FeatureVal String := fs ⟷ e
  [ entry {⟨.person, .first⟩, ⟨.gender, .animate⟩, ⟨.number, .singular⟩} "mi",
    entry {⟨.person, .first⟩, ⟨.gender, .animate⟩, ⟨.number, .plural⟩} "si",
    entry {⟨.person, .second⟩, ⟨.gender, .animate⟩, ⟨.number, .singular⟩} "we",
    entry {⟨.person, .second⟩, ⟨.gender, .animate⟩, ⟨.number, .plural⟩} "nyi",
    entry {⟨.gender, .animate⟩, ⟨.number, .singular⟩} "ye",
    entry {⟨.gender, .animate⟩, ⟨.number, .plural⟩} "o" ]

/-- The exponent of a pronoun structure, by the Subset Principle over (28). -/
def spellout (t : Tree DPCat String) : Option String :=
  subsetPrinciple resumptiveVocab (featureList t).toFinset

/-- The person of a cell as the structures' person, third person being the absence of
PersP. -/
def cellPerson (c : Agreement.Bundle) : Option Person :=
  if c.IsSAP then some c.person else none

/-- The number of a cell. -/
def cellNumber (c : Agreement.Bundle) : Number := if c.IsPlural then .plural else .singular

/-- Every cell of the resumptive paradigm of Table 2 is the Subset Principle's choice for the
corresponding structure, by the Vocabulary of (28) ((43), (45)). -/
theorem table2 :
    ∀ c ∈ Agreement.Bundle.personNumberCells,
      (spellout (pronoun (cellPerson c) (cellNumber c))).map Morphology.Morph.suff =
        resumptive.realize c := by
  intro c hc
  simp only [Agreement.Bundle.personNumberCells, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### MaxElide (§5.2–5.3) -/

mutual
/-- Delete the constituent of category `c`, the subtree it heads, from a
tree. -/
def deleteLayer (c : DPCat) : Tree DPCat String → Tree DPCat String
  | .node k children => .node k (deleteLayerAll c children)
  | other => other

def deleteLayerAll (c : DPCat) : List (Tree DPCat String) → List (Tree DPCat String)
  | [] => []
  | t :: ts => if t.cat = c then deleteLayerAll c ts else deleteLayer c t :: deleteLayerAll c ts
end

/-- A layer of a pronoun is deletable when what remains can still be spelled out, MaxElide's
condition ((48)). Deleting PersP leaves `[sg + n_anim]`, which *-ye* spells out, while
deleting nP leaves Num alone, which nothing spells out. -/
def Deletable (t : Tree DPCat String) (c : DPCat) : Prop :=
  c ≠ .D ∧ (spellout (deleteLayer c t)).isSome = true

instance (t : Tree DPCat String) (c : DPCat) : Decidable (Deletable t c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The layers of a pronoun, outermost first. -/
def layers : List DPCat := [.D, .Num, .n, .Pers]

/-- MaxElide chooses the largest deletable constituent. -/
def maxElideTarget (t : Tree DPCat String) : Option DPCat :=
  layers.find? fun c ↦ decide (Deletable t c)

/-- In a local-person pronoun PersP is the unique deletable layer, so MaxElide
deletes it ((46)–(47)). -/
theorem maxElide_persP :
    ∀ (p : Person) (n : Number), p = .first ∨ p = .second →
      maxElideTarget (pronoun (some p) n) = some .Pers := by
  decide

/-- Deleting a layer can keep person only if it keeps number, since Num is above Pers
(§6). -/
theorem person_entails_number :
    ∀ (c : DPCat) (n : Number),
      (featureList (deleteLayer c (pronoun (some .first) n))).any
          (fun f ↦ decide (f.1 = .person)) = true →
        (featureList (deleteLayer c (pronoun (some .first) n))).any
          (fun f ↦ decide (f.1 = .number)) = true := by
  decide

/-! ### Chain reduction (§5.2–5.3) -/

/-- A resumptive is a base-generated bound pronoun or a lower copy of Ā-movement. -/
inductive Origin where
  | bound | movementCopy
  deriving DecidableEq, Repr

/-- The pronounced form. A bound pronoun is spelled out in full. A movement
copy is deleted by Economy of Pronunciation unless its position carries the
bimoraic Minimality requirement of a monosyllabic preposition (§3.3), where
Phonological Recoverability forces partial deletion, MaxElide removing PersP and the residue
being spelled out. -/
def pronounce (t : Tree DPCat String) : Origin → (minimality : Bool) → Option String
  | .bound, _ => spellout t
  | .movementCopy, true => spellout (deleteLayer .Pers t)
  | .movementCopy, false => none

/-- Subjects and objects, with no Minimality requirement, leave a gap
((17)–(18)). -/
theorem gap_without_minimality (t : Tree DPCat String) :
    pronounce t .movementCopy false = none := rfl

/-- A movement copy under Minimality loses its person and surfaces as the
personless pronoun ((36)). -/
theorem movement_copy_personless :
    ∀ (p : Person) (n : Number), p = .first ∨ p = .second →
      pronounce (pronoun (some p) n) .movementCopy true =
        pronounce (pronoun none n) .bound true := by
  decide

/-! ### The data pool (§3.4, §4) -/

/-- The constructions of the pool are simple clefts, clefts out of adjunct islands, and
parasitic gaps. -/
inductive Construction where
  | cleft | island | parasiticGap
  deriving DecidableEq, Repr

/-- A cell of the pool records the antecedent's person and number, the construction, the
resumptive form or forms, and the judgment. -/
structure Row where
  construction : Construction
  person : Person
  number : Number
  form : String
  parasitic : Option String
  accepted : Bool
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let fs := ex.paperFeatures
  let construction ← match fs.lookup "construction" with
    | some "cleft" => some Construction.cleft
    | some "island" => some Construction.island
    | some "parasiticGap" => some Construction.parasiticGap
    | _ => none
  let person ← match fs.lookup "antecedentPerson" with
    | some "1" => some Person.first | some "2" => some Person.second | _ => none
  let number ← match fs.lookup "antecedentNumber" with
    | some "sg" => some Number.singular | some "pl" => some Number.plural | _ => none
  let form ← fs.lookup "form" <|> fs.lookup "trueGap"
  pure ⟨construction, person, number, form, fs.lookup "parasitic", ex.judgment = .acceptable⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The antecedent's structure. -/
def Row.tree (r : Row) : Tree DPCat String := pronoun (some r.person) r.number

/-- In a cleft either the bound pronoun or the movement copy is available, so the form is
accepted iff it is one of the two, which fixes number while leaving person optional
((24)–(25), (29)). -/
theorem cleft_rows :
    ∀ r ∈ rows, r.construction = .cleft →
      (r.accepted = (pronounce r.tree .bound true = some r.form ∨
        pronounce r.tree .movementCopy true = some r.form)) := by
  decide

/-- Out of an adjunct island movement is blocked, so the form is accepted iff it is the bound
pronoun's ((31)–(33)). -/
theorem island_rows :
    ∀ r ∈ rows, r.construction = .island →
      (r.accepted = (pronounce r.tree .bound true = some r.form)) := by
  decide

/-- A movement copy in the parasitic position is licensed only by a movement copy in the
true-gap position, so for every speaker *ye … ye* is in and *mi … ye* is out ((36)–(37),
Table 4). -/
theorem parasitic_rows :
    ∀ r ∈ rows, r.construction = .parasiticGap →
      r.parasitic = pronounce r.tree .movementCopy true →
        (r.accepted = (some r.form = pronounce r.tree .movementCopy true)) := by
  decide

end Scott2021
