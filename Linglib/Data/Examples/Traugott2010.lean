module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Traugott2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Traugott2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Traugott2010.Examples`.
-/

@[expose] public section

namespace Traugott2010.Examples

def ex_5a : Datum :=
  { id := "traugott2010_5a"
    source := ⟨"traugott-2010", "(5a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I am going to visit the prisoner. Fare you well."
    glossedTokens := []
    context := "1604, Shakespeare, Measure for Measure III.iii."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "be going to"), ("use", "motion with intent"), ("century", "16")] }

def ex_5b : Datum :=
  { id := "traugott2010_5b"
    source := ⟨"traugott-2010", "(5b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I ha' forgot what I was going to say to you."
    glossedTokens := []
    context := "1663, Cowley, Cutter of Coleman Street V.ii."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "be going to"), ("use", "intention without motion"), ("century", "17")] }

def ex_5c : Datum :=
  { id := "traugott2010_5c"
    source := ⟨"traugott-2010", "(5c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I am afraid there is going to be such a calm among us, that we must be forced to invent some mock Quarrels."
    glossedTokens := []
    context := "1725, Odingsells, The Bath Unmask'd V.iii."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "be going to"), ("use", "raising"), ("century", "18")] }

def ex_6 : Datum :=
  { id := "traugott2010_6"
    source := ⟨"traugott-2010", "(6)"⟩
    reportedIn := none
    method := some .description
    language := "nucl1643"
    primaryText := "saburahu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Old Japanese: wait in a specific location (non-honorific)", .acceptable), ("Late Old Japanese: humble subject be in the vicinity of respected referent (referent honorific, subjectified)", .acceptable), ("Early Middle Japanese -saburau/-soorau: be-polite (addressee honorific, intersubjectified)", .acceptable)]
    paperFeatures := [("item", "saburahu"), ("honorific", "non-honorific"), ("honorific", "referent honorific"), ("honorific", "addressee honorific")] }

def ex_12a : Datum :=
  { id := "traugott2010_12a"
    source := ⟨"traugott-2010", "(12a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "In þe assaut some … breke a pece of þe wal"
    glossedTokens := []
    context := "c1325, Gloucester Chronicle A 11590."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a piece of"), ("stage", "I Partitive")] }

def ex_13a : Datum :=
  { id := "traugott2010_13a"
    source := ⟨"traugott-2010", "(13a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Dorus, whilom king of Grece ... hadde of infortune a piece"
    glossedTokens := []
    context := "a1393, Gower, Confessio Amantis V. 1338; note the preposed *of infortune*."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a piece of"), ("stage", "II Extended Partitive")] }

def ex_14a : Datum :=
  { id := "traugott2010_14a"
    source := ⟨"traugott-2010", "(14a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "If I had not beene a peece of a Logician before I came to him."
    glossedTokens := []
    context := "1586, Sidney, Apologie for Poetrie."
    judgment := .acceptable
    contrasts := []
    readings := [("partitive: a small part or exemplar of a logician", .acceptable), ("quantifier: a logician to a certain degree, somewhat of a logician", .acceptable)]
    paperFeatures := [("item", "a piece of"), ("stage", "III Quantifier")] }

def ex_16a : Datum :=
  { id := "traugott2010_16a"
    source := ⟨"traugott-2010", "(16a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "In to the pyne of helle .. for the bytt of an Appel"
    glossedTokens := []
    context := "c1400, Ancrene Riwle 22/25."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "0 Pre-Partitive")] }

def ex_17 : Datum :=
  { id := "traugott2010_17"
    source := ⟨"traugott-2010", "(17)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "He badd tatt gho shollde himm ec / An bite brædess brinngenn"
    glossedTokens := []
    context := "c1200, Ormulum 8640; still with the genitive."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "I Partitive")] }

def ex_18a : Datum :=
  { id := "traugott2010_18a"
    source := ⟨"traugott-2010", "(18a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The fragments, scraps, the bits, and greazie reliques of her ore-eaten faith"
    glossedTokens := []
    context := "1606, Shakespeare, Troilus and Cressida V.ii.159; a metaphorical context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "II Extended Partitive")] }

def ex_19a : Datum :=
  { id := "traugott2010_19a"
    source := ⟨"traugott-2010", "(19a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Your beauty is a little bit of a jilt"
    glossedTokens := []
    context := "1771, Foote, Maid of Bath."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "III Quantifier"), ("pragmatic", "intersubjective hedge")] }

def ex_20 : Datum :=
  { id := "traugott2010_20"
    source := ⟨"traugott-2010", "(20)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I would not be a bit wiser, a bit richer, a bit taller, a bit shorter, than I am at this Instant"
    glossedTokens := []
    context := "1723, Steele, The Conscious Lovers III.i."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "IV Adverb Degree Modifier")] }

def ex_21b : Datum :=
  { id := "traugott2010_21b"
    source := ⟨"traugott-2010", "(21b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A. Hear me. B. Not a bit"
    glossedTokens := []
    context := "1739, Baker, The Cit Turn'd Gentleman."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "V Adjunct"), ("polarity", "negative")] }

def ex_22 : Datum :=
  { id := "traugott2010_22"
    source := ⟨"traugott-2010", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Your friend is a bit of a beauty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a bit of"), ("stage", "III Quantifier"), ("head", "positively evaluated")] }

def ex_23 : Datum :=
  { id := "traugott2010_23"
    source := ⟨"traugott-2010", "(23)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "With strengthe of his blast / The white [dragon] brent than rede, / That of him nas founden a schrede / Bot dust"
    glossedTokens := []
    context := "c1300, Arthour and Merlin 1540; note the preposing."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a shred of"), ("stage", "I Partitive")] }

def ex_24b : Datum :=
  { id := "traugott2010_24b"
    source := ⟨"traugott-2010", "(24b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A despis'd Shred of mankind"
    glossedTokens := []
    context := "1645, G. Daniel, Poems."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a shred of"), ("stage", "II Extended Partitive")] }

def ex_25a : Datum :=
  { id := "traugott2010_25a"
    source := ⟨"traugott-2010", "(25a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Loto has not a shred of beauty. She is a big, angular, raw-boned Normande, with a rough voice, and a villainous patois"
    glossedTokens := []
    context := "1867, Ouida, Under Two Flags."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("item", "a shred of"), ("stage", "III Quantifier"), ("polarity", "negative")] }

def all : List Datum := [ex_5a, ex_5b, ex_5c, ex_6, ex_12a, ex_13a, ex_14a, ex_16a, ex_17, ex_18a, ex_19a, ex_20, ex_21b, ex_22, ex_23, ex_24b, ex_25a]

/-- The expressions whose histories the paper sketches. -/
inductive Item where
  /-- be going to: the motion verb that became a raising future -/
  | beGoingTo
  /-- saburahu: the Japanese verb that became an addressee honorific -/
  | saburahu
  /-- a piece of: the first case study of section 4 -/
  | aPieceOf
  /-- a bit of: the second case study of section 4 -/
  | aBitOf
  /-- a shred of: the third case study of section 4 -/
  | aShredOf
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `item`. -/
def item (e : Datum) : Option Item :=
  e.parse? "item" [("be going to", .beGoingTo), ("saburahu", .saburahu), ("a piece of", .aPieceOf),
    ("a bit of", .aBitOf), ("a shred of", .aShredOf)]

/-- The stages of the binominal case studies of section 4. -/
inductive Stage where
  /-- 0 Pre-Partitive: a nominalization, 'biting' -/
  | prePartitive
  /-- I Partitive: a unit of a concrete complement -/
  | partitive
  /-- II Extended Partitive: a unit of a non-food or abstract complement -/
  | extendedPartitive
  /-- III Quantifier: the first noun quantifies the second, which is the head -/
  | quantifier
  /-- IV Adverb Degree Modifier: an adverb before an adjective -/
  | degreeModifier
  /-- V Adjunct: an adverb without a complement, or a free adjunct -/
  | adjunct
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `stage`. -/
def stage (e : Datum) : Option Stage :=
  e.parse? "stage" [("0 Pre-Partitive", .prePartitive), ("I Partitive", .partitive),
    ("II Extended Partitive", .extendedPartitive), ("III Quantifier", .quantifier),
    ("IV Adverb Degree Modifier", .degreeModifier), ("V Adjunct", .adjunct)]

/-- The uses of *be going to* in (5). -/
inductive Use where
  /-- motion with intent: motion with intent to act -/
  | motion
  /-- intention without motion: intention without motion -/
  | intention
  /-- raising: the raising construction, the speaker's assessment of the future -/
  | raising
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `use`. -/
def use (e : Datum) : Option Use :=
  e.parse? "use" [("motion with intent", .motion), ("intention without motion", .intention),
    ("raising", .raising)]

/-- The honorific values of *saburahu* in (6), in the order they arose. -/
inductive Honorific where
  /-- non-honorific: no honorific value -/
  | nonHonorific
  /-- referent honorific: points humiliatively or respectfully to the subject referent -/
  | referent
  /-- addressee honorific: indexes politeness towards the addressee -/
  | addressee
  deriving DecidableEq, Repr, Fintype

/-- The values a row records under `honorific`. -/
def honorific (e : Datum) : List Honorific :=
  (e.features "honorific").filterMap (List.lookup · [("non-honorific", .nonHonorific), ("referent honorific", .referent),
    ("addressee honorific", .addressee)])

/-- The examples of the paper. -/
inductive Example where
  | ex_5a
  | ex_5b
  | ex_5c
  | ex_6
  | ex_12a
  | ex_13a
  | ex_14a
  | ex_16a
  | ex_17
  | ex_18a
  | ex_19a
  | ex_20
  | ex_21b
  | ex_22
  | ex_23
  | ex_24b
  | ex_25a
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_5a, .ex_5b, .ex_5c, .ex_6, .ex_12a, .ex_13a, .ex_14a, .ex_16a, .ex_17, .ex_18a, .ex_19a,
    .ex_20, .ex_21b, .ex_22, .ex_23, .ex_24b, .ex_25a]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_5a => _root_.Traugott2010.Examples.ex_5a
  | .ex_5b => _root_.Traugott2010.Examples.ex_5b
  | .ex_5c => _root_.Traugott2010.Examples.ex_5c
  | .ex_6 => _root_.Traugott2010.Examples.ex_6
  | .ex_12a => _root_.Traugott2010.Examples.ex_12a
  | .ex_13a => _root_.Traugott2010.Examples.ex_13a
  | .ex_14a => _root_.Traugott2010.Examples.ex_14a
  | .ex_16a => _root_.Traugott2010.Examples.ex_16a
  | .ex_17 => _root_.Traugott2010.Examples.ex_17
  | .ex_18a => _root_.Traugott2010.Examples.ex_18a
  | .ex_19a => _root_.Traugott2010.Examples.ex_19a
  | .ex_20 => _root_.Traugott2010.Examples.ex_20
  | .ex_21b => _root_.Traugott2010.Examples.ex_21b
  | .ex_22 => _root_.Traugott2010.Examples.ex_22
  | .ex_23 => _root_.Traugott2010.Examples.ex_23
  | .ex_24b => _root_.Traugott2010.Examples.ex_24b
  | .ex_25a => _root_.Traugott2010.Examples.ex_25a

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Traugott2010.Examples.all := rfl

/-- The value the example records under `item`. -/
def Example.item : Example → Option Item
  | .ex_5a => some .beGoingTo
  | .ex_5b => some .beGoingTo
  | .ex_5c => some .beGoingTo
  | .ex_6 => some .saburahu
  | .ex_12a => some .aPieceOf
  | .ex_13a => some .aPieceOf
  | .ex_14a => some .aPieceOf
  | .ex_16a => some .aBitOf
  | .ex_17 => some .aBitOf
  | .ex_18a => some .aBitOf
  | .ex_19a => some .aBitOf
  | .ex_20 => some .aBitOf
  | .ex_21b => some .aBitOf
  | .ex_22 => some .aBitOf
  | .ex_23 => some .aShredOf
  | .ex_24b => some .aShredOf
  | .ex_25a => some .aShredOf

theorem Example.item_datum :
    ∀ x : Example, _root_.Traugott2010.Examples.item x.datum = x.item := by
  decide +kernel

/-- The value the example records under `stage`. -/
def Example.stage : Example → Option Stage
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_6 => none
  | .ex_12a => some .partitive
  | .ex_13a => some .extendedPartitive
  | .ex_14a => some .quantifier
  | .ex_16a => some .prePartitive
  | .ex_17 => some .partitive
  | .ex_18a => some .extendedPartitive
  | .ex_19a => some .quantifier
  | .ex_20 => some .degreeModifier
  | .ex_21b => some .adjunct
  | .ex_22 => some .quantifier
  | .ex_23 => some .partitive
  | .ex_24b => some .extendedPartitive
  | .ex_25a => some .quantifier

theorem Example.stage_datum :
    ∀ x : Example, _root_.Traugott2010.Examples.stage x.datum = x.stage := by
  decide +kernel

/-- The value the example records under `use`. -/
def Example.use : Example → Option Use
  | .ex_5a => some .motion
  | .ex_5b => some .intention
  | .ex_5c => some .raising
  | .ex_6 => none
  | .ex_12a => none
  | .ex_13a => none
  | .ex_14a => none
  | .ex_16a => none
  | .ex_17 => none
  | .ex_18a => none
  | .ex_19a => none
  | .ex_20 => none
  | .ex_21b => none
  | .ex_22 => none
  | .ex_23 => none
  | .ex_24b => none
  | .ex_25a => none

theorem Example.use_datum :
    ∀ x : Example, _root_.Traugott2010.Examples.use x.datum = x.use := by
  decide +kernel

/-- The values the example records under `honorific`. -/
def Example.honorific : Example → List Honorific
  | .ex_5a => []
  | .ex_5b => []
  | .ex_5c => []
  | .ex_6 => [.nonHonorific, .referent, .addressee]
  | .ex_12a => []
  | .ex_13a => []
  | .ex_14a => []
  | .ex_16a => []
  | .ex_17 => []
  | .ex_18a => []
  | .ex_19a => []
  | .ex_20 => []
  | .ex_21b => []
  | .ex_22 => []
  | .ex_23 => []
  | .ex_24b => []
  | .ex_25a => []

theorem Example.honorific_datum :
    ∀ x : Example, _root_.Traugott2010.Examples.honorific x.datum = x.honorific := by
  decide +kernel

end Traugott2010.Examples
